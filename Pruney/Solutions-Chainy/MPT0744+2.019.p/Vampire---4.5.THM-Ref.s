%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 939 expanded)
%              Number of leaves         :   21 ( 285 expanded)
%              Depth                    :   23
%              Number of atoms          :  565 (3733 expanded)
%              Number of equality atoms :  276 (1205 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f121,f242,f113])).

fof(f113,plain,(
    ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] :
      ( ~ sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8)
      | r2_hidden(X10,X8) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( r2_hidden(X10,X8)
      | X0 != X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
              & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
            | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
          & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
            | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
            | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] :
      ( ? [X9] :
          ( ( ( X0 != X9
              & X1 != X9
              & X2 != X9
              & X3 != X9
              & X4 != X9
              & X5 != X9
              & X6 != X9
              & X7 != X9 )
            | ~ r2_hidden(X9,X8) )
          & ( X0 = X9
            | X1 = X9
            | X2 = X9
            | X3 = X9
            | X4 = X9
            | X5 = X9
            | X6 = X9
            | X7 = X9
            | r2_hidden(X9,X8) ) )
     => ( ( ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6
            & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7 )
          | ~ r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) )
        & ( sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6
          | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7
          | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)
        | ? [X9] :
            ( ( ( X0 != X9
                & X1 != X9
                & X2 != X9
                & X3 != X9
                & X4 != X9
                & X5 != X9
                & X6 != X9
                & X7 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X0 = X9
              | X1 = X9
              | X2 = X9
              | X3 = X9
              | X4 = X9
              | X5 = X9
              | X6 = X9
              | X7 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X10] :
            ( ( r2_hidden(X10,X8)
              | ( X0 != X10
                & X1 != X10
                & X2 != X10
                & X3 != X10
                & X4 != X10
                & X5 != X10
                & X6 != X10
                & X7 != X10 ) )
            & ( X0 = X10
              | X1 = X10
              | X2 = X10
              | X3 = X10
              | X4 = X10
              | X5 = X10
              | X6 = X10
              | X7 = X10
              | ~ r2_hidden(X10,X8) ) )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | ? [X9] :
            ( ( ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 )
              | ~ r2_hidden(X9,X8) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | r2_hidden(X9,X8) ) ) )
      & ( ! [X9] :
            ( ( r2_hidden(X9,X8)
              | ( X7 != X9
                & X6 != X9
                & X5 != X9
                & X4 != X9
                & X3 != X9
                & X2 != X9
                & X1 != X9
                & X0 != X9 ) )
            & ( X7 = X9
              | X6 = X9
              | X5 = X9
              | X4 = X9
              | X3 = X9
              | X2 = X9
              | X1 = X9
              | X0 = X9
              | ~ r2_hidden(X9,X8) ) )
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f242,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f241,f201])).

fof(f201,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f200,f182])).

fof(f182,plain,
    ( ~ r1_tarski(sK1,sK2)
    | sK1 = sK2 ),
    inference(resolution,[],[f178,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f178,plain,(
    r1_tarski(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f46,f166,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f166,plain,(
    r1_ordinal1(sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f47,f46,f164,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f164,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f163,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f163,plain,
    ( r2_hidden(sK2,sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f160,f46])).

fof(f160,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f135,f138])).

fof(f138,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f100,f111])).

fof(f111,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f63,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f96])).

fof(f96,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f54,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f68,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f69,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f70,f71])).

fof(f71,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f100,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(definition_unfolding,[],[f49,f99])).

fof(f99,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f51,f97,f98])).

fof(f98,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f96])).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f51,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f49,plain,
    ( ~ r1_ordinal1(sK1,sK2)
    | ~ r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_ordinal1(sK1,sK2)
      | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
    & ( r1_ordinal1(sK1,sK2)
      | r2_hidden(sK1,k1_ordinal1(sK2)) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK1,X1)
            | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK1,X1)
            | r2_hidden(sK1,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK1,X1)
          | ~ r2_hidden(sK1,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK1,X1)
          | r2_hidden(sK1,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK1,sK2)
        | ~ r2_hidden(sK1,k1_ordinal1(sK2)) )
      & ( r1_ordinal1(sK1,sK2)
        | r2_hidden(sK1,k1_ordinal1(sK2)) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f135,plain,(
    ! [X2] :
      ( r1_ordinal1(X2,sK2)
      | r2_hidden(sK2,X2)
      | ~ v3_ordinal1(X2) ) ),
    inference(resolution,[],[f47,f52])).

fof(f46,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f47,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f200,plain,
    ( sK1 = sK2
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f199,f46])).

fof(f199,plain,
    ( sK1 = sK2
    | r1_tarski(sK1,sK2)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f197,f133])).

fof(f133,plain,(
    ! [X0] :
      ( ~ r1_ordinal1(X0,sK2)
      | r1_tarski(X0,sK2)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f47,f56])).

fof(f197,plain,
    ( r1_ordinal1(sK1,sK2)
    | sK1 = sK2 ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,
    ( sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | sK1 = sK2
    | r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f186,f121])).

fof(f186,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( ~ sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
      | sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK1 = X5
      | sK1 = X6
      | sK1 = X7
      | r1_ordinal1(sK1,sK2) ) ),
    inference(subsumption_resolution,[],[f184,f164])).

fof(f184,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(sK1,sK2)
      | r1_ordinal1(sK1,sK2)
      | sK1 = X0
      | sK1 = X1
      | sK1 = X2
      | sK1 = X3
      | sK1 = X4
      | sK1 = X5
      | sK1 = X6
      | sK1 = X7
      | ~ sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ) ),
    inference(resolution,[],[f143,f72])).

fof(f72,plain,(
    ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] :
      ( ~ r2_hidden(X10,X8)
      | X1 = X10
      | X2 = X10
      | X3 = X10
      | X4 = X10
      | X5 = X10
      | X6 = X10
      | X7 = X10
      | X0 = X10
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f143,plain,
    ( r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | r2_hidden(sK1,sK2)
    | r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f101,f112])).

fof(f112,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f62,f97])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f101,plain,
    ( r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))))
    | r1_ordinal1(sK1,sK2) ),
    inference(definition_unfolding,[],[f48,f99])).

fof(f48,plain,
    ( r1_ordinal1(sK1,sK2)
    | r2_hidden(sK1,k1_ordinal1(sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f241,plain,(
    ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(subsumption_resolution,[],[f210,f125])).

fof(f125,plain,(
    r1_ordinal1(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f108,f46,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f210,plain,
    ( ~ r1_ordinal1(sK1,sK1)
    | ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    inference(backward_demodulation,[],[f139,f201])).

fof(f139,plain,
    ( ~ r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ r1_ordinal1(sK1,sK2) ),
    inference(resolution,[],[f100,f110])).

fof(f110,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f97])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f121,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] :
      ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
      | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
        | ~ sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) )
      & ( sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)
        | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8 ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) ) ),
    inference(definition_folding,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ( X7 = X9
            | X6 = X9
            | X5 = X9
            | X4 = X9
            | X3 = X9
            | X2 = X9
            | X1 = X9
            | X0 = X9 ) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] :
      ( k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8
    <=> ! [X9] :
          ( r2_hidden(X9,X8)
        <=> ~ ( X7 != X9
              & X6 != X9
              & X5 != X9
              & X4 != X9
              & X3 != X9
              & X2 != X9
              & X1 != X9
              & X0 != X9 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:22:31 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.49  % (28490)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.50  % (28486)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (28485)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.51  % (28487)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.51  % (28491)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.28/0.51  % (28482)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.28/0.51  % (28489)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.28/0.52  % (28504)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.28/0.52  % (28484)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.52  % (28496)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.52  % (28505)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.28/0.52  % (28483)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.28/0.52  % (28483)Refutation not found, incomplete strategy% (28483)------------------------------
% 1.28/0.52  % (28483)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (28483)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (28483)Memory used [KB]: 1663
% 1.28/0.52  % (28483)Time elapsed: 0.117 s
% 1.28/0.52  % (28483)------------------------------
% 1.28/0.52  % (28483)------------------------------
% 1.28/0.52  % (28496)Refutation not found, incomplete strategy% (28496)------------------------------
% 1.28/0.52  % (28496)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.52  % (28496)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.52  
% 1.28/0.52  % (28496)Memory used [KB]: 1791
% 1.28/0.52  % (28496)Time elapsed: 0.081 s
% 1.28/0.52  % (28496)------------------------------
% 1.28/0.52  % (28496)------------------------------
% 1.28/0.53  % (28510)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.53  % (28501)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.53  % (28511)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.53  % (28508)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.53  % (28503)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.53  % (28511)Refutation not found, incomplete strategy% (28511)------------------------------
% 1.40/0.53  % (28511)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.53  % (28511)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.53  
% 1.40/0.53  % (28511)Memory used [KB]: 1663
% 1.40/0.53  % (28511)Time elapsed: 0.129 s
% 1.40/0.53  % (28511)------------------------------
% 1.40/0.53  % (28511)------------------------------
% 1.40/0.53  % (28497)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.53  % (28488)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.53  % (28502)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.53  % (28500)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.40/0.54  % (28493)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.40/0.54  % (28509)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.54  % (28495)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.54  % (28499)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.54  % (28492)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.54  % (28494)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.54  % (28493)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % (28506)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.54  % (28498)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.54  % (28498)Refutation not found, incomplete strategy% (28498)------------------------------
% 1.40/0.54  % (28498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.54  % (28498)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.54  
% 1.40/0.54  % (28498)Memory used [KB]: 10746
% 1.40/0.54  % (28498)Time elapsed: 0.135 s
% 1.40/0.54  % (28498)------------------------------
% 1.40/0.54  % (28498)------------------------------
% 1.40/0.54  % (28492)Refutation not found, incomplete strategy% (28492)------------------------------
% 1.40/0.54  % (28492)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (28499)Refutation not found, incomplete strategy% (28499)------------------------------
% 1.40/0.55  % (28499)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (28499)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (28499)Memory used [KB]: 1791
% 1.40/0.55  % (28499)Time elapsed: 0.150 s
% 1.40/0.55  % (28499)------------------------------
% 1.40/0.55  % (28499)------------------------------
% 1.40/0.55  % (28507)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.55  % (28508)Refutation not found, incomplete strategy% (28508)------------------------------
% 1.40/0.55  % (28508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (28508)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (28508)Memory used [KB]: 6268
% 1.40/0.55  % (28508)Time elapsed: 0.131 s
% 1.40/0.55  % (28508)------------------------------
% 1.40/0.55  % (28508)------------------------------
% 1.40/0.55  % SZS output start Proof for theBenchmark
% 1.40/0.55  fof(f282,plain,(
% 1.40/0.55    $false),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f121,f242,f113])).
% 1.40/0.55  fof(f113,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X10,X8,X7,X5,X3,X1] : (~sP0(X10,X1,X2,X3,X4,X5,X6,X7,X8) | r2_hidden(X10,X8)) )),
% 1.40/0.55    inference(equality_resolution,[],[f80])).
% 1.40/0.55  fof(f80,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (r2_hidden(X10,X8) | X0 != X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X8,X7,X6,X5,X4,X3,X2,X1,X0] : (? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8))) => (((sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X0 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X1 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X2 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X3 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X4 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X5 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X6 & sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) != X7) | ~r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8)) & (sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X0 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X1 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X2 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X3 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X4 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X5 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X6 | sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8) = X7 | r2_hidden(sK4(X0,X1,X2,X3,X4,X5,X6,X7,X8),X8))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f42,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8) | ? [X9] : (((X0 != X9 & X1 != X9 & X2 != X9 & X3 != X9 & X4 != X9 & X5 != X9 & X6 != X9 & X7 != X9) | ~r2_hidden(X9,X8)) & (X0 = X9 | X1 = X9 | X2 = X9 | X3 = X9 | X4 = X9 | X5 = X9 | X6 = X9 | X7 = X9 | r2_hidden(X9,X8)))) & (! [X10] : ((r2_hidden(X10,X8) | (X0 != X10 & X1 != X10 & X2 != X10 & X3 != X10 & X4 != X10 & X5 != X10 & X6 != X10 & X7 != X10)) & (X0 = X10 | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | ~r2_hidden(X10,X8))) | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)))),
% 1.40/0.55    inference(rectify,[],[f41])).
% 1.40/0.55  fof(f41,plain,(
% 1.40/0.55    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9 | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.40/0.55    inference(flattening,[],[f40])).
% 1.40/0.55  fof(f40,plain,(
% 1.40/0.55    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : ((sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | ? [X9] : (((X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9) | ~r2_hidden(X9,X8)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | r2_hidden(X9,X8)))) & (! [X9] : ((r2_hidden(X9,X8) | (X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)) & ((X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9) | ~r2_hidden(X9,X8))) | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)))),
% 1.40/0.55    inference(nnf_transformation,[],[f25])).
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X7,X6,X5,X4,X3,X2,X1,X0,X8] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.40/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.40/0.55  fof(f242,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1))),
% 1.40/0.55    inference(forward_demodulation,[],[f241,f201])).
% 1.40/0.55  fof(f201,plain,(
% 1.40/0.55    sK1 = sK2),
% 1.40/0.55    inference(subsumption_resolution,[],[f200,f182])).
% 1.40/0.55  fof(f182,plain,(
% 1.40/0.55    ~r1_tarski(sK1,sK2) | sK1 = sK2),
% 1.40/0.55    inference(resolution,[],[f178,f60])).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(flattening,[],[f33])).
% 1.40/0.55  fof(f33,plain,(
% 1.40/0.55    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.40/0.55    inference(nnf_transformation,[],[f3])).
% 1.40/0.55  fof(f3,axiom,(
% 1.40/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.40/0.55  fof(f178,plain,(
% 1.40/0.55    r1_tarski(sK2,sK1)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f47,f46,f166,f56])).
% 1.40/0.55  fof(f56,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f32])).
% 1.40/0.55  fof(f32,plain,(
% 1.40/0.55    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.40/0.55    inference(nnf_transformation,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.40/0.55    inference(flattening,[],[f22])).
% 1.40/0.55  fof(f22,plain,(
% 1.40/0.55    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f14])).
% 1.40/0.55  fof(f14,axiom,(
% 1.40/0.55    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.40/0.55  fof(f166,plain,(
% 1.40/0.55    r1_ordinal1(sK2,sK1)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f47,f46,f164,f52])).
% 1.40/0.55  fof(f52,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f20])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.40/0.55    inference(flattening,[],[f19])).
% 1.40/0.55  fof(f19,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 1.40/0.55  fof(f164,plain,(
% 1.40/0.55    ~r2_hidden(sK1,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f163,f55])).
% 1.40/0.55  fof(f55,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f21])).
% 1.40/0.55  fof(f21,plain,(
% 1.40/0.55    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 1.40/0.55  fof(f163,plain,(
% 1.40/0.55    r2_hidden(sK2,sK1) | ~r2_hidden(sK1,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f160,f46])).
% 1.40/0.55  fof(f160,plain,(
% 1.40/0.55    r2_hidden(sK2,sK1) | ~v3_ordinal1(sK1) | ~r2_hidden(sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f135,f138])).
% 1.40/0.55  fof(f138,plain,(
% 1.40/0.55    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f100,f111])).
% 1.40/0.55  fof(f111,plain,(
% 1.40/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 1.40/0.55    inference(equality_resolution,[],[f106])).
% 1.40/0.55  fof(f106,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.40/0.55    inference(definition_unfolding,[],[f63,f97])).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f53,f96])).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f54,f95])).
% 1.40/0.55  fof(f95,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f61,f94])).
% 1.40/0.55  fof(f94,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f68,f93])).
% 1.40/0.55  fof(f93,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f69,f92])).
% 1.40/0.55  fof(f92,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f70,f71])).
% 1.40/0.55  fof(f71,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.40/0.55  fof(f70,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.40/0.55  fof(f69,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f8])).
% 1.40/0.55  fof(f8,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.40/0.55  fof(f68,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f5])).
% 1.40/0.55  fof(f5,axiom,(
% 1.40/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.40/0.55  fof(f53,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f11])).
% 1.40/0.55  fof(f11,axiom,(
% 1.40/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.40/0.55  fof(f63,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f37,f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f37,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.40/0.55    inference(rectify,[],[f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.40/0.55    inference(flattening,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 1.40/0.55    inference(nnf_transformation,[],[f2])).
% 1.40/0.55  fof(f2,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.40/0.55  fof(f100,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | ~r1_ordinal1(sK1,sK2)),
% 1.40/0.55    inference(definition_unfolding,[],[f49,f99])).
% 1.40/0.55  fof(f99,plain,(
% 1.40/0.55    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.40/0.55    inference(definition_unfolding,[],[f51,f97,f98])).
% 1.40/0.55  fof(f98,plain,(
% 1.40/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.40/0.55    inference(definition_unfolding,[],[f50,f96])).
% 1.40/0.55  fof(f50,plain,(
% 1.40/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f4])).
% 1.40/0.55  fof(f4,axiom,(
% 1.40/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f13])).
% 1.40/0.55  fof(f13,axiom,(
% 1.40/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f31,plain,(
% 1.40/0.55    ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f30,f29])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ? [X1] : ((~r1_ordinal1(sK1,X1) | ~r2_hidden(sK1,k1_ordinal1(X1))) & (r1_ordinal1(sK1,X1) | r2_hidden(sK1,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK1,sK2) | ~r2_hidden(sK1,k1_ordinal1(sK2))) & (r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))) & v3_ordinal1(sK2))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.40/0.55    inference(flattening,[],[f27])).
% 1.40/0.55  fof(f27,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.40/0.55    inference(nnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.40/0.55    inference(ennf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,negated_conjecture,(
% 1.40/0.55    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.40/0.55    inference(negated_conjecture,[],[f16])).
% 1.40/0.55  fof(f16,conjecture,(
% 1.40/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.40/0.55  fof(f135,plain,(
% 1.40/0.55    ( ! [X2] : (r1_ordinal1(X2,sK2) | r2_hidden(sK2,X2) | ~v3_ordinal1(X2)) )),
% 1.40/0.55    inference(resolution,[],[f47,f52])).
% 1.40/0.55  fof(f46,plain,(
% 1.40/0.55    v3_ordinal1(sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f47,plain,(
% 1.40/0.55    v3_ordinal1(sK2)),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f200,plain,(
% 1.40/0.55    sK1 = sK2 | r1_tarski(sK1,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f199,f46])).
% 1.40/0.55  fof(f199,plain,(
% 1.40/0.55    sK1 = sK2 | r1_tarski(sK1,sK2) | ~v3_ordinal1(sK1)),
% 1.40/0.55    inference(resolution,[],[f197,f133])).
% 1.40/0.55  fof(f133,plain,(
% 1.40/0.55    ( ! [X0] : (~r1_ordinal1(X0,sK2) | r1_tarski(X0,sK2) | ~v3_ordinal1(X0)) )),
% 1.40/0.55    inference(resolution,[],[f47,f56])).
% 1.40/0.55  fof(f197,plain,(
% 1.40/0.55    r1_ordinal1(sK1,sK2) | sK1 = sK2),
% 1.40/0.55    inference(duplicate_literal_removal,[],[f196])).
% 1.40/0.55  fof(f196,plain,(
% 1.40/0.55    sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | sK1 = sK2 | r1_ordinal1(sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f186,f121])).
% 1.40/0.55  fof(f186,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (~sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK1 = X5 | sK1 = X6 | sK1 = X7 | r1_ordinal1(sK1,sK2)) )),
% 1.40/0.55    inference(subsumption_resolution,[],[f184,f164])).
% 1.40/0.55  fof(f184,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(sK1,sK2) | r1_ordinal1(sK1,sK2) | sK1 = X0 | sK1 = X1 | sK1 = X2 | sK1 = X3 | sK1 = X4 | sK1 = X5 | sK1 = X6 | sK1 = X7 | ~sP0(X7,X0,X1,X2,X3,X4,X5,X6,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))) )),
% 1.40/0.55    inference(resolution,[],[f143,f72])).
% 1.40/0.55  fof(f72,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X10,X8,X7,X5,X3,X1] : (~r2_hidden(X10,X8) | X1 = X10 | X2 = X10 | X3 = X10 | X4 = X10 | X5 = X10 | X6 = X10 | X7 = X10 | X0 = X10 | ~sP0(X0,X1,X2,X3,X4,X5,X6,X7,X8)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f143,plain,(
% 1.40/0.55    r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | r2_hidden(sK1,sK2) | r1_ordinal1(sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f101,f112])).
% 1.40/0.55  fof(f112,plain,(
% 1.40/0.55    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f107])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.40/0.55    inference(definition_unfolding,[],[f62,f97])).
% 1.40/0.55  fof(f62,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  fof(f101,plain,(
% 1.40/0.55    r2_hidden(sK1,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)))) | r1_ordinal1(sK1,sK2)),
% 1.40/0.55    inference(definition_unfolding,[],[f48,f99])).
% 1.40/0.55  fof(f48,plain,(
% 1.40/0.55    r1_ordinal1(sK1,sK2) | r2_hidden(sK1,k1_ordinal1(sK2))),
% 1.40/0.55    inference(cnf_transformation,[],[f31])).
% 1.40/0.55  fof(f241,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.40/0.55    inference(subsumption_resolution,[],[f210,f125])).
% 1.40/0.55  fof(f125,plain,(
% 1.40/0.55    r1_ordinal1(sK1,sK1)),
% 1.40/0.55    inference(unit_resulting_resolution,[],[f46,f108,f46,f57])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f32])).
% 1.40/0.55  fof(f108,plain,(
% 1.40/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f59])).
% 1.40/0.55  fof(f59,plain,(
% 1.40/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.40/0.55    inference(cnf_transformation,[],[f34])).
% 1.40/0.55  fof(f210,plain,(
% 1.40/0.55    ~r1_ordinal1(sK1,sK1) | ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 1.40/0.55    inference(backward_demodulation,[],[f139,f201])).
% 1.40/0.55  fof(f139,plain,(
% 1.40/0.55    ~r2_hidden(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~r1_ordinal1(sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f100,f110])).
% 1.40/0.55  fof(f110,plain,(
% 1.40/0.55    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 1.40/0.55    inference(equality_resolution,[],[f105])).
% 1.40/0.55  fof(f105,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) != X2) )),
% 1.40/0.55    inference(definition_unfolding,[],[f64,f97])).
% 1.40/0.55  fof(f64,plain,(
% 1.40/0.55    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  fof(f121,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7))) )),
% 1.40/0.55    inference(equality_resolution,[],[f90])).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    ( ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8) )),
% 1.40/0.55    inference(cnf_transformation,[],[f45])).
% 1.40/0.55  fof(f45,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : ((k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 | ~sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8)) & (sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8) | k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) != X8))),
% 1.40/0.55    inference(nnf_transformation,[],[f26])).
% 1.40/0.55  fof(f26,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> sP0(X7,X6,X5,X4,X3,X2,X1,X0,X8))),
% 1.40/0.55    inference(definition_folding,[],[f24,f25])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> (X7 = X9 | X6 = X9 | X5 = X9 | X4 = X9 | X3 = X9 | X2 = X9 | X1 = X9 | X0 = X9)))),
% 1.40/0.55    inference(ennf_transformation,[],[f12])).
% 1.40/0.55  fof(f12,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = X8 <=> ! [X9] : (r2_hidden(X9,X8) <=> ~(X7 != X9 & X6 != X9 & X5 != X9 & X4 != X9 & X3 != X9 & X2 != X9 & X1 != X9 & X0 != X9)))),
% 1.40/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (28493)------------------------------
% 1.40/0.55  % (28493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (28493)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (28493)Memory used [KB]: 6396
% 1.40/0.55  % (28493)Time elapsed: 0.149 s
% 1.40/0.55  % (28493)------------------------------
% 1.40/0.55  % (28493)------------------------------
% 1.40/0.56  % (28481)Success in time 0.204 s
%------------------------------------------------------------------------------
