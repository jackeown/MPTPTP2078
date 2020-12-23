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
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 664 expanded)
%              Number of leaves         :   14 ( 195 expanded)
%              Depth                    :   21
%              Number of atoms          :  337 (3308 expanded)
%              Number of equality atoms :   44 ( 705 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(subsumption_resolution,[],[f529,f270])).

fof(f270,plain,(
    ~ r2_hidden(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f39,f71,f264,f182])).

fof(f182,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X1,sK0)
      | sK0 = k2_xboole_0(X1,k1_tarski(X1))
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f143,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f143,plain,(
    ! [X1] :
      ( r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),sK0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f141,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f49,f48])).

fof(f48,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f49,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f141,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),sK0)
      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(resolution,[],[f101,f97])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r1_ordinal1(X1,sK0)
      | r1_tarski(X1,sK0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f39,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f101,plain,(
    ! [X4] :
      ( r1_ordinal1(k2_xboole_0(X4,k1_tarski(X4)),sK0)
      | ~ r2_hidden(X4,sK0)
      | ~ v3_ordinal1(X4) ) ),
    inference(resolution,[],[f39,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f54,f48])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(k1_ordinal1(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,X1)
              | ~ r1_ordinal1(k1_ordinal1(X0),X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f264,plain,(
    r1_tarski(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f90,f248,f59])).

fof(f248,plain,(
    r1_ordinal1(sK0,k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f72,f239])).

fof(f239,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_xboole_0(sK0,k1_tarski(sK0)))
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X1,k2_xboole_0(sK0,k1_tarski(sK0))) ) ),
    inference(resolution,[],[f125,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f65,f48])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f125,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k2_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(k2_xboole_0(sK0,k1_tarski(sK0)))))
      | r1_ordinal1(X6,k2_xboole_0(sK0,k1_tarski(sK0)))
      | ~ v3_ordinal1(X6) ) ),
    inference(resolution,[],[f90,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f56,f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f72,plain,(
    ! [X0] : r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0))) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f47,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f90,plain,(
    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f73])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_tarski(X0)) != X0 ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f46,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f39,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f529,plain,(
    r2_hidden(sK0,sK0) ),
    inference(forward_demodulation,[],[f527,f461])).

fof(f461,plain,(
    sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f460,f69])).

fof(f69,plain,
    ( ~ v4_ordinal1(sK0)
    | sK0 = k2_xboole_0(sK1,k1_tarski(sK1)) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f42,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f460,plain,(
    v4_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f459,f39])).

fof(f459,plain,
    ( v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(duplicate_literal_removal,[],[f458])).

fof(f458,plain,
    ( v4_ordinal1(sK0)
    | v4_ordinal1(sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f457,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f457,plain,
    ( ~ v3_ordinal1(sK2(sK0))
    | v4_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f456,f95])).

fof(f95,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | v4_ordinal1(sK0) ),
    inference(resolution,[],[f39,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | v4_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f456,plain,
    ( v4_ordinal1(sK0)
    | ~ r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f455,f67])).

fof(f67,plain,(
    ! [X2] :
      ( sK0 != k2_xboole_0(X2,k1_tarski(X2))
      | v4_ordinal1(sK0)
      | ~ v3_ordinal1(X2) ) ),
    inference(definition_unfolding,[],[f45,f48])).

fof(f45,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f455,plain,
    ( sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | v4_ordinal1(sK0)
    | ~ r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f452,f73])).

fof(f452,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | v4_ordinal1(sK0)
    | ~ r2_hidden(sK2(sK0),sK0)
    | ~ v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f185,f101])).

fof(f185,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | ~ v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))))
    | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))
    | v4_ordinal1(sK0) ),
    inference(resolution,[],[f145,f99])).

fof(f99,plain,
    ( ~ r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0)
    | v4_ordinal1(sK0) ),
    inference(resolution,[],[f39,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | ~ r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0)
      | v4_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f53,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f145,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK0)
      | ~ v3_ordinal1(X0)
      | ~ r1_ordinal1(X0,sK0)
      | sK0 = X0 ) ),
    inference(resolution,[],[f102,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f64,f48])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,(
    ! [X5] :
      ( r2_hidden(X5,k2_xboole_0(sK0,k1_tarski(sK0)))
      | ~ r1_ordinal1(X5,sK0)
      | ~ v3_ordinal1(X5) ) ),
    inference(resolution,[],[f39,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X1)
      | ~ r1_ordinal1(X0,X1)
      | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f57,f48])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f527,plain,(
    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f39,f460,f462,f499,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( ~ v4_ordinal1(X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f50,f48])).

fof(f50,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f499,plain,(
    r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f72,f461])).

fof(f462,plain,(
    v3_ordinal1(sK1) ),
    inference(unit_resulting_resolution,[],[f460,f40])).

fof(f40,plain,
    ( ~ v4_ordinal1(sK0)
    | v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:30:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.54  % (17192)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (17189)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (17182)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (17184)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (17179)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.55  % (17170)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.55  % (17198)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.55  % (17190)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.55  % (17197)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.56  % (17197)Refutation not found, incomplete strategy% (17197)------------------------------
% 0.20/0.56  % (17197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (17181)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.56  % (17176)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  % (17197)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (17197)Memory used [KB]: 10746
% 0.20/0.56  % (17197)Time elapsed: 0.142 s
% 0.20/0.56  % (17197)------------------------------
% 0.20/0.56  % (17197)------------------------------
% 0.20/0.56  % (17172)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.57  % (17173)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.57  % (17179)Refutation not found, incomplete strategy% (17179)------------------------------
% 0.20/0.57  % (17179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (17179)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (17179)Memory used [KB]: 10746
% 0.20/0.57  % (17179)Time elapsed: 0.150 s
% 0.20/0.57  % (17179)------------------------------
% 0.20/0.57  % (17179)------------------------------
% 0.20/0.57  % (17180)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.58  % (17169)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.58  % (17174)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.58  % (17171)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.59  % (17175)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.59  % (17194)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.59  % (17191)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.82/0.59  % (17187)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.82/0.60  % (17186)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.82/0.60  % (17193)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.82/0.60  % (17177)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.82/0.60  % (17178)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.82/0.60  % (17185)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.82/0.60  % (17196)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.82/0.61  % (17185)Refutation not found, incomplete strategy% (17185)------------------------------
% 1.82/0.61  % (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (17185)Termination reason: Refutation not found, incomplete strategy
% 1.82/0.61  
% 1.82/0.61  % (17185)Memory used [KB]: 10618
% 1.82/0.61  % (17185)Time elapsed: 0.183 s
% 1.82/0.61  % (17185)------------------------------
% 1.82/0.61  % (17185)------------------------------
% 1.82/0.61  % (17183)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.82/0.61  % (17195)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.82/0.61  % (17188)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 2.03/0.62  % (17180)Refutation found. Thanks to Tanya!
% 2.03/0.62  % SZS status Theorem for theBenchmark
% 2.03/0.62  % SZS output start Proof for theBenchmark
% 2.03/0.62  fof(f530,plain,(
% 2.03/0.62    $false),
% 2.03/0.62    inference(subsumption_resolution,[],[f529,f270])).
% 2.03/0.62  fof(f270,plain,(
% 2.03/0.62    ~r2_hidden(sK0,sK0)),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f39,f71,f264,f182])).
% 2.03/0.62  fof(f182,plain,(
% 2.03/0.62    ( ! [X1] : (~r1_tarski(sK0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X1,sK0) | sK0 = k2_xboole_0(X1,k1_tarski(X1)) | ~v3_ordinal1(X1)) )),
% 2.03/0.62    inference(resolution,[],[f143,f63])).
% 2.03/0.62  fof(f63,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f36])).
% 2.03/0.62  fof(f36,plain,(
% 2.03/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.62    inference(flattening,[],[f35])).
% 2.03/0.62  fof(f35,plain,(
% 2.03/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.62    inference(nnf_transformation,[],[f1])).
% 2.03/0.62  fof(f1,axiom,(
% 2.03/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.62  fof(f143,plain,(
% 2.03/0.62    ( ! [X1] : (r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),sK0) | ~v3_ordinal1(X1) | ~r2_hidden(X1,sK0)) )),
% 2.03/0.62    inference(subsumption_resolution,[],[f141,f73])).
% 2.03/0.62  fof(f73,plain,(
% 2.03/0.62    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f49,f48])).
% 2.03/0.62  fof(f48,plain,(
% 2.03/0.62    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 2.03/0.62    inference(cnf_transformation,[],[f2])).
% 2.03/0.62  fof(f2,axiom,(
% 2.03/0.62    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 2.03/0.62  fof(f49,plain,(
% 2.03/0.62    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f16])).
% 2.03/0.62  fof(f16,plain,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(ennf_transformation,[],[f8])).
% 2.03/0.62  fof(f8,axiom,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 2.03/0.62  fof(f141,plain,(
% 2.03/0.62    ( ! [X1] : (~r2_hidden(X1,sK0) | ~v3_ordinal1(X1) | r1_tarski(k2_xboole_0(X1,k1_tarski(X1)),sK0) | ~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))) )),
% 2.03/0.62    inference(resolution,[],[f101,f97])).
% 2.03/0.62  fof(f97,plain,(
% 2.03/0.62    ( ! [X1] : (~r1_ordinal1(X1,sK0) | r1_tarski(X1,sK0) | ~v3_ordinal1(X1)) )),
% 2.03/0.62    inference(resolution,[],[f39,f59])).
% 2.03/0.62  fof(f59,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f34])).
% 2.03/0.62  fof(f34,plain,(
% 2.03/0.62    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(nnf_transformation,[],[f24])).
% 2.03/0.62  fof(f24,plain,(
% 2.03/0.62    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(flattening,[],[f23])).
% 2.03/0.62  fof(f23,plain,(
% 2.03/0.62    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 2.03/0.62    inference(ennf_transformation,[],[f3])).
% 2.03/0.62  fof(f3,axiom,(
% 2.03/0.62    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 2.03/0.62  fof(f101,plain,(
% 2.03/0.62    ( ! [X4] : (r1_ordinal1(k2_xboole_0(X4,k1_tarski(X4)),sK0) | ~r2_hidden(X4,sK0) | ~v3_ordinal1(X4)) )),
% 2.03/0.62    inference(resolution,[],[f39,f77])).
% 2.03/0.62  fof(f77,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | r1_ordinal1(k2_xboole_0(X0,k1_tarski(X0)),X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f54,f48])).
% 2.03/0.62  fof(f54,plain,(
% 2.03/0.62    ( ! [X0,X1] : (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f32])).
% 2.03/0.62  fof(f32,plain,(
% 2.03/0.62    ! [X0] : (! [X1] : (((r2_hidden(X0,X1) | ~r1_ordinal1(k1_ordinal1(X0),X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(nnf_transformation,[],[f19])).
% 2.03/0.62  fof(f19,plain,(
% 2.03/0.62    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(ennf_transformation,[],[f9])).
% 2.03/0.62  fof(f9,axiom,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 2.03/0.62  fof(f264,plain,(
% 2.03/0.62    r1_tarski(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f39,f90,f248,f59])).
% 2.03/0.62  fof(f248,plain,(
% 2.03/0.62    r1_ordinal1(sK0,k2_xboole_0(sK0,k1_tarski(sK0)))),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f39,f72,f239])).
% 2.03/0.62  fof(f239,plain,(
% 2.03/0.62    ( ! [X1] : (~r2_hidden(X1,k2_xboole_0(sK0,k1_tarski(sK0))) | ~v3_ordinal1(X1) | r1_ordinal1(X1,k2_xboole_0(sK0,k1_tarski(sK0)))) )),
% 2.03/0.62    inference(resolution,[],[f125,f81])).
% 2.03/0.62  fof(f81,plain,(
% 2.03/0.62    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f65,f48])).
% 2.03/0.62  fof(f65,plain,(
% 2.03/0.62    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f38])).
% 2.03/0.62  fof(f38,plain,(
% 2.03/0.62    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.03/0.62    inference(flattening,[],[f37])).
% 2.03/0.62  fof(f37,plain,(
% 2.03/0.62    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 2.03/0.62    inference(nnf_transformation,[],[f5])).
% 2.03/0.62  fof(f5,axiom,(
% 2.03/0.62    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 2.03/0.62  fof(f125,plain,(
% 2.03/0.62    ( ! [X6] : (~r2_hidden(X6,k2_xboole_0(k2_xboole_0(sK0,k1_tarski(sK0)),k1_tarski(k2_xboole_0(sK0,k1_tarski(sK0))))) | r1_ordinal1(X6,k2_xboole_0(sK0,k1_tarski(sK0))) | ~v3_ordinal1(X6)) )),
% 2.03/0.62    inference(resolution,[],[f90,f79])).
% 2.03/0.62  fof(f79,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f56,f48])).
% 2.03/0.62  fof(f56,plain,(
% 2.03/0.62    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f33])).
% 2.03/0.62  fof(f33,plain,(
% 2.03/0.62    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(nnf_transformation,[],[f20])).
% 2.03/0.62  fof(f20,plain,(
% 2.03/0.62    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(ennf_transformation,[],[f10])).
% 2.03/0.62  fof(f10,axiom,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_ordinal1)).
% 2.03/0.62  fof(f72,plain,(
% 2.03/0.62    ( ! [X0] : (r2_hidden(X0,k2_xboole_0(X0,k1_tarski(X0)))) )),
% 2.03/0.62    inference(definition_unfolding,[],[f47,f48])).
% 2.03/0.62  fof(f47,plain,(
% 2.03/0.62    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 2.03/0.62    inference(cnf_transformation,[],[f4])).
% 2.03/0.62  fof(f4,axiom,(
% 2.03/0.62    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 2.03/0.62  fof(f90,plain,(
% 2.03/0.62    v3_ordinal1(k2_xboole_0(sK0,k1_tarski(sK0)))),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f39,f73])).
% 2.03/0.62  fof(f71,plain,(
% 2.03/0.62    ( ! [X0] : (k2_xboole_0(X0,k1_tarski(X0)) != X0) )),
% 2.03/0.62    inference(definition_unfolding,[],[f46,f48])).
% 2.03/0.62  fof(f46,plain,(
% 2.03/0.62    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 2.03/0.62    inference(cnf_transformation,[],[f6])).
% 2.03/0.62  fof(f6,axiom,(
% 2.03/0.62    ! [X0] : k1_ordinal1(X0) != X0),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 2.03/0.62  fof(f39,plain,(
% 2.03/0.62    v3_ordinal1(sK0)),
% 2.03/0.62    inference(cnf_transformation,[],[f27])).
% 2.03/0.62  fof(f27,plain,(
% 2.03/0.62    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 2.03/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f26,f25])).
% 2.03/0.62  fof(f25,plain,(
% 2.03/0.62    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 2.03/0.62    introduced(choice_axiom,[])).
% 2.03/0.62  fof(f26,plain,(
% 2.03/0.62    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 2.03/0.62    introduced(choice_axiom,[])).
% 2.03/0.62  fof(f15,plain,(
% 2.03/0.62    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 2.03/0.62    inference(ennf_transformation,[],[f14])).
% 2.03/0.62  fof(f14,plain,(
% 2.03/0.62    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 2.03/0.62    inference(rectify,[],[f13])).
% 2.03/0.62  fof(f13,negated_conjecture,(
% 2.03/0.62    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.03/0.62    inference(negated_conjecture,[],[f12])).
% 2.03/0.62  fof(f12,conjecture,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).
% 2.03/0.62  fof(f529,plain,(
% 2.03/0.62    r2_hidden(sK0,sK0)),
% 2.03/0.62    inference(forward_demodulation,[],[f527,f461])).
% 2.03/0.62  fof(f461,plain,(
% 2.03/0.62    sK0 = k2_xboole_0(sK1,k1_tarski(sK1))),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f460,f69])).
% 2.03/0.62  fof(f69,plain,(
% 2.03/0.62    ~v4_ordinal1(sK0) | sK0 = k2_xboole_0(sK1,k1_tarski(sK1))),
% 2.03/0.62    inference(definition_unfolding,[],[f42,f48])).
% 2.03/0.62  fof(f42,plain,(
% 2.03/0.62    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 2.03/0.62    inference(cnf_transformation,[],[f27])).
% 2.03/0.62  fof(f460,plain,(
% 2.03/0.62    v4_ordinal1(sK0)),
% 2.03/0.62    inference(subsumption_resolution,[],[f459,f39])).
% 2.03/0.62  fof(f459,plain,(
% 2.03/0.62    v4_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 2.03/0.62    inference(duplicate_literal_removal,[],[f458])).
% 2.03/0.62  fof(f458,plain,(
% 2.03/0.62    v4_ordinal1(sK0) | v4_ordinal1(sK0) | ~v3_ordinal1(sK0)),
% 2.03/0.62    inference(resolution,[],[f457,f51])).
% 2.03/0.62  fof(f51,plain,(
% 2.03/0.62    ( ! [X0] : (v3_ordinal1(sK2(X0)) | v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f31])).
% 2.03/0.62  fof(f31,plain,(
% 2.03/0.62    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 2.03/0.62  fof(f30,plain,(
% 2.03/0.62    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 2.03/0.62    introduced(choice_axiom,[])).
% 2.03/0.62  fof(f29,plain,(
% 2.03/0.62    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(rectify,[],[f28])).
% 2.03/0.62  fof(f28,plain,(
% 2.03/0.62    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(nnf_transformation,[],[f18])).
% 2.03/0.62  fof(f18,plain,(
% 2.03/0.62    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(flattening,[],[f17])).
% 2.03/0.62  fof(f17,plain,(
% 2.03/0.62    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 2.03/0.62    inference(ennf_transformation,[],[f11])).
% 2.03/0.62  fof(f11,axiom,(
% 2.03/0.62    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 2.03/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 2.03/0.62  fof(f457,plain,(
% 2.03/0.62    ~v3_ordinal1(sK2(sK0)) | v4_ordinal1(sK0)),
% 2.03/0.62    inference(subsumption_resolution,[],[f456,f95])).
% 2.03/0.62  fof(f95,plain,(
% 2.03/0.62    r2_hidden(sK2(sK0),sK0) | v4_ordinal1(sK0)),
% 2.03/0.62    inference(resolution,[],[f39,f52])).
% 2.03/0.62  fof(f52,plain,(
% 2.03/0.62    ( ! [X0] : (~v3_ordinal1(X0) | r2_hidden(sK2(X0),X0) | v4_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f31])).
% 2.03/0.62  fof(f456,plain,(
% 2.03/0.62    v4_ordinal1(sK0) | ~r2_hidden(sK2(sK0),sK0) | ~v3_ordinal1(sK2(sK0))),
% 2.03/0.62    inference(subsumption_resolution,[],[f455,f67])).
% 2.03/0.62  fof(f67,plain,(
% 2.03/0.62    ( ! [X2] : (sK0 != k2_xboole_0(X2,k1_tarski(X2)) | v4_ordinal1(sK0) | ~v3_ordinal1(X2)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f45,f48])).
% 2.03/0.62  fof(f45,plain,(
% 2.03/0.62    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f27])).
% 2.03/0.62  fof(f455,plain,(
% 2.03/0.62    sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | v4_ordinal1(sK0) | ~r2_hidden(sK2(sK0),sK0) | ~v3_ordinal1(sK2(sK0))),
% 2.03/0.62    inference(subsumption_resolution,[],[f452,f73])).
% 2.03/0.62  fof(f452,plain,(
% 2.03/0.62    ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | v4_ordinal1(sK0) | ~r2_hidden(sK2(sK0),sK0) | ~v3_ordinal1(sK2(sK0))),
% 2.03/0.62    inference(resolution,[],[f185,f101])).
% 2.03/0.62  fof(f185,plain,(
% 2.03/0.62    ~r1_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | ~v3_ordinal1(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0)))) | sK0 = k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))) | v4_ordinal1(sK0)),
% 2.03/0.62    inference(resolution,[],[f145,f99])).
% 2.03/0.62  fof(f99,plain,(
% 2.03/0.62    ~r2_hidden(k2_xboole_0(sK2(sK0),k1_tarski(sK2(sK0))),sK0) | v4_ordinal1(sK0)),
% 2.03/0.62    inference(resolution,[],[f39,f74])).
% 2.03/0.62  fof(f74,plain,(
% 2.03/0.62    ( ! [X0] : (~v3_ordinal1(X0) | ~r2_hidden(k2_xboole_0(sK2(X0),k1_tarski(sK2(X0))),X0) | v4_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f53,f48])).
% 2.03/0.62  fof(f53,plain,(
% 2.03/0.62    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK2(X0)),X0) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f31])).
% 2.03/0.62  fof(f145,plain,(
% 2.03/0.62    ( ! [X0] : (r2_hidden(X0,sK0) | ~v3_ordinal1(X0) | ~r1_ordinal1(X0,sK0) | sK0 = X0) )),
% 2.03/0.62    inference(resolution,[],[f102,f82])).
% 2.03/0.62  fof(f82,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 2.03/0.62    inference(definition_unfolding,[],[f64,f48])).
% 2.03/0.62  fof(f64,plain,(
% 2.03/0.62    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 2.03/0.62    inference(cnf_transformation,[],[f38])).
% 2.03/0.62  fof(f102,plain,(
% 2.03/0.62    ( ! [X5] : (r2_hidden(X5,k2_xboole_0(sK0,k1_tarski(sK0))) | ~r1_ordinal1(X5,sK0) | ~v3_ordinal1(X5)) )),
% 2.03/0.62    inference(resolution,[],[f39,f78])).
% 2.03/0.62  fof(f78,plain,(
% 2.03/0.62    ( ! [X0,X1] : (~v3_ordinal1(X1) | ~r1_ordinal1(X0,X1) | r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f57,f48])).
% 2.03/0.62  fof(f57,plain,(
% 2.03/0.62    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f33])).
% 2.03/0.62  fof(f527,plain,(
% 2.03/0.62    r2_hidden(k2_xboole_0(sK1,k1_tarski(sK1)),sK0)),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f39,f460,f462,f499,f75])).
% 2.03/0.62  fof(f75,plain,(
% 2.03/0.62    ( ! [X2,X0] : (~v4_ordinal1(X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | r2_hidden(k2_xboole_0(X2,k1_tarski(X2)),X0) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(definition_unfolding,[],[f50,f48])).
% 2.03/0.62  fof(f50,plain,(
% 2.03/0.62    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 2.03/0.62    inference(cnf_transformation,[],[f31])).
% 2.03/0.62  fof(f499,plain,(
% 2.03/0.62    r2_hidden(sK1,sK0)),
% 2.03/0.62    inference(superposition,[],[f72,f461])).
% 2.03/0.62  fof(f462,plain,(
% 2.03/0.62    v3_ordinal1(sK1)),
% 2.03/0.62    inference(unit_resulting_resolution,[],[f460,f40])).
% 2.03/0.62  fof(f40,plain,(
% 2.03/0.62    ~v4_ordinal1(sK0) | v3_ordinal1(sK1)),
% 2.03/0.62    inference(cnf_transformation,[],[f27])).
% 2.03/0.62  % SZS output end Proof for theBenchmark
% 2.03/0.62  % (17180)------------------------------
% 2.03/0.62  % (17180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.62  % (17180)Termination reason: Refutation
% 2.03/0.62  
% 2.03/0.62  % (17180)Memory used [KB]: 6524
% 2.03/0.62  % (17180)Time elapsed: 0.189 s
% 2.03/0.62  % (17180)------------------------------
% 2.03/0.62  % (17180)------------------------------
% 2.03/0.63  % (17168)Success in time 0.267 s
%------------------------------------------------------------------------------
