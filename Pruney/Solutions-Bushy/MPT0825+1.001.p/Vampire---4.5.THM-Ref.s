%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0825+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:42 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 164 expanded)
%              Number of leaves         :   12 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  217 ( 615 expanded)
%              Number of equality atoms :   36 ( 109 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(global_subsumption,[],[f92,f95])).

fof(f95,plain,(
    ~ r2_hidden(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK2) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,
    ( ~ r2_hidden(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK2)
    | ~ r2_hidden(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK2) ),
    inference(resolution,[],[f83,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f83,plain,(
    ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2))),k2_zfmisc_1(sK2,sK2)) ),
    inference(global_subsumption,[],[f28,f81])).

fof(f81,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2))),k2_zfmisc_1(sK2,sK2))
    | r1_tarski(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(superposition,[],[f67,f78])).

fof(f78,plain,(
    sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) = sK4(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(resolution,[],[f73,f28])).

fof(f73,plain,(
    ! [X4,X5] :
      ( r1_tarski(k6_relat_1(X4),X5)
      | sK3(k6_relat_1(X4),X5) = sK4(k6_relat_1(X4),X5) ) ),
    inference(resolution,[],[f66,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k6_relat_1(X2))
      | X0 = X1 ) ),
    inference(resolution,[],[f48,f54])).

fof(f54,plain,(
    ! [X0] : sP7(k6_relat_1(X0)) ),
    inference(resolution,[],[f47,f53])).

fof(f53,plain,(
    ! [X1] : sP0(X1,k6_relat_1(X1)) ),
    inference(subsumption_resolution,[],[f45,f52])).

fof(f52,plain,(
    ! [X0,X1] : sP1(k6_relat_1(X0),X1) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | sP1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( sP1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f9,f11,f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2,X3] :
          ( r2_hidden(k4_tarski(X2,X3),X1)
        <=> ( X2 = X3
            & r2_hidden(X2,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f11,plain,(
    ! [X1,X0] :
      ( ( k6_relat_1(X0) = X1
      <=> sP0(X0,X1) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_relat_1)).

fof(f45,plain,(
    ! [X1] :
      ( sP0(X1,k6_relat_1(X1))
      | ~ sP1(k6_relat_1(X1),X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k6_relat_1(X1) != X0
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X1) = X0
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k6_relat_1(X1) != X0 ) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ( ( k6_relat_1(X0) = X1
          | ~ sP0(X0,X1) )
        & ( sP0(X0,X1)
          | k6_relat_1(X0) != X1 ) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | sP7(X1) ) ),
    inference(cnf_transformation,[],[f47_D])).

fof(f47_D,plain,(
    ! [X1] :
      ( ! [X0] : ~ sP0(X0,X1)
    <=> ~ sP7(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f48,plain,(
    ! [X4,X5,X1] :
      ( ~ sP7(X1)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | X4 = X5 ) ),
    inference(general_splitting,[],[f36,f47_D])).

fof(f36,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK5(X0,X1) != sK6(X0,X1)
            | ~ r2_hidden(sK5(X0,X1),X0)
            | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
          & ( ( sK5(X0,X1) = sK6(X0,X1)
              & r2_hidden(sK5(X0,X1),X0) )
            | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) )
      & ( ! [X4,X5] :
            ( ( r2_hidden(k4_tarski(X4,X5),X1)
              | X4 != X5
              | ~ r2_hidden(X4,X0) )
            & ( ( X4 = X5
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f23,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK5(X0,X1) != sK6(X0,X1)
          | ~ r2_hidden(sK5(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) )
        & ( ( sK5(X0,X1) = sK6(X0,X1)
            & r2_hidden(sK5(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK5(X0,X1),sK6(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(k6_relat_1(X0),X1),sK4(k6_relat_1(X0),X1)),k6_relat_1(X0))
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
              & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X4,X5),X1)
                | ~ r2_hidden(k4_tarski(X4,X5),X0) )
            | ~ r1_tarski(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X2,X3),X1)
          & r2_hidden(k4_tarski(X2,X3),X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(k6_relat_1(X0),X1),sK4(k6_relat_1(X0),X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f28,plain,(
    ~ r1_tarski(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ~ r1_tarski(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relset_1)).

fof(f92,plain,(
    r2_hidden(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK2) ),
    inference(resolution,[],[f86,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( sP8(X0,k6_relat_1(X1))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f49,f53])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( ~ sP0(X0,X1)
      | r2_hidden(X4,X0)
      | sP8(X4,X1) ) ),
    inference(cnf_transformation,[],[f49_D])).

fof(f49_D,plain,(
    ! [X1,X4] :
      ( ! [X0] :
          ( ~ sP0(X0,X1)
          | r2_hidden(X4,X0) )
    <=> ~ sP8(X4,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f86,plain,(
    ~ sP8(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),k6_relat_1(sK2)) ),
    inference(resolution,[],[f82,f50])).

fof(f50,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP8(X4,X1) ) ),
    inference(general_splitting,[],[f35,f49_D])).

fof(f35,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    r2_hidden(k4_tarski(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2))),k6_relat_1(sK2)) ),
    inference(global_subsumption,[],[f28,f80])).

fof(f80,plain,
    ( r2_hidden(k4_tarski(sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)),sK3(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2))),k6_relat_1(sK2))
    | r1_tarski(k6_relat_1(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(superposition,[],[f66,f78])).

%------------------------------------------------------------------------------
