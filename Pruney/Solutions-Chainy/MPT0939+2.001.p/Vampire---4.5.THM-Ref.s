%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 247 expanded)
%              Number of leaves         :   12 (  58 expanded)
%              Depth                    :   22
%              Number of atoms          :  368 (1647 expanded)
%              Number of equality atoms :   37 ( 282 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f128,plain,(
    $false ),
    inference(subsumption_resolution,[],[f127,f37])).

fof(f37,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ v6_relat_2(k1_wellord2(sK0))
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ~ v6_relat_2(k1_wellord2(X0))
        & v3_ordinal1(X0) )
   => ( ~ v6_relat_2(k1_wellord2(sK0))
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v6_relat_2(k1_wellord2(X0))
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => v6_relat_2(k1_wellord2(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v6_relat_2(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).

fof(f127,plain,(
    ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ~ v6_relat_2(k1_wellord2(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f111,plain,(
    ! [X0] :
      ( v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(subsumption_resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f71,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f71,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f70,plain,(
    ! [X0] :
      ( r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f41,f68])).

fof(f68,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f65,f39])).

fof(f65,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f34])).

fof(f34,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

% (10057)Refutation not found, incomplete strategy% (10057)------------------------------
% (10057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
            & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
            & sK1(X0) != sK2(X0)
            & r2_hidden(sK2(X0),k3_relat_1(X0))
            & r2_hidden(sK1(X0),k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).

% (10057)Termination reason: Refutation not found, incomplete strategy

% (10057)Memory used [KB]: 10490
% (10057)Time elapsed: 0.071 s
% (10057)------------------------------
% (10057)------------------------------
fof(f29,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( ~ r2_hidden(k4_tarski(X2,X1),X0)
          & ~ r2_hidden(k4_tarski(X1,X2),X0)
          & X1 != X2
          & r2_hidden(X2,k3_relat_1(X0))
          & r2_hidden(X1,k3_relat_1(X0)) )
     => ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
        & ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
        & sK1(X0) != sK2(X0)
        & r2_hidden(sK2(X0),k3_relat_1(X0))
        & r2_hidden(sK1(X0),k3_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( r2_hidden(k4_tarski(X4,X3),X0)
              | r2_hidden(k4_tarski(X3,X4),X0)
              | X3 = X4
              | ~ r2_hidden(X4,k3_relat_1(X0))
              | ~ r2_hidden(X3,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v6_relat_2(X0)
          | ? [X1,X2] :
              ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( r2_hidden(k4_tarski(X2,X1),X0)
              | r2_hidden(k4_tarski(X1,X2),X0)
              | X1 = X2
              | ~ r2_hidden(X2,k3_relat_1(X0))
              | ~ r2_hidden(X1,k3_relat_1(X0)) )
          | ~ v6_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ( r2_hidden(k4_tarski(X2,X1),X0)
            | r2_hidden(k4_tarski(X1,X2),X0)
            | X1 = X2
            | ~ r2_hidden(X2,k3_relat_1(X0))
            | ~ r2_hidden(X1,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v6_relat_2(X0)
      <=> ! [X1,X2] :
            ~ ( ~ r2_hidden(k4_tarski(X2,X1),X0)
              & ~ r2_hidden(k4_tarski(X1,X2),X0)
              & X1 != X2
              & r2_hidden(X2,k3_relat_1(X0))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).

fof(f110,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f106,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f75,f56])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f74,f39])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(superposition,[],[f42,f68])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),k3_relat_1(X0))
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f106,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f105,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f105,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_ordinal1(sK1(k1_wellord2(X0))) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(sK2(k1_wellord2(X0)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0))
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_ordinal1(sK1(k1_wellord2(X0))) ) ),
    inference(resolution,[],[f94,f97])).

fof(f97,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1)))
      | v6_relat_2(k1_wellord2(X1))
      | ~ v1_ordinal1(sK1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f93,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ r2_hidden(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f93,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1)))
      | v6_relat_2(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f92,f75])).

fof(f92,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1)))
      | ~ r2_hidden(sK2(k1_wellord2(X1)),X1)
      | v6_relat_2(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f91,f71])).

fof(f91,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1)))
      | ~ r2_hidden(sK1(k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK2(k1_wellord2(X1)),X1)
      | v6_relat_2(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f86,f39])).

fof(f86,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1)))
      | ~ r2_hidden(sK1(k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK2(k1_wellord2(X1)),X1)
      | v6_relat_2(k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(subsumption_resolution,[],[f63,f39])).

fof(f63,plain,(
    ! [X4,X0,X5] :
      ( r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_wellord2(X0)),sK1(k1_wellord2(X0)))
      | ~ v3_ordinal1(sK2(k1_wellord2(X0)))
      | ~ v3_ordinal1(sK1(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f90,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f57,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f90,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f89,f71])).

fof(f89,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f88,f75])).

fof(f88,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | ~ r2_hidden(sK2(k1_wellord2(X0)),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0)) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0)))
      | ~ r2_hidden(sK2(k1_wellord2(X0)),X0)
      | ~ r2_hidden(sK1(k1_wellord2(X0)),X0)
      | v6_relat_2(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0)
      | v6_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10074)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (10066)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (10070)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (10062)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10069)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (10057)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (10074)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v3_ordinal1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~v6_relat_2(k1_wellord2(sK0)) & v3_ordinal1(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ? [X0] : (~v6_relat_2(k1_wellord2(X0)) & v3_ordinal1(X0)) => (~v6_relat_2(k1_wellord2(sK0)) & v3_ordinal1(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ? [X0] : (~v6_relat_2(k1_wellord2(X0)) & v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v3_ordinal1(X0) => v6_relat_2(k1_wellord2(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => v6_relat_2(k1_wellord2(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_wellord2)).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~v3_ordinal1(sK0)),
% 0.21/0.48    inference(resolution,[],[f111,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v6_relat_2(k1_wellord2(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X0] : (v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X0] : (v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f71,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_ordinal1(X0) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1))),
% 0.21/0.48    inference(flattening,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : ((v3_ordinal1(X0) | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => v3_ordinal1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(superposition,[],[f41,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f39])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(equality_resolution,[],[f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(rectify,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.48  % (10057)Refutation not found, incomplete strategy% (10057)------------------------------
% 0.21/0.48  % (10057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK1(X0),k3_relat_1(X0)) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0] : (((v6_relat_2(X0) | (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f28,f29])).
% 0.21/0.48  % (10057)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10057)Memory used [KB]: 10490
% 0.21/0.48  % (10057)Time elapsed: 0.071 s
% 0.21/0.48  % (10057)------------------------------
% 0.21/0.48  % (10057)------------------------------
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0] : (? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0))) => (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) & ~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) & sK1(X0) != sK2(X0) & r2_hidden(sK2(X0),k3_relat_1(X0)) & r2_hidden(sK1(X0),k3_relat_1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X3,X4] : (r2_hidden(k4_tarski(X4,X3),X0) | r2_hidden(k4_tarski(X3,X4),X0) | X3 = X4 | ~r2_hidden(X4,k3_relat_1(X0)) | ~r2_hidden(X3,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (((v6_relat_2(X0) | ? [X1,X2] : (~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))) & (! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v6_relat_2(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : ((v6_relat_2(X0) <=> ! [X1,X2] : (r2_hidden(k4_tarski(X2,X1),X0) | r2_hidden(k4_tarski(X1,X2),X0) | X1 = X2 | ~r2_hidden(X2,k3_relat_1(X0)) | ~r2_hidden(X1,k3_relat_1(X0)))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (v6_relat_2(X0) <=> ! [X1,X2] : ~(~r2_hidden(k4_tarski(X2,X1),X0) & ~r2_hidden(k4_tarski(X1,X2),X0) & X1 != X2 & r2_hidden(X2,k3_relat_1(X0)) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l4_wellord1)).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f107])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f106,f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X0] : (v3_ordinal1(sK2(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(resolution,[],[f75,f56])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f74,f39])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.48    inference(superposition,[],[f42,f68])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(X0),k3_relat_1(X0)) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(sK2(k1_wellord2(X0))) | ~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f105,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 0.21/0.48    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(sK2(k1_wellord2(X0))) | ~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | ~v1_ordinal1(sK1(k1_wellord2(X0)))) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_ordinal1(sK2(k1_wellord2(X0))) | ~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0)) | v6_relat_2(k1_wellord2(X0)) | ~v1_ordinal1(sK1(k1_wellord2(X0)))) )),
% 0.21/0.48    inference(resolution,[],[f94,f97])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X1] : (~r2_hidden(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1))) | v6_relat_2(k1_wellord2(X1)) | ~v1_ordinal1(sK1(k1_wellord2(X1)))) )),
% 0.21/0.48    inference(resolution,[],[f93,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0) | ~v1_ordinal1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(X1,X0) | ~r2_hidden(X1,X0)) | ~v1_ordinal1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    inference(unused_predicate_definition_removal,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_ordinal1(X0) <=> ! [X1] : (r2_hidden(X1,X0) => r1_tarski(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1))) | v6_relat_2(k1_wellord2(X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f75])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1))) | ~r2_hidden(sK2(k1_wellord2(X1)),X1) | v6_relat_2(k1_wellord2(X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f71])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X1] : (~r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1))) | ~r2_hidden(sK1(k1_wellord2(X1)),X1) | ~r2_hidden(sK2(k1_wellord2(X1)),X1) | v6_relat_2(k1_wellord2(X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f39])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ( ! [X1] : (~r1_tarski(sK2(k1_wellord2(X1)),sK1(k1_wellord2(X1))) | ~r2_hidden(sK1(k1_wellord2(X1)),X1) | ~r2_hidden(sK2(k1_wellord2(X1)),X1) | v6_relat_2(k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.21/0.49    inference(resolution,[],[f66,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(X0),sK1(X0)),X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f39])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X4,X0,X5] : (r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X4,X0,X5,X1] : (r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f35])).
% 0.21/0.49  fof(f94,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK2(k1_wellord2(X0)),sK1(k1_wellord2(X0))) | ~v3_ordinal1(sK2(k1_wellord2(X0))) | ~v3_ordinal1(sK1(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.49    inference(resolution,[],[f90,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f57,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f71])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f75])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | ~r2_hidden(sK2(k1_wellord2(X0)),X0) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f85,f39])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1(k1_wellord2(X0)),sK2(k1_wellord2(X0))) | ~r2_hidden(sK2(k1_wellord2(X0)),X0) | ~r2_hidden(sK1(k1_wellord2(X0)),X0) | v6_relat_2(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.49    inference(resolution,[],[f66,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK1(X0),sK2(X0)),X0) | v6_relat_2(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f30])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10074)------------------------------
% 0.21/0.49  % (10074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10074)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10074)Memory used [KB]: 1663
% 0.21/0.49  % (10074)Time elapsed: 0.070 s
% 0.21/0.49  % (10074)------------------------------
% 0.21/0.49  % (10074)------------------------------
% 0.21/0.49  % (10055)Success in time 0.124 s
%------------------------------------------------------------------------------
