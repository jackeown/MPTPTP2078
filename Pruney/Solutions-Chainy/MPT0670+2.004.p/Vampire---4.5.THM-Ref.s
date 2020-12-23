%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  76 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   12
%              Number of atoms          :  276 ( 371 expanded)
%              Number of equality atoms :   39 (  62 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f118,f30])).

fof(f30,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2)
    & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0)
        & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2)
      & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0)
      & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
         => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))
       => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).

fof(f118,plain,(
    ~ v1_relat_1(sK4) ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f31,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f21])).

fof(f115,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f113,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( sP0(k8_relat_1(X0,X1),X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( sP0(k8_relat_1(X0,X1),X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f58,f34])).

fof(f34,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f57,f35])).

fof(f35,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_funct_1(k8_relat_1(X1,X0))
      | ~ v1_funct_1(k6_relat_1(X1))
      | ~ v1_relat_1(k6_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP0(k8_relat_1(X0,X1),X1,X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f53,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X0,X2,X1)
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f16,f18,f17])).

fof(f17,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ( ! [X3] :
            ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,k1_relat_1(X1)) )
        & ! [X4] :
            ( r2_hidden(X4,k1_relat_1(X1))
          <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
              & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X2,X1] :
      ( ( k8_relat_1(X0,X2) = X1
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) )
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X4),X0)
                    & r2_hidden(X4,k1_relat_1(X2)) ) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( ( v1_funct_1(X2)
            & v1_relat_1(X2) )
         => ( k8_relat_1(X0,X2) = X1
          <=> ( ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                 => k1_funct_1(X2,X3) = k1_funct_1(X1,X3) )
              & ! [X3] :
                  ( r2_hidden(X3,k1_relat_1(X1))
                <=> ( r2_hidden(k1_funct_1(X2,X3),X0)
                    & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1,k8_relat_1(X0,X1))
      | sP0(k8_relat_1(X0,X1),X1,X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k8_relat_1(X0,X1) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X0,X1) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f22])).

fof(f22,plain,(
    ! [X0,X2,X1] :
      ( ( ( k8_relat_1(X0,X2) = X1
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | k8_relat_1(X0,X2) != X1 ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f113,plain,(
    ! [X0] : ~ sP0(k8_relat_1(sK3,sK4),sK4,X0) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK4,sK2) != k1_funct_1(X0,sK2)
      | ~ sP0(k8_relat_1(sK3,sK4),X0,X1) ) ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f32,plain,(
    r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k1_funct_1(sK4,sK2) != k1_funct_1(X0,sK2)
      | ~ r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))
      | ~ sP0(k8_relat_1(sK3,sK4),X0,X1) ) ),
    inference(superposition,[],[f33,f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X1] :
      ( k1_funct_1(X1,X5) = k1_funct_1(X0,X5)
      | ~ r2_hidden(X5,k1_relat_1(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( k1_funct_1(X1,sK5(X0,X1)) != k1_funct_1(X0,sK5(X0,X1))
          & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) )
        | ( ( ~ r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2)
            | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))
            | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
          & ( ( r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2)
              & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) )
            | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X1,X5) = k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,k1_relat_1(X0)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X0))
                | ~ r2_hidden(k1_funct_1(X1,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X1)) )
              & ( ( r2_hidden(k1_funct_1(X1,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X1)) )
                | ~ r2_hidden(X6,k1_relat_1(X0)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
          & r2_hidden(X3,k1_relat_1(X0)) )
     => ( k1_funct_1(X1,sK5(X0,X1)) != k1_funct_1(X0,sK5(X0,X1))
        & r2_hidden(sK5(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X1,X4),X2)
            | ~ r2_hidden(X4,k1_relat_1(X1))
            | ~ r2_hidden(X4,k1_relat_1(X0)) )
          & ( ( r2_hidden(k1_funct_1(X1,X4),X2)
              & r2_hidden(X4,k1_relat_1(X1)) )
            | r2_hidden(X4,k1_relat_1(X0)) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2)
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))
          | ~ r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
        & ( ( r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) )
          | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( k1_funct_1(X1,X3) != k1_funct_1(X0,X3)
            & r2_hidden(X3,k1_relat_1(X0)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X1,X4),X2)
              | ~ r2_hidden(X4,k1_relat_1(X1))
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
            & ( ( r2_hidden(k1_funct_1(X1,X4),X2)
                & r2_hidden(X4,k1_relat_1(X1)) )
              | r2_hidden(X4,k1_relat_1(X0)) ) ) )
      & ( ( ! [X5] :
              ( k1_funct_1(X1,X5) = k1_funct_1(X0,X5)
              | ~ r2_hidden(X5,k1_relat_1(X0)) )
          & ! [X6] :
              ( ( r2_hidden(X6,k1_relat_1(X0))
                | ~ r2_hidden(k1_funct_1(X1,X6),X2)
                | ~ r2_hidden(X6,k1_relat_1(X1)) )
              & ( ( r2_hidden(k1_funct_1(X1,X6),X2)
                  & r2_hidden(X6,k1_relat_1(X1)) )
                | ~ r2_hidden(X6,k1_relat_1(X0)) ) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( k1_funct_1(X2,X3) != k1_funct_1(X1,X3)
            & r2_hidden(X3,k1_relat_1(X1)) )
        | ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X2,X4),X0)
              | ~ r2_hidden(X4,k1_relat_1(X2))
              | ~ r2_hidden(X4,k1_relat_1(X1)) )
            & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                & r2_hidden(X4,k1_relat_1(X2)) )
              | r2_hidden(X4,k1_relat_1(X1)) ) ) )
      & ( ( ! [X3] :
              ( k1_funct_1(X2,X3) = k1_funct_1(X1,X3)
              | ~ r2_hidden(X3,k1_relat_1(X1)) )
          & ! [X4] :
              ( ( r2_hidden(X4,k1_relat_1(X1))
                | ~ r2_hidden(k1_funct_1(X2,X4),X0)
                | ~ r2_hidden(X4,k1_relat_1(X2)) )
              & ( ( r2_hidden(k1_funct_1(X2,X4),X0)
                  & r2_hidden(X4,k1_relat_1(X2)) )
                | ~ r2_hidden(X4,k1_relat_1(X1)) ) ) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (31504)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.43  % (31504)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f119,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(subsumption_resolution,[],[f118,f30])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    v1_relat_1(sK4)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2) & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) & v1_funct_1(sK4) & v1_relat_1(sK4)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f10,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2)) => (k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2) & r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) & v1_funct_1(sK4) & v1_relat_1(sK4))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.43    inference(flattening,[],[f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((k1_funct_1(k8_relat_1(X1,X2),X0) != k1_funct_1(X2,X0) & r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.43    inference(negated_conjecture,[],[f6])).
% 0.22/0.43  fof(f6,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X0,k1_relat_1(k8_relat_1(X1,X2))) => k1_funct_1(k8_relat_1(X1,X2),X0) = k1_funct_1(X2,X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_funct_1)).
% 0.22/0.43  fof(f118,plain,(
% 0.22/0.43    ~v1_relat_1(sK4)),
% 0.22/0.43    inference(subsumption_resolution,[],[f115,f31])).
% 0.22/0.43  fof(f31,plain,(
% 0.22/0.43    v1_funct_1(sK4)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f115,plain,(
% 0.22/0.43    ~v1_funct_1(sK4) | ~v1_relat_1(sK4)),
% 0.22/0.43    inference(resolution,[],[f113,f62])).
% 0.22/0.43  fof(f62,plain,(
% 0.22/0.43    ( ! [X0,X1] : (sP0(k8_relat_1(X0,X1),X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f61,f36])).
% 0.22/0.43  fof(f36,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f11])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.22/0.43  fof(f61,plain,(
% 0.22/0.43    ( ! [X0,X1] : (sP0(k8_relat_1(X0,X1),X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f60,f59])).
% 0.22/0.43  fof(f59,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f58,f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,axiom,(
% 0.22/0.43    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.22/0.43  fof(f58,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f57,f35])).
% 0.22/0.43  fof(f35,plain,(
% 0.22/0.43    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f4])).
% 0.22/0.43  fof(f57,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f56])).
% 0.22/0.43  fof(f56,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_funct_1(k8_relat_1(X1,X0)) | ~v1_funct_1(k6_relat_1(X1)) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(superposition,[],[f39,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f12])).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(ennf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.22/0.43  fof(f39,plain,(
% 0.22/0.43    ( ! [X0,X1] : (v1_funct_1(k5_relat_1(X0,X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.43    inference(flattening,[],[f13])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.43    inference(ennf_transformation,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_funct_1)).
% 0.22/0.43  fof(f60,plain,(
% 0.22/0.43    ( ! [X0,X1] : (sP0(k8_relat_1(X0,X1),X1,X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(k8_relat_1(X0,X1)) | ~v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.22/0.43    inference(resolution,[],[f53,f52])).
% 0.22/0.43  fof(f52,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : (sP1(X0,X2,X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(definition_folding,[],[f16,f18,f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))),
% 0.22/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.43  fof(f18,plain,(
% 0.22/0.43    ! [X0,X2,X1] : ((k8_relat_1(X0,X2) = X1 <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.22/0.43    inference(flattening,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X2) = X1 <=> (! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2)))))) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X4] : (r2_hidden(X4,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))))))))),
% 0.22/0.43    inference(rectify,[],[f5])).
% 0.22/0.43  fof(f5,axiom,(
% 0.22/0.43    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (k8_relat_1(X0,X2) = X1 <=> (! [X3] : (r2_hidden(X3,k1_relat_1(X1)) => k1_funct_1(X2,X3) = k1_funct_1(X1,X3)) & ! [X3] : (r2_hidden(X3,k1_relat_1(X1)) <=> (r2_hidden(k1_funct_1(X2,X3),X0) & r2_hidden(X3,k1_relat_1(X2))))))))),
% 0.22/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_funct_1)).
% 0.22/0.43  fof(f53,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~sP1(X0,X1,k8_relat_1(X0,X1)) | sP0(k8_relat_1(X0,X1),X1,X0)) )),
% 0.22/0.43    inference(equality_resolution,[],[f40])).
% 0.22/0.43  fof(f40,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k8_relat_1(X0,X1) != X2 | ~sP1(X0,X1,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (((k8_relat_1(X0,X1) = X2 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k8_relat_1(X0,X1) != X2)) | ~sP1(X0,X1,X2))),
% 0.22/0.43    inference(rectify,[],[f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ! [X0,X2,X1] : (((k8_relat_1(X0,X2) = X1 | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | k8_relat_1(X0,X2) != X1)) | ~sP1(X0,X2,X1))),
% 0.22/0.43    inference(nnf_transformation,[],[f18])).
% 0.22/0.43  fof(f113,plain,(
% 0.22/0.43    ( ! [X0] : (~sP0(k8_relat_1(sK3,sK4),sK4,X0)) )),
% 0.22/0.43    inference(equality_resolution,[],[f105])).
% 0.22/0.43  fof(f105,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_funct_1(sK4,sK2) != k1_funct_1(X0,sK2) | ~sP0(k8_relat_1(sK3,sK4),X0,X1)) )),
% 0.22/0.43    inference(subsumption_resolution,[],[f98,f32])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4)))),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  fof(f98,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_funct_1(sK4,sK2) != k1_funct_1(X0,sK2) | ~r2_hidden(sK2,k1_relat_1(k8_relat_1(sK3,sK4))) | ~sP0(k8_relat_1(sK3,sK4),X0,X1)) )),
% 0.22/0.43    inference(superposition,[],[f33,f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    ( ! [X2,X0,X5,X1] : (k1_funct_1(X1,X5) = k1_funct_1(X0,X5) | ~r2_hidden(X5,k1_relat_1(X0)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (k1_funct_1(X1,sK5(X0,X1)) != k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))) | ((~r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))) & ((! [X5] : (k1_funct_1(X1,X5) = k1_funct_1(X0,X5) | ~r2_hidden(X5,k1_relat_1(X0))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X1,X6),X2) | ~r2_hidden(X6,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X6),X2) & r2_hidden(X6,k1_relat_1(X1))) | ~r2_hidden(X6,k1_relat_1(X0))))) | ~sP0(X0,X1,X2)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f26,f28,f27])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ! [X1,X0] : (? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,k1_relat_1(X0))) => (k1_funct_1(X1,sK5(X0,X1)) != k1_funct_1(X0,sK5(X0,X1)) & r2_hidden(sK5(X0,X1),k1_relat_1(X0))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    ! [X2,X1,X0] : (? [X4] : ((~r2_hidden(k1_funct_1(X1,X4),X2) | ~r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X1,X4),X2) & r2_hidden(X4,k1_relat_1(X1))) | r2_hidden(X4,k1_relat_1(X0)))) => ((~r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1)) | ~r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X1,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X1))) | r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)))))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (k1_funct_1(X1,X3) != k1_funct_1(X0,X3) & r2_hidden(X3,k1_relat_1(X0))) | ? [X4] : ((~r2_hidden(k1_funct_1(X1,X4),X2) | ~r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X1,X4),X2) & r2_hidden(X4,k1_relat_1(X1))) | r2_hidden(X4,k1_relat_1(X0))))) & ((! [X5] : (k1_funct_1(X1,X5) = k1_funct_1(X0,X5) | ~r2_hidden(X5,k1_relat_1(X0))) & ! [X6] : ((r2_hidden(X6,k1_relat_1(X0)) | ~r2_hidden(k1_funct_1(X1,X6),X2) | ~r2_hidden(X6,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X1,X6),X2) & r2_hidden(X6,k1_relat_1(X1))) | ~r2_hidden(X6,k1_relat_1(X0))))) | ~sP0(X0,X1,X2)))),
% 0.22/0.43    inference(rectify,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : ((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | ~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | ~sP0(X1,X2,X0)))),
% 0.22/0.43    inference(flattening,[],[f24])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | (? [X3] : (k1_funct_1(X2,X3) != k1_funct_1(X1,X3) & r2_hidden(X3,k1_relat_1(X1))) | ? [X4] : (((~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | r2_hidden(X4,k1_relat_1(X1)))))) & ((! [X3] : (k1_funct_1(X2,X3) = k1_funct_1(X1,X3) | ~r2_hidden(X3,k1_relat_1(X1))) & ! [X4] : ((r2_hidden(X4,k1_relat_1(X1)) | (~r2_hidden(k1_funct_1(X2,X4),X0) | ~r2_hidden(X4,k1_relat_1(X2)))) & ((r2_hidden(k1_funct_1(X2,X4),X0) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X4,k1_relat_1(X1))))) | ~sP0(X1,X2,X0)))),
% 0.22/0.43    inference(nnf_transformation,[],[f17])).
% 0.22/0.43  fof(f33,plain,(
% 0.22/0.43    k1_funct_1(k8_relat_1(sK3,sK4),sK2) != k1_funct_1(sK4,sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f21])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (31504)------------------------------
% 0.22/0.43  % (31504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (31504)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (31504)Memory used [KB]: 1663
% 0.22/0.43  % (31504)Time elapsed: 0.007 s
% 0.22/0.43  % (31504)------------------------------
% 0.22/0.43  % (31504)------------------------------
% 0.22/0.43  % (31485)Success in time 0.07 s
%------------------------------------------------------------------------------
