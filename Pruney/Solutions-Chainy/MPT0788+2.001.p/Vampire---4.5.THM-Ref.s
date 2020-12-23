%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 245 expanded)
%              Number of leaves         :    6 (  48 expanded)
%              Depth                    :   20
%              Number of atoms          :  306 (1975 expanded)
%              Number of equality atoms :   70 ( 387 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(subsumption_resolution,[],[f95,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f95,plain,(
    ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))
    | sK0 != sK0 ),
    inference(superposition,[],[f28,f84])).

fof(f84,plain,(
    sK0 = sK1 ),
    inference(subsumption_resolution,[],[f83,f64])).

fof(f64,plain,(
    ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f63,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),sK2)
      | ~ r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f42,f23])).

fof(f23,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
        & sK0 != sK1 )
      | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
      | sK0 = sK1
      | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
    & r2_hidden(sK1,k3_relat_1(sK2))
    & r2_hidden(sK0,k3_relat_1(sK2))
    & v2_wellord1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
            & X0 != X1 )
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1
          | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2))
        & v2_wellord1(X2)
        & v1_relat_1(X2) )
   => ( ( ( ~ r2_hidden(sK0,k1_wellord1(sK2,sK1))
          & sK0 != sK1 )
        | ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & ( r2_hidden(sK0,k1_wellord1(sK2,sK1))
        | sK0 = sK1
        | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) )
      & r2_hidden(sK1,k3_relat_1(sK2))
      & r2_hidden(sK0,k3_relat_1(sK2))
      & v2_wellord1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ( ~ r2_hidden(X0,k1_wellord1(X2,X1))
          & X0 != X1 )
        | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & ( r2_hidden(X0,k1_wellord1(X2,X1))
        | X0 = X1
        | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      <~> ( r2_hidden(X0,k1_wellord1(X2,X1))
          | X0 = X1 ) )
      & r2_hidden(X1,k3_relat_1(X2))
      & r2_hidden(X0,k3_relat_1(X2))
      & v2_wellord1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r2_hidden(X1,k3_relat_1(X2))
            & r2_hidden(X0,k3_relat_1(X2))
            & v2_wellord1(X2) )
         => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
              | X0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
        <=> ( r2_hidden(X0,k1_wellord1(X2,X1))
            | X0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).

fof(f42,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                | sK3(X0,X1,X2) = X1
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
                  & sK3(X0,X1,X2) != X1 )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
          | sK3(X0,X1,X2) = X1
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0)
            & sK3(X0,X1,X2) != X1 )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f63,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f62,f23])).

fof(f62,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f61,f24])).

fof(f24,plain,(
    v2_wellord1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f60,f25])).

fof(f25,plain,(
    r2_hidden(sK0,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f60,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f26,plain,(
    r2_hidden(sK1,k3_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | ~ r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
        & ( r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) )
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2))
          & v2_wellord1(X2) )
       => ( r2_hidden(k4_tarski(X0,X1),X2)
        <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).

fof(f83,plain,
    ( sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f78,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK2)
      | X0 = X1
      | r2_hidden(X0,k1_wellord1(sK2,X1)) ) ),
    inference(resolution,[],[f41,f23])).

fof(f41,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | r2_hidden(X4,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k4_tarski(X4,X1),X0)
      | X1 = X4
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f78,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1 ),
    inference(subsumption_resolution,[],[f77,f64])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f76,f23])).

fof(f76,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f75,f24])).

fof(f75,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f74,f25])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(subsumption_resolution,[],[f69,f26])).

fof(f69,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),sK2)
    | ~ r2_hidden(sK1,k3_relat_1(sK2))
    | ~ r2_hidden(sK0,k3_relat_1(sK2))
    | ~ v2_wellord1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(resolution,[],[f40,f27])).

fof(f27,plain,
    ( r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | sK0 = sK1
    | r2_hidden(sK0,k1_wellord1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(X2))
      | ~ v2_wellord1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,
    ( ~ r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))
    | sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (3077)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.49  % (3069)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.49  % (3068)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.49  % (3060)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.49  % (3067)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3072)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (3060)Refutation not found, incomplete strategy% (3060)------------------------------
% 0.21/0.49  % (3060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3060)Memory used [KB]: 1663
% 0.21/0.49  % (3060)Time elapsed: 0.077 s
% 0.21/0.49  % (3060)------------------------------
% 0.21/0.49  % (3060)------------------------------
% 0.21/0.49  % (3069)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.49    inference(equality_resolution,[],[f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.49    inference(nnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0))),
% 0.21/0.49    inference(trivial_inequality_removal,[],[f89])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK0)) | sK0 != sK0),
% 0.21/0.49    inference(superposition,[],[f28,f84])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    sK0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f83,f64])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK2) | ~r2_hidden(X0,k1_wellord1(sK2,X1))) )),
% 0.21/0.49    inference(resolution,[],[f42,f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ((~r2_hidden(sK0,k1_wellord1(sK2,sK1)) & sK0 != sK1) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & (r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2)) => (((~r2_hidden(sK0,k1_wellord1(sK2,sK1)) & sK0 != sK1) | ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & (r2_hidden(sK0,k1_wellord1(sK2,sK1)) | sK0 = sK1 | r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1))) & r2_hidden(sK1,k3_relat_1(sK2)) & r2_hidden(sK0,k3_relat_1(sK2)) & v2_wellord1(sK2) & v1_relat_1(sK2))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1 | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((((~r2_hidden(X0,k1_wellord1(X2,X1)) & X0 != X1) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & ((r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1) | r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1,X2] : ((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2) & v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1,X2] : (((r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <~> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1)) & (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2))) & v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) <=> (r2_hidden(X0,k1_wellord1(X2,X1)) | X0 = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_wellord1)).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) | sK3(X0,X1,X2) = X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK3(X0,X1,X2),X1),X0) & sK3(X0,X1,X2) != X1) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(rectify,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(flattening,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f62,f23])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f61,f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    v2_wellord1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f60,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    r2_hidden(sK0,k3_relat_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f57,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    r2_hidden(sK1,k3_relat_1(sK2))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ~r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(resolution,[],[f39,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | ~r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) & (r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(nnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1))) | (~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)) & v2_wellord1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_wellord1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    sK0 = sK1 | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(resolution,[],[f78,f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK2) | X0 = X1 | r2_hidden(X0,k1_wellord1(sK2,X1))) )),
% 0.21/0.49    inference(resolution,[],[f41,f23])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X4,X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | r2_hidden(X4,k1_wellord1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4 | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f64])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f23])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v1_relat_1(sK2) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f24])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f25])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f69,f26])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK0,sK1),sK2) | ~r2_hidden(sK1,k3_relat_1(sK2)) | ~r2_hidden(sK0,k3_relat_1(sK2)) | ~v2_wellord1(sK2) | ~v1_relat_1(sK2) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(resolution,[],[f40,f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | sK0 = sK1 | r2_hidden(sK0,k1_wellord1(sK2,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k1_wellord1(X2,X0),k1_wellord1(X2,X1)) | r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k3_relat_1(X2)) | ~r2_hidden(X0,k3_relat_1(X2)) | ~v2_wellord1(X2) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~r1_tarski(k1_wellord1(sK2,sK0),k1_wellord1(sK2,sK1)) | sK0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3069)------------------------------
% 0.21/0.49  % (3069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3069)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3069)Memory used [KB]: 1663
% 0.21/0.49  % (3069)Time elapsed: 0.087 s
% 0.21/0.49  % (3069)------------------------------
% 0.21/0.49  % (3069)------------------------------
% 0.21/0.49  % (3059)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (3052)Success in time 0.132 s
%------------------------------------------------------------------------------
