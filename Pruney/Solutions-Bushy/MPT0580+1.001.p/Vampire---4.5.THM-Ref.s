%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0580+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:15 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 606 expanded)
%              Number of leaves         :    8 ( 153 expanded)
%              Depth                    :   24
%              Number of atoms          :  218 (3057 expanded)
%              Number of equality atoms :   66 ( 798 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f94])).

fof(f94,plain,(
    k1_xboole_0 != sK1 ),
    inference(subsumption_resolution,[],[f27,f92])).

fof(f92,plain,(
    v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f90,f24])).

fof(f24,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ( ( k1_xboole_0 != sK1
        & r2_hidden(sK1,k2_relat_1(sK0)) )
      | ~ v3_relat_1(sK0) )
    & ( ! [X2] :
          ( k1_xboole_0 = X2
          | ~ r2_hidden(X2,k2_relat_1(sK0)) )
      | v3_relat_1(sK0) )
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f13,f12])).

fof(f12,plain,
    ( ? [X0] :
        ( ( ? [X1] :
              ( k1_xboole_0 != X1
              & r2_hidden(X1,k2_relat_1(X0)) )
          | ~ v3_relat_1(X0) )
        & ( ! [X2] :
              ( k1_xboole_0 = X2
              | ~ r2_hidden(X2,k2_relat_1(X0)) )
          | v3_relat_1(X0) )
        & v1_relat_1(X0) )
   => ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(sK0)) )
        | ~ v3_relat_1(sK0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(sK0)) )
        | v3_relat_1(sK0) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X1] :
        ( k1_xboole_0 != X1
        & r2_hidden(X1,k2_relat_1(sK0)) )
   => ( k1_xboole_0 != sK1
      & r2_hidden(sK1,k2_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X2] :
            ( k1_xboole_0 = X2
            | ~ r2_hidden(X2,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ( ? [X1] :
            ( k1_xboole_0 != X1
            & r2_hidden(X1,k2_relat_1(X0)) )
        | ~ v3_relat_1(X0) )
      & ( ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
        | v3_relat_1(X0) )
      & v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ( v3_relat_1(X0)
      <~> ! [X1] :
            ( k1_xboole_0 = X1
            | ~ r2_hidden(X1,k2_relat_1(X0)) ) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ( v3_relat_1(X0)
        <=> ! [X1] :
              ( r2_hidden(X1,k2_relat_1(X0))
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> ! [X1] :
            ( r2_hidden(X1,k2_relat_1(X0))
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t184_relat_1)).

fof(f90,plain,
    ( v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f89,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( ( v3_relat_1(X0)
          | ~ r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
        & ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
          | ~ v3_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v3_relat_1(X0)
      <=> r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_relat_1)).

fof(f89,plain,(
    r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f38,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f87,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | r1_tarski(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    inference(superposition,[],[f36,f86])).

fof(f86,plain,(
    k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f85,f54])).

fof(f54,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f53,f24])).

fof(f53,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(sK0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( v3_relat_1(sK0)
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | v3_relat_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f45,f33])).

fof(f45,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK0),X0)
      | v3_relat_1(sK0)
      | k1_xboole_0 = sK3(k2_relat_1(sK0),X0) ) ),
    inference(resolution,[],[f25,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f25,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = X2
      | v3_relat_1(sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,
    ( k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | ~ v3_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f82,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f54,f27])).

fof(f82,plain,
    ( k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
    | k1_xboole_0 = sK1
    | ~ v3_relat_1(sK0) ),
    inference(resolution,[],[f79,f26])).

fof(f26,plain,
    ( r2_hidden(sK1,k2_relat_1(sK0))
    | ~ v3_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(sK0))
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(sK0))
      | ~ v1_relat_1(sK0)
      | k1_xboole_0 = sK3(k2_relat_1(sK0),k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f49,f54])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ v3_relat_1(X3)
      | r2_hidden(X2,k1_tarski(k1_xboole_0))
      | ~ r2_hidden(X2,k2_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k1_tarski(k1_xboole_0))
      | ~ v3_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f27,plain,
    ( ~ v3_relat_1(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f102,plain,(
    k1_xboole_0 = sK1 ),
    inference(resolution,[],[f99,f93])).

fof(f93,plain,(
    r2_hidden(sK1,k2_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f26,f92])).

fof(f99,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k2_relat_1(sK0))
      | k1_xboole_0 = X2 ) ),
    inference(resolution,[],[f91,f39])).

fof(f91,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(k1_xboole_0))
      | ~ r2_hidden(X0,k2_relat_1(sK0)) ) ),
    inference(resolution,[],[f89,f34])).

%------------------------------------------------------------------------------
