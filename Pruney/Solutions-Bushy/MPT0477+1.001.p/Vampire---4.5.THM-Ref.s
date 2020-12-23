%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0477+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:03 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 174 expanded)
%              Number of leaves         :    7 (  44 expanded)
%              Depth                    :   19
%              Number of atoms          :  211 (1035 expanded)
%              Number of equality atoms :   73 ( 316 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,(
    k6_relat_1(sK0) != k6_relat_1(sK0) ),
    inference(superposition,[],[f20,f117])).

% (16118)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f117,plain,(
    ! [X8] : k6_relat_1(X8) = k4_relat_1(k6_relat_1(X8)) ),
    inference(subsumption_resolution,[],[f113,f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK1(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X3))
      | r2_hidden(k4_tarski(sK1(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X2))
      | k6_relat_1(X3) = k4_relat_1(k6_relat_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK1(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X3))
      | r2_hidden(k4_tarski(sK1(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X2))
      | k6_relat_1(X3) = k4_relat_1(k6_relat_1(X2))
      | k6_relat_1(X3) = k4_relat_1(k6_relat_1(X2)) ) ),
    inference(superposition,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X3] :
      ( sK1(k6_relat_1(X2),k6_relat_1(X3)) = sK2(k6_relat_1(X2),k6_relat_1(X3))
      | k6_relat_1(X3) = k4_relat_1(k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | X4 = X5 ) ),
    inference(global_subsumption,[],[f21,f36])).

fof(f36,plain,(
    ! [X4,X0,X5] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X0,X5,X1] :
      ( X4 = X5
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | k6_relat_1(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
          | ( ( sK3(X0,X1) != sK4(X0,X1)
              | ~ r2_hidden(sK3(X0,X1),X0)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( ( sK3(X0,X1) = sK4(X0,X1)
                & r2_hidden(sK3(X0,X1),X0) )
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) )
        & ( ! [X4,X5] :
              ( ( r2_hidden(k4_tarski(X4,X5),X1)
                | X4 != X5
                | ~ r2_hidden(X4,X0) )
              & ( ( X4 = X5
                  & r2_hidden(X4,X0) )
                | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f17,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( X2 != X3
            | ~ r2_hidden(X2,X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( ( X2 = X3
              & r2_hidden(X2,X0) )
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( sK3(X0,X1) != sK4(X0,X1)
          | ~ r2_hidden(sK3(X0,X1),X0)
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( ( sK3(X0,X1) = sK4(X0,X1)
            & r2_hidden(sK3(X0,X1),X0) )
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
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
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
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
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ( k6_relat_1(X0) = X1
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
          | k6_relat_1(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_relat_1)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f68,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(sK2(k6_relat_1(X2),k6_relat_1(X3)),sK1(k6_relat_1(X2),k6_relat_1(X3))),k6_relat_1(X2))
      | k6_relat_1(X3) = k4_relat_1(k6_relat_1(X2))
      | sK1(k6_relat_1(X2),k6_relat_1(X3)) = sK2(k6_relat_1(X2),k6_relat_1(X3)) ) ),
    inference(resolution,[],[f66,f39])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK1(k6_relat_1(X0),k6_relat_1(X1)),sK2(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X1))
      | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),k6_relat_1(X1)),sK1(k6_relat_1(X0),k6_relat_1(X1))),k6_relat_1(X0))
      | k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X1) ) ),
    inference(resolution,[],[f53,f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(sK1(k6_relat_1(X0),X1),sK2(k6_relat_1(X0),X1)),X1)
      | r2_hidden(k4_tarski(sK2(k6_relat_1(X0),X1),sK1(k6_relat_1(X0),X1)),k6_relat_1(X0))
      | k4_relat_1(k6_relat_1(X0)) = X1 ) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | k4_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
                & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
                  | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f13])).

% (16118)Refutation not found, incomplete strategy% (16118)------------------------------
% (16118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16118)Termination reason: Refutation not found, incomplete strategy

% (16118)Memory used [KB]: 6012
% (16118)Time elapsed: 0.066 s
% (16118)------------------------------
% (16118)------------------------------
fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r2_hidden(k4_tarski(X3,X2),X0)
            | r2_hidden(k4_tarski(X2,X3),X1) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) )
        & ( r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
          | r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X4,X5] :
                  ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r2_hidden(k4_tarski(X5,X4),X0) )
                  & ( r2_hidden(k4_tarski(X5,X4),X0)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k4_relat_1(X0) = X1
              | ? [X2,X3] :
                  ( ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | r2_hidden(k4_tarski(X2,X3),X1) ) ) )
            & ( ! [X2,X3] :
                  ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r2_hidden(k4_tarski(X3,X2),X0) )
                  & ( r2_hidden(k4_tarski(X3,X2),X0)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | k4_relat_1(X0) != X1 ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( k4_relat_1(X0) = X1
          <=> ! [X2,X3] :
                ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r2_hidden(k4_tarski(X3,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_1)).

fof(f113,plain,(
    ! [X8] :
      ( k6_relat_1(X8) = k4_relat_1(k6_relat_1(X8))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X8),k6_relat_1(X8)),sK1(k6_relat_1(X8),k6_relat_1(X8))),k6_relat_1(X8)) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X8] :
      ( k6_relat_1(X8) = k4_relat_1(k6_relat_1(X8))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X8),k6_relat_1(X8)),sK1(k6_relat_1(X8),k6_relat_1(X8))),k6_relat_1(X8))
      | k6_relat_1(X8) = k4_relat_1(k6_relat_1(X8)) ) ),
    inference(resolution,[],[f82,f104])).

fof(f104,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK1(k6_relat_1(X0),k6_relat_1(X0)),sK1(k6_relat_1(X0),k6_relat_1(X0))),k6_relat_1(X0))
      | k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ) ),
    inference(factoring,[],[f79])).

fof(f82,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f81,f21])).

fof(f81,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(subsumption_resolution,[],[f78,f21])).

fof(f78,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4)) ) ),
    inference(duplicate_literal_removal,[],[f77])).

fof(f77,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4))
      | ~ r2_hidden(k4_tarski(sK1(k6_relat_1(X4),k6_relat_1(X5)),sK1(k6_relat_1(X4),k6_relat_1(X5))),k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X5))
      | ~ v1_relat_1(k6_relat_1(X4))
      | k6_relat_1(X5) = k4_relat_1(k6_relat_1(X4)) ) ),
    inference(superposition,[],[f25,f73])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK2(X0,X1),sK1(X0,X1)),X0)
      | k4_relat_1(X0) = X1
      | ~ r2_hidden(k4_tarski(sK1(X0,X1),sK2(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f20,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f9,plain,
    ( ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0))
   => k6_relat_1(sK0) != k4_relat_1(k6_relat_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : k6_relat_1(X0) != k4_relat_1(k6_relat_1(X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_relat_1)).

%------------------------------------------------------------------------------
