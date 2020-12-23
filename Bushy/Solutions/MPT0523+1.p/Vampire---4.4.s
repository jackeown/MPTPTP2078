%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t123_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:48 EDT 2019

% Result     : Theorem 18.92s
% Output     : Refutation 18.92s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 145 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :   19
%              Number of atoms          :  243 ( 773 expanded)
%              Number of equality atoms :   21 (  58 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83697,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f83696])).

fof(f83696,plain,(
    ! [X0] : k8_relat_1(X0,sK3) = k5_relat_1(sK3,k6_relat_1(X0)) ),
    inference(subsumption_resolution,[],[f83695,f54])).

fof(f54,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k8_relat_1(sK2,sK3) != k5_relat_1(sK3,k6_relat_1(sK2))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
        & v1_relat_1(X1) )
   => ( k8_relat_1(sK2,sK3) != k5_relat_1(sK3,k6_relat_1(sK2))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k8_relat_1(X0,X1) != k5_relat_1(X1,k6_relat_1(X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',t123_relat_1)).

fof(f83695,plain,(
    ! [X0] :
      ( k8_relat_1(X0,sK3) = k5_relat_1(sK3,k6_relat_1(X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f83693,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',dt_k6_relat_1)).

fof(f83693,plain,(
    ! [X0] :
      ( k8_relat_1(X0,sK3) = k5_relat_1(sK3,k6_relat_1(X0))
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f83692,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',dt_k5_relat_1)).

fof(f83692,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k5_relat_1(sK3,k6_relat_1(X2)))
      | k8_relat_1(X2,sK3) = k5_relat_1(sK3,k6_relat_1(X2)) ) ),
    inference(subsumption_resolution,[],[f83662,f54])).

fof(f83662,plain,(
    ! [X2] :
      ( k8_relat_1(X2,sK3) = k5_relat_1(sK3,k6_relat_1(X2))
      | ~ v1_relat_1(k5_relat_1(sK3,k6_relat_1(X2)))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f83658,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k8_relat_1(X1,X0) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( sP1(X2,X0,X1)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f24,f35,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ( r2_hidden(k4_tarski(X3,X4),X1)
            & r2_hidden(X4,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( k8_relat_1(X0,X1) = X2
      <=> sP0(X1,X0,X2) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',d12_relat_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k8_relat_1(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( k8_relat_1(X1,X2) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k8_relat_1(X1,X2) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ( ( k8_relat_1(X0,X1) = X2
          | ~ sP0(X1,X0,X2) )
        & ( sP0(X1,X0,X2)
          | k8_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f83658,plain,(
    ! [X13] : sP0(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13))) ),
    inference(subsumption_resolution,[],[f83647,f9485])).

fof(f9485,plain,(
    ! [X7] :
      ( r2_hidden(k4_tarski(sK7(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7))),sK8(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7)))),k5_relat_1(sK3,k6_relat_1(X7)))
      | sP0(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7))) ) ),
    inference(duplicate_literal_removal,[],[f9472])).

fof(f9472,plain,(
    ! [X7] :
      ( r2_hidden(k4_tarski(sK7(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7))),sK8(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7)))),k5_relat_1(sK3,k6_relat_1(X7)))
      | sP0(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7)))
      | r2_hidden(k4_tarski(sK7(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7))),sK8(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7)))),k5_relat_1(sK3,k6_relat_1(X7)))
      | sP0(sK3,X7,k5_relat_1(sK3,k6_relat_1(X7))) ) ),
    inference(resolution,[],[f2647,f4996])).

fof(f4996,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),X1)
      | sP0(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))) ) ),
    inference(factoring,[],[f1272])).

fof(f1272,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(sK8(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))),X19)
      | r2_hidden(sK8(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))),X18)
      | sP0(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))) ) ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ v1_relat_1(X25)
      | sP0(X23,X24,k5_relat_1(X25,k6_relat_1(X26)))
      | r2_hidden(sK8(X23,X24,k5_relat_1(X25,k6_relat_1(X26))),X26)
      | r2_hidden(sK8(X23,X24,k5_relat_1(X25,k6_relat_1(X26))),X24) ) ),
    inference(resolution,[],[f70,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X1,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X1,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2))) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t123_relat_1.p',t75_relat_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | r2_hidden(sK8(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
            | ~ r2_hidden(sK8(X0,X1,X2),X1)
            | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
              & r2_hidden(sK8(X0,X1,X2),X1) )
            | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X6,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X6,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X4,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X4,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
          | ~ r2_hidden(sK8(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
            & r2_hidden(sK8(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X4,X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X6,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X6,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f2647,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(sK8(sK3,X17,X18),X19)
      | r2_hidden(k4_tarski(sK7(sK3,X17,X18),sK8(sK3,X17,X18)),k5_relat_1(sK3,k6_relat_1(X19)))
      | sP0(sK3,X17,X18)
      | r2_hidden(k4_tarski(sK7(sK3,X17,X18),sK8(sK3,X17,X18)),X18) ) ),
    inference(resolution,[],[f320,f54])).

fof(f320,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),k5_relat_1(X0,k6_relat_1(X3)))
      | ~ r2_hidden(sK8(X0,X1,X2),X3)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ),
    inference(resolution,[],[f71,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | ~ r2_hidden(X1,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f83647,plain,(
    ! [X13] :
      ( sP0(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13)))
      | ~ r2_hidden(k4_tarski(sK7(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13))),sK8(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13)))),k5_relat_1(sK3,k6_relat_1(X13))) ) ),
    inference(duplicate_literal_removal,[],[f83645])).

fof(f83645,plain,(
    ! [X13] :
      ( sP0(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13)))
      | ~ r2_hidden(k4_tarski(sK7(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13))),sK8(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13)))),k5_relat_1(sK3,k6_relat_1(X13)))
      | sP0(sK3,X13,k5_relat_1(sK3,k6_relat_1(X13))) ) ),
    inference(resolution,[],[f5001,f13266])).

fof(f13266,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(sK3,X0,k5_relat_1(sK3,k6_relat_1(X1))),sK8(sK3,X0,k5_relat_1(sK3,k6_relat_1(X1)))),sK3)
      | sP0(sK3,X0,k5_relat_1(sK3,k6_relat_1(X1))) ) ),
    inference(factoring,[],[f3598])).

fof(f3598,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(k4_tarski(sK7(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))),sK8(X17,X18,k5_relat_1(sK3,k6_relat_1(X19)))),sK3)
      | r2_hidden(k4_tarski(sK7(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))),sK8(X17,X18,k5_relat_1(sK3,k6_relat_1(X19)))),X17)
      | sP0(X17,X18,k5_relat_1(sK3,k6_relat_1(X19))) ) ),
    inference(resolution,[],[f332,f54])).

fof(f332,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ v1_relat_1(X21)
      | sP0(X19,X20,k5_relat_1(X21,k6_relat_1(X22)))
      | r2_hidden(k4_tarski(sK7(X19,X20,k5_relat_1(X21,k6_relat_1(X22))),sK8(X19,X20,k5_relat_1(X21,k6_relat_1(X22)))),X21)
      | r2_hidden(k4_tarski(sK7(X19,X20,k5_relat_1(X21,k6_relat_1(X22))),sK8(X19,X20,k5_relat_1(X21,k6_relat_1(X22)))),X19) ) ),
    inference(resolution,[],[f71,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(X3,k6_relat_1(X2)))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5001,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),X0)
      | sP0(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),k5_relat_1(sK3,k6_relat_1(X1))) ) ),
    inference(subsumption_resolution,[],[f5000,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,X2),sK8(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f5000,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),X1)
      | sP0(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),X0)
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),k5_relat_1(sK3,k6_relat_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f4990])).

fof(f4990,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),X1)
      | sP0(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),X0)
      | sP0(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))
      | ~ r2_hidden(k4_tarski(sK7(X0,X1,k5_relat_1(sK3,k6_relat_1(X1))),sK8(X0,X1,k5_relat_1(sK3,k6_relat_1(X1)))),k5_relat_1(sK3,k6_relat_1(X1))) ) ),
    inference(resolution,[],[f1272,f72])).

fof(f55,plain,(
    k8_relat_1(sK2,sK3) != k5_relat_1(sK3,k6_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
