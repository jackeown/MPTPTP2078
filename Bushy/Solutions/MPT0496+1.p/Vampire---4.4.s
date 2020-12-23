%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t94_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:06 EDT 2019

% Result     : Theorem 19.46s
% Output     : Refutation 19.55s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 165 expanded)
%              Number of leaves         :    9 (  41 expanded)
%              Depth                    :   19
%              Number of atoms          :  247 ( 900 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :   12 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83634,plain,(
    $false ),
    inference(subsumption_resolution,[],[f55,f83633])).

fof(f83633,plain,(
    ! [X0] : k7_relat_1(sK3,X0) = k5_relat_1(k6_relat_1(X0),sK3) ),
    inference(subsumption_resolution,[],[f83632,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t94_relat_1.p',dt_k6_relat_1)).

fof(f83632,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k5_relat_1(k6_relat_1(X0),sK3)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(subsumption_resolution,[],[f83630,f54])).

fof(f54,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f37])).

fof(f37,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k5_relat_1(k6_relat_1(X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t94_relat_1.p',t94_relat_1)).

fof(f83630,plain,(
    ! [X0] :
      ( k7_relat_1(sK3,X0) = k5_relat_1(k6_relat_1(X0),sK3)
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(resolution,[],[f83629,f77])).

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
    file('/export/starexec/sandbox2/benchmark/relat_1__t94_relat_1.p',dt_k5_relat_1)).

fof(f83629,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),sK3))
      | k7_relat_1(sK3,X2) = k5_relat_1(k6_relat_1(X2),sK3) ) ),
    inference(subsumption_resolution,[],[f83599,f54])).

fof(f83599,plain,(
    ! [X2] :
      ( k7_relat_1(sK3,X2) = k5_relat_1(k6_relat_1(X2),sK3)
      | ~ v1_relat_1(k5_relat_1(k6_relat_1(X2),sK3))
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f83595,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k7_relat_1(X0,X1) = X2
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f64,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X2,X1,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f23,f35,f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X1,X2)
    <=> ! [X3,X4] :
          ( r2_hidden(k4_tarski(X3,X4),X2)
        <=> ( r2_hidden(k4_tarski(X3,X4),X0)
            & r2_hidden(X3,X1) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ( k7_relat_1(X0,X1) = X2
      <=> sP0(X0,X1,X2) )
      | ~ sP1(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t94_relat_1.p',d11_relat_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | k7_relat_1(X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( k7_relat_1(X2,X1) = X0
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k7_relat_1(X2,X1) != X0 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ( ( k7_relat_1(X0,X1) = X2
          | ~ sP0(X0,X1,X2) )
        & ( sP0(X0,X1,X2)
          | k7_relat_1(X0,X1) != X2 ) )
      | ~ sP1(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f83595,plain,(
    ! [X13] : sP0(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3)) ),
    inference(subsumption_resolution,[],[f83584,f9488])).

fof(f9488,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X5),sK3))
      | sP0(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))
      | r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X6),sK3)) ) ),
    inference(subsumption_resolution,[],[f9480,f2647])).

fof(f2647,plain,(
    ! [X19,X17,X18] :
      ( ~ r2_hidden(sK6(sK3,X17,X18),X19)
      | r2_hidden(k4_tarski(sK6(sK3,X17,X18),sK7(sK3,X17,X18)),k5_relat_1(k6_relat_1(X19),sK3))
      | sP0(sK3,X17,X18)
      | r2_hidden(k4_tarski(sK6(sK3,X17,X18),sK7(sK3,X17,X18)),X18) ) ),
    inference(resolution,[],[f320,f54])).

fof(f320,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP0(X0,X1,X2)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),k5_relat_1(k6_relat_1(X3),X0))
      | ~ r2_hidden(sK6(X0,X1,X2),X3)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ),
    inference(resolution,[],[f69,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | ~ r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
          | ~ r2_hidden(k4_tarski(X0,X1),X3)
          | ~ r2_hidden(X0,X2) )
        & ( ( r2_hidden(k4_tarski(X0,X1),X3)
            & r2_hidden(X0,X2) )
          | ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t94_relat_1.p',t74_relat_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
          & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X5,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X5,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3,X4] :
          ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(k4_tarski(X3,X4),X2) )
          & ( ( r2_hidden(k4_tarski(X3,X4),X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(k4_tarski(X3,X4),X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) )
        & ( ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X5,X6] :
            ( ( r2_hidden(k4_tarski(X5,X6),X2)
              | ~ r2_hidden(k4_tarski(X5,X6),X0)
              | ~ r2_hidden(X5,X1) )
            & ( ( r2_hidden(k4_tarski(X5,X6),X0)
                & r2_hidden(X5,X1) )
              | ~ r2_hidden(k4_tarski(X5,X6),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X3,X1) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X3,X1) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3,X4] :
            ( ( ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X4),X2) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(k4_tarski(X3,X4),X2) ) ) )
      & ( ! [X3,X4] :
            ( ( r2_hidden(k4_tarski(X3,X4),X2)
              | ~ r2_hidden(k4_tarski(X3,X4),X0)
              | ~ r2_hidden(X3,X1) )
            & ( ( r2_hidden(k4_tarski(X3,X4),X0)
                & r2_hidden(X3,X1) )
              | ~ r2_hidden(k4_tarski(X3,X4),X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f9480,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X5),sK3))
      | sP0(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))
      | r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X6),sK3))
      | r2_hidden(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),X6) ) ),
    inference(duplicate_literal_removal,[],[f9465])).

fof(f9465,plain,(
    ! [X6,X5] :
      ( r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X5),sK3))
      | sP0(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))
      | r2_hidden(k4_tarski(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),sK7(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3))),k5_relat_1(k6_relat_1(X6),sK3))
      | r2_hidden(sK6(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)),X6)
      | sP0(sK3,X5,k5_relat_1(k6_relat_1(X6),sK3)) ) ),
    inference(resolution,[],[f2647,f1272])).

fof(f1272,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(sK6(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)),X19)
      | r2_hidden(sK6(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)),X18)
      | sP0(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)) ) ),
    inference(resolution,[],[f103,f54])).

fof(f103,plain,(
    ! [X26,X24,X23,X25] :
      ( ~ v1_relat_1(X26)
      | sP0(X23,X24,k5_relat_1(k6_relat_1(X25),X26))
      | r2_hidden(sK6(X23,X24,k5_relat_1(k6_relat_1(X25),X26)),X25)
      | r2_hidden(sK6(X23,X24,k5_relat_1(k6_relat_1(X25),X26)),X24) ) ),
    inference(resolution,[],[f68,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(X0,X2)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f83584,plain,(
    ! [X13] :
      ( sP0(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3))
      | ~ r2_hidden(k4_tarski(sK6(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3)),sK7(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3))),k5_relat_1(k6_relat_1(X13),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f83582])).

fof(f83582,plain,(
    ! [X13] :
      ( sP0(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3))
      | ~ r2_hidden(k4_tarski(sK6(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3)),sK7(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3))),k5_relat_1(k6_relat_1(X13),sK3))
      | sP0(sK3,X13,k5_relat_1(k6_relat_1(X13),sK3)) ) ),
    inference(resolution,[],[f4999,f13260])).

fof(f13260,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK6(sK3,X0,k5_relat_1(k6_relat_1(X1),sK3)),sK7(sK3,X0,k5_relat_1(k6_relat_1(X1),sK3))),sK3)
      | sP0(sK3,X0,k5_relat_1(k6_relat_1(X1),sK3)) ) ),
    inference(factoring,[],[f3598])).

fof(f3598,plain,(
    ! [X19,X17,X18] :
      ( r2_hidden(k4_tarski(sK6(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)),sK7(X17,X18,k5_relat_1(k6_relat_1(X19),sK3))),sK3)
      | r2_hidden(k4_tarski(sK6(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)),sK7(X17,X18,k5_relat_1(k6_relat_1(X19),sK3))),X17)
      | sP0(X17,X18,k5_relat_1(k6_relat_1(X19),sK3)) ) ),
    inference(resolution,[],[f332,f54])).

fof(f332,plain,(
    ! [X21,X19,X22,X20] :
      ( ~ v1_relat_1(X22)
      | sP0(X19,X20,k5_relat_1(k6_relat_1(X21),X22))
      | r2_hidden(k4_tarski(sK6(X19,X20,k5_relat_1(k6_relat_1(X21),X22)),sK7(X19,X20,k5_relat_1(k6_relat_1(X21),X22))),X22)
      | r2_hidden(k4_tarski(sK6(X19,X20,k5_relat_1(k6_relat_1(X21),X22)),sK7(X19,X20,k5_relat_1(k6_relat_1(X21),X22))),X19) ) ),
    inference(resolution,[],[f69,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      | r2_hidden(k4_tarski(X0,X1),X3)
      | ~ v1_relat_1(X3) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4999,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),X0)
      | sP0(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),k5_relat_1(k6_relat_1(X1),sK3)) ) ),
    inference(subsumption_resolution,[],[f4998,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X0)
      | sP0(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,X2),sK7(X0,X1,X2)),X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f4998,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),X1)
      | sP0(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),X0)
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),k5_relat_1(k6_relat_1(X1),sK3)) ) ),
    inference(duplicate_literal_removal,[],[f4988])).

fof(f4988,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),X1)
      | sP0(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),X0)
      | sP0(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))
      | ~ r2_hidden(k4_tarski(sK6(X0,X1,k5_relat_1(k6_relat_1(X1),sK3)),sK7(X0,X1,k5_relat_1(k6_relat_1(X1),sK3))),k5_relat_1(k6_relat_1(X1),sK3)) ) ),
    inference(resolution,[],[f1272,f70])).

fof(f55,plain,(
    k7_relat_1(sK3,sK2) != k5_relat_1(k6_relat_1(sK2),sK3) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
