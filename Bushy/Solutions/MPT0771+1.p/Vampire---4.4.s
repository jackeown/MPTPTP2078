%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t20_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:11 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 111 expanded)
%              Number of leaves         :    5 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 388 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f395,plain,(
    $false ),
    inference(subsumption_resolution,[],[f391,f365])).

fof(f365,plain,(
    r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    inference(resolution,[],[f362,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',d3_tarski)).

fof(f362,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    inference(subsumption_resolution,[],[f361,f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f56,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f56,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f46])).

fof(f46,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',t20_wellord1)).

fof(f361,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f352,f55])).

fof(f55,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f352,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f76,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k3_relat_1(X2))
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t20_wellord1.p',t19_wellord1)).

fof(f76,plain,
    ( r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)),k3_relat_1(k2_wellord1(sK1,sK0)))
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    inference(resolution,[],[f56,f60])).

fof(f391,plain,(
    ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),k3_relat_1(k2_wellord1(sK1,sK0))) ),
    inference(resolution,[],[f366,f75])).

fof(f75,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,X4)
      | ~ r2_hidden(X3,k3_relat_1(k2_wellord1(sK1,X4))) ) ),
    inference(resolution,[],[f55,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f366,plain,(
    ~ r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,sK0)),sK0),sK0) ),
    inference(resolution,[],[f362,f61])).
%------------------------------------------------------------------------------
