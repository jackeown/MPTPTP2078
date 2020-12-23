%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0559+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  46 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :   77 ( 115 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1116,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1115,f1045])).

fof(f1045,plain,(
    ! [X59] : v1_relat_1(k7_relat_1(sK2,X59)) ),
    inference(resolution,[],[f897,f959])).

fof(f959,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f870])).

fof(f870,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f897,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f875])).

fof(f875,plain,
    ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f813,f874])).

fof(f874,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f813,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f745])).

fof(f745,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f744])).

fof(f744,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k9_relat_1(k7_relat_1(X2,X0),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_relat_1)).

fof(f1115,plain,(
    ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1114,f897])).

fof(f1114,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1113,f1044])).

fof(f1044,plain,(
    ! [X58] : r1_tarski(k7_relat_1(sK2,X58),sK2) ),
    inference(resolution,[],[f897,f958])).

fof(f958,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f869])).

fof(f869,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f801])).

fof(f801,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f1113,plain,
    ( ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f1110,f970])).

fof(f970,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f877])).

fof(f877,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f876])).

fof(f876,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1110,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(k7_relat_1(sK2,sK0),sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0)) ),
    inference(resolution,[],[f898,f903])).

fof(f903,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f817])).

fof(f817,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f816])).

fof(f816,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f740])).

fof(f740,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f898,plain,(
    ~ r1_tarski(k9_relat_1(k7_relat_1(sK2,sK0),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f875])).
%------------------------------------------------------------------------------
