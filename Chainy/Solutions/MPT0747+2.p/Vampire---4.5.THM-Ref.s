%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0747+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:47 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   28 (  59 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 191 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1233,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1232,f1198])).

fof(f1198,plain,(
    r2_hidden(sK2(sK0),sK0) ),
    inference(resolution,[],[f1142,f1182])).

fof(f1182,plain,(
    v3_ordinal1(sK2(sK0)) ),
    inference(subsumption_resolution,[],[f1175,f1146])).

fof(f1146,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1127,plain,(
    ! [X0] :
      ( ( r1_tarski(X0,sK2(X0))
        & v3_ordinal1(sK2(X0)) )
      | ( ~ v3_ordinal1(sK3(X0))
        & r2_hidden(sK3(X0),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f1104,f1126,f1125])).

fof(f1125,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
     => ( r1_tarski(X0,sK2(X0))
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1126,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
     => ( ~ v3_ordinal1(sK3(X0))
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1104,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r1_tarski(X0,X1)
          & v3_ordinal1(X1) )
      | ? [X2] :
          ( ~ v3_ordinal1(X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1099])).

fof(f1099,plain,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X2] :
            ( r2_hidden(X2,X0)
           => v3_ordinal1(X2) ) ) ),
    inference(rectify,[],[f1091])).

fof(f1091,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ( v3_ordinal1(X1)
           => ~ r1_tarski(X0,X1) )
        & ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_ordinal1)).

fof(f1175,plain,
    ( v3_ordinal1(sK3(sK0))
    | v3_ordinal1(sK2(sK0)) ),
    inference(resolution,[],[f1141,f1145])).

fof(f1145,plain,(
    ! [X0] :
      ( v3_ordinal1(sK2(X0))
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1141,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f1122])).

fof(f1122,plain,(
    ! [X1] :
      ( ( r2_hidden(X1,sK0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,sK0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f1120,f1121])).

fof(f1121,plain,
    ( ? [X0] :
      ! [X1] :
        ( ( r2_hidden(X1,X0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) )
   => ! [X1] :
        ( ( r2_hidden(X1,sK0)
          | ~ v3_ordinal1(X1) )
        & ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1120,plain,(
    ? [X0] :
    ! [X1] :
      ( ( r2_hidden(X1,X0)
        | ~ v3_ordinal1(X1) )
      & ( v3_ordinal1(X1)
        | ~ r2_hidden(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f1101])).

fof(f1101,plain,(
    ? [X0] :
    ! [X1] :
      ( r2_hidden(X1,X0)
    <=> v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1093])).

fof(f1093,negated_conjecture,(
    ~ ! [X0] :
        ~ ! [X1] :
            ( r2_hidden(X1,X0)
          <=> v3_ordinal1(X1) ) ),
    inference(negated_conjecture,[],[f1092])).

fof(f1092,conjecture,(
    ! [X0] :
      ~ ! [X1] :
          ( r2_hidden(X1,X0)
        <=> v3_ordinal1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_ordinal1)).

fof(f1142,plain,(
    ! [X1] :
      ( ~ v3_ordinal1(X1)
      | r2_hidden(X1,sK0) ) ),
    inference(cnf_transformation,[],[f1122])).

fof(f1232,plain,(
    ~ r2_hidden(sK2(sK0),sK0) ),
    inference(resolution,[],[f1183,f1162])).

fof(f1162,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1116])).

fof(f1116,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1098])).

fof(f1098,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f1183,plain,(
    r1_tarski(sK0,sK2(sK0)) ),
    inference(subsumption_resolution,[],[f1176,f1148])).

fof(f1148,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2(X0))
      | ~ v3_ordinal1(sK3(X0)) ) ),
    inference(cnf_transformation,[],[f1127])).

fof(f1176,plain,
    ( v3_ordinal1(sK3(sK0))
    | r1_tarski(sK0,sK2(sK0)) ),
    inference(resolution,[],[f1141,f1147])).

fof(f1147,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2(X0))
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f1127])).
%------------------------------------------------------------------------------
