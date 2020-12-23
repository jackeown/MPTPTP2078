%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0771+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   30 (  64 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :   89 ( 226 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1303,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1294,f1302])).

fof(f1302,plain,(
    ! [X3] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X3)),k3_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f1300])).

fof(f1300,plain,(
    ! [X3] :
      ( r1_tarski(k3_relat_1(k2_wellord1(sK1,X3)),k3_relat_1(sK1))
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X3)),k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f1274,f1196])).

fof(f1196,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1183,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1181,f1182])).

fof(f1182,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1181,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1180])).

fof(f1180,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1163])).

fof(f1163,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1274,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,X0)),X1),k3_relat_1(sK1))
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f1238,f1190])).

fof(f1190,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1179])).

fof(f1179,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1159,f1178])).

fof(f1178,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1159,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1154])).

fof(f1154,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f1153])).

fof(f1153,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f1238,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(k3_relat_1(k2_wellord1(X0,X1)),X2),k3_relat_1(X0))
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f1212,f1195])).

fof(f1195,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1183])).

fof(f1212,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,k3_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1173])).

fof(f1173,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1172])).

fof(f1172,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1152])).

fof(f1152,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_wellord1)).

fof(f1294,plain,(
    ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f1191,f1293])).

fof(f1293,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ),
    inference(duplicate_literal_removal,[],[f1284])).

fof(f1284,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ) ),
    inference(resolution,[],[f1268,f1196])).

fof(f1268,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(k3_relat_1(k2_wellord1(sK1,X0)),X1),X0)
      | r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X1) ) ),
    inference(resolution,[],[f1229,f1190])).

fof(f1229,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK2(k3_relat_1(k2_wellord1(X0,X1)),X2),X1)
      | r1_tarski(k3_relat_1(k2_wellord1(X0,X1)),X2) ) ),
    inference(resolution,[],[f1213,f1195])).

fof(f1213,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1173])).

fof(f1191,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f1179])).
%------------------------------------------------------------------------------
