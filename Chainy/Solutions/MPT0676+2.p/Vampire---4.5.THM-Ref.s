%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0676+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:44 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   33 (  59 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   98 ( 184 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1419,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1418,f1387])).

fof(f1387,plain,(
    ! [X51] : v1_relat_1(k8_relat_1(X51,sK4)) ),
    inference(subsumption_resolution,[],[f1357,f1123])).

fof(f1123,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1076,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK2,sK4),sK3),k9_relat_1(sK4,sK3))
    & v1_funct_1(sK4)
    & v1_relat_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f987,f1075])).

fof(f1075,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK2,sK4),sK3),k9_relat_1(sK4,sK3))
      & v1_funct_1(sK4)
      & v1_relat_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f987,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f986])).

fof(f986,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f926])).

fof(f926,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f925])).

fof(f925,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_funct_1)).

fof(f1357,plain,(
    ! [X51] :
      ( v1_relat_1(k8_relat_1(X51,sK4))
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f1122,f1200])).

fof(f1200,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1043])).

fof(f1043,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1042])).

fof(f1042,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f910])).

fof(f910,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v1_funct_1(k8_relat_1(X0,X1))
        & v1_relat_1(k8_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_funct_1)).

fof(f1122,plain,(
    v1_relat_1(sK4) ),
    inference(cnf_transformation,[],[f1076])).

fof(f1418,plain,(
    ~ v1_relat_1(k8_relat_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1417,f1122])).

fof(f1417,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k8_relat_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1416,f1368])).

fof(f1368,plain,(
    ! [X68] : r1_tarski(k8_relat_1(X68,sK4),sK4) ),
    inference(resolution,[],[f1122,f1220])).

fof(f1220,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1061])).

fof(f1061,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f720])).

fof(f720,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

fof(f1416,plain,
    ( ~ r1_tarski(k8_relat_1(sK2,sK4),sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k8_relat_1(sK2,sK4)) ),
    inference(subsumption_resolution,[],[f1413,f1248])).

fof(f1248,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f1126])).

fof(f1126,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1078])).

fof(f1078,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1077])).

fof(f1077,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1413,plain,
    ( ~ r1_tarski(sK3,sK3)
    | ~ r1_tarski(k8_relat_1(sK2,sK4),sK4)
    | ~ v1_relat_1(sK4)
    | ~ v1_relat_1(k8_relat_1(sK2,sK4)) ),
    inference(resolution,[],[f1124,f1130])).

fof(f1130,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f993])).

fof(f993,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f992])).

fof(f992,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f761])).

fof(f761,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t158_relat_1)).

fof(f1124,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK2,sK4),sK3),k9_relat_1(sK4,sK3)) ),
    inference(cnf_transformation,[],[f1076])).
%------------------------------------------------------------------------------
