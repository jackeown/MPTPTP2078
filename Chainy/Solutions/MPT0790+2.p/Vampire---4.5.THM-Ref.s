%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0790+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:48 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   21 (  40 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 119 expanded)
%              Number of equality atoms :   16 (  37 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1393,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1256,f1392])).

fof(f1392,plain,(
    ! [X2] : k1_wellord1(sK1,X2) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X2))) ),
    inference(subsumption_resolution,[],[f1391,f1254])).

fof(f1254,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f1228])).

fof(f1228,plain,
    ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f1182,f1227])).

fof(f1227,plain,
    ( ? [X0,X1] :
        ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0)))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f1182,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f1181])).

fof(f1181,plain,(
    ? [X0,X1] :
      ( k1_wellord1(X1,X0) != k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0)))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1175])).

fof(f1175,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    inference(negated_conjecture,[],[f1174])).

fof(f1174,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => k1_wellord1(X1,X0) = k3_relat_1(k2_wellord1(X1,k1_wellord1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_wellord1)).

fof(f1391,plain,(
    ! [X2] :
      ( k1_wellord1(sK1,X2) = k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,X2)))
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1385,f1298])).

fof(f1298,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1215])).

fof(f1215,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1150])).

fof(f1150,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_wellord1(X1,X0),k3_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_wellord1)).

fof(f1385,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK1))
      | k3_relat_1(k2_wellord1(sK1,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f1383,f1254])).

fof(f1383,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k3_relat_1(sK1))
      | k3_relat_1(k2_wellord1(sK1,X0)) = X0
      | ~ v1_relat_1(sK1) ) ),
    inference(resolution,[],[f1305,f1255])).

fof(f1255,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f1228])).

fof(f1305,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X1)
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1218])).

fof(f1218,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1217])).

fof(f1217,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_wellord1(X1,X0)) = X0
      | ~ r1_tarski(X0,k3_relat_1(X1))
      | ~ v2_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1173])).

fof(f1173,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ( r1_tarski(X0,k3_relat_1(X1))
          & v2_wellord1(X1) )
       => k3_relat_1(k2_wellord1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_wellord1)).

fof(f1256,plain,(
    k1_wellord1(sK1,sK0) != k3_relat_1(k2_wellord1(sK1,k1_wellord1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f1228])).
%------------------------------------------------------------------------------
