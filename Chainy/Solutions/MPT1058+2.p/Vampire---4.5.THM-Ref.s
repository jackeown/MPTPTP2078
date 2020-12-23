%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1058+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:04 EST 2020

% Result     : Theorem 7.58s
% Output     : Refutation 7.58s
% Verified   : 
% Statistics : Number of formulae       :   23 (  37 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 ( 118 expanded)
%              Number of equality atoms :   22 (  40 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13172,plain,(
    $false ),
    inference(subsumption_resolution,[],[f13151,f12000])).

fof(f12000,plain,(
    k10_relat_1(sK38,sK40) = k3_xboole_0(sK39,k10_relat_1(sK38,sK40)) ),
    inference(superposition,[],[f5850,f4777])).

fof(f4777,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f5850,plain,(
    k10_relat_1(sK38,sK40) = k3_xboole_0(k10_relat_1(sK38,sK40),sK39) ),
    inference(resolution,[],[f3584,f3851])).

fof(f3851,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1908])).

fof(f1908,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f3584,plain,(
    r1_tarski(k10_relat_1(sK38,sK40),sK39) ),
    inference(cnf_transformation,[],[f2806])).

fof(f2806,plain,
    ( k10_relat_1(sK38,sK40) != k10_relat_1(k7_relat_1(sK38,sK39),sK40)
    & r1_tarski(k10_relat_1(sK38,sK40),sK39)
    & v1_funct_1(sK38)
    & v1_relat_1(sK38) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK38,sK39,sK40])],[f1673,f2805,f2804])).

fof(f2804,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(k10_relat_1(X0,X2),X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k10_relat_1(sK38,X2) != k10_relat_1(k7_relat_1(sK38,X1),X2)
          & r1_tarski(k10_relat_1(sK38,X2),X1) )
      & v1_funct_1(sK38)
      & v1_relat_1(sK38) ) ),
    introduced(choice_axiom,[])).

fof(f2805,plain,
    ( ? [X2,X1] :
        ( k10_relat_1(sK38,X2) != k10_relat_1(k7_relat_1(sK38,X1),X2)
        & r1_tarski(k10_relat_1(sK38,X2),X1) )
   => ( k10_relat_1(sK38,sK40) != k10_relat_1(k7_relat_1(sK38,sK39),sK40)
      & r1_tarski(k10_relat_1(sK38,sK40),sK39) ) ),
    introduced(choice_axiom,[])).

fof(f1673,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f1672])).

fof(f1672,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k10_relat_1(X0,X2) != k10_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(k10_relat_1(X0,X2),X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1586])).

fof(f1586,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(k10_relat_1(X0,X2),X1)
           => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f1585])).

fof(f1585,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(k10_relat_1(X0,X2),X1)
         => k10_relat_1(X0,X2) = k10_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(f13151,plain,(
    k10_relat_1(sK38,sK40) != k3_xboole_0(sK39,k10_relat_1(sK38,sK40)) ),
    inference(superposition,[],[f3585,f5569])).

fof(f5569,plain,(
    ! [X10,X11] : k10_relat_1(k7_relat_1(sK38,X10),X11) = k3_xboole_0(X10,k10_relat_1(sK38,X11)) ),
    inference(resolution,[],[f3582,f3647])).

fof(f3647,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f1729])).

fof(f1729,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f959])).

fof(f959,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(k7_relat_1(X2,X0),X1) = k3_xboole_0(X0,k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(f3582,plain,(
    v1_relat_1(sK38) ),
    inference(cnf_transformation,[],[f2806])).

fof(f3585,plain,(
    k10_relat_1(sK38,sK40) != k10_relat_1(k7_relat_1(sK38,sK39),sK40) ),
    inference(cnf_transformation,[],[f2806])).
%------------------------------------------------------------------------------
