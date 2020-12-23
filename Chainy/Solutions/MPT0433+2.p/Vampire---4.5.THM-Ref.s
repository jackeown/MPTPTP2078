%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0433+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:30 EST 2020

% Result     : Theorem 8.94s
% Output     : Refutation 8.94s
% Verified   : 
% Statistics : Number of formulae       :   41 (  79 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 187 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10969,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f3022,f1533,f4382,f2144])).

fof(f2144,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f982])).

fof(f982,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f981])).

fof(f981,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f4382,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(X0,sK32)),k1_relat_1(sK32)) ),
    inference(superposition,[],[f3379,f1659])).

fof(f1659,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f3379,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(sK32,X0)),k1_relat_1(sK32)) ),
    inference(superposition,[],[f1648,f2824])).

fof(f2824,plain,(
    ! [X1] : k1_relat_1(sK32) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK32,X1)),k1_relat_1(sK32)) ),
    inference(forward_demodulation,[],[f2823,f1663])).

fof(f1663,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f2823,plain,(
    ! [X1] : k2_xboole_0(k1_relat_1(k3_xboole_0(sK32,X1)),k1_relat_1(sK32)) = k1_relat_1(k2_xboole_0(sK32,k3_xboole_0(sK32,X1))) ),
    inference(forward_demodulation,[],[f2814,f1661])).

fof(f1661,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f2814,plain,(
    ! [X1] : k1_relat_1(k2_xboole_0(k3_xboole_0(sK32,X1),sK32)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK32,X1)),k1_relat_1(sK32)) ),
    inference(resolution,[],[f2703,f2702])).

fof(f2702,plain,(
    ! [X1] : v1_relat_1(k3_xboole_0(sK32,X1)) ),
    inference(resolution,[],[f1532,f1736])).

fof(f1736,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f706])).

fof(f706,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f1532,plain,(
    v1_relat_1(sK32) ),
    inference(cnf_transformation,[],[f1142])).

fof(f1142,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK31,sK32)),k3_xboole_0(k1_relat_1(sK31),k1_relat_1(sK32)))
    & v1_relat_1(sK32)
    & v1_relat_1(sK31) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31,sK32])],[f659,f1141,f1140])).

fof(f1140,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK31,X1)),k3_xboole_0(k1_relat_1(sK31),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f1141,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK31,X1)),k3_xboole_0(k1_relat_1(sK31),k1_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k1_relat_1(k3_xboole_0(sK31,sK32)),k3_xboole_0(k1_relat_1(sK31),k1_relat_1(sK32)))
      & v1_relat_1(sK32) ) ),
    introduced(choice_axiom,[])).

fof(f659,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f646])).

fof(f646,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f645])).

fof(f645,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

fof(f2703,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k2_xboole_0(X2,sK32)) = k2_xboole_0(k1_relat_1(X2),k1_relat_1(sK32)) ) ),
    inference(resolution,[],[f1532,f1599])).

fof(f1599,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f674])).

fof(f674,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f644])).

fof(f644,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

fof(f1648,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1533,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0(sK31,sK32)),k3_xboole_0(k1_relat_1(sK31),k1_relat_1(sK32))) ),
    inference(cnf_transformation,[],[f1142])).

fof(f3022,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k3_xboole_0(sK31,X0)),k1_relat_1(sK31)) ),
    inference(superposition,[],[f1648,f2789])).

fof(f2789,plain,(
    ! [X0] : k1_relat_1(sK31) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK31,X0)),k1_relat_1(sK31)) ),
    inference(forward_demodulation,[],[f2788,f1663])).

fof(f2788,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k3_xboole_0(sK31,X0)),k1_relat_1(sK31)) = k1_relat_1(k2_xboole_0(sK31,k3_xboole_0(sK31,X0))) ),
    inference(forward_demodulation,[],[f2779,f1661])).

fof(f2779,plain,(
    ! [X0] : k1_relat_1(k2_xboole_0(k3_xboole_0(sK31,X0),sK31)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK31,X0)),k1_relat_1(sK31)) ),
    inference(resolution,[],[f2700,f2699])).

fof(f2699,plain,(
    ! [X1] : v1_relat_1(k3_xboole_0(sK31,X1)) ),
    inference(resolution,[],[f1531,f1736])).

fof(f1531,plain,(
    v1_relat_1(sK31) ),
    inference(cnf_transformation,[],[f1142])).

fof(f2700,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | k1_relat_1(k2_xboole_0(X2,sK31)) = k2_xboole_0(k1_relat_1(X2),k1_relat_1(sK31)) ) ),
    inference(resolution,[],[f1531,f1599])).
%------------------------------------------------------------------------------
