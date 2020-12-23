%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0560+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:37 EST 2020

% Result     : Theorem 3.64s
% Output     : Refutation 3.64s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 104 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :   71 ( 280 expanded)
%              Number of equality atoms :   31 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4316,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4298,f2249])).

fof(f2249,plain,(
    k9_relat_1(sK0,sK1) = k9_relat_1(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(forward_demodulation,[],[f2224,f1062])).

fof(f1062,plain,(
    ! [X7] : k9_relat_1(sK0,X7) = k2_relat_1(k7_relat_1(sK0,X7)) ),
    inference(resolution,[],[f960,f902])).

fof(f902,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f880])).

fof(f880,plain,
    ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f814,f879,f878])).

fof(f878,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
            & r1_tarski(X1,X2) )
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f879,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X1) != k9_relat_1(k7_relat_1(sK0,X2),X1)
        & r1_tarski(X1,X2) )
   => ( k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1)
      & r1_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f814,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X1) != k9_relat_1(k7_relat_1(X0,X2),X1)
          & r1_tarski(X1,X2) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f746])).

fof(f746,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1,X2] :
            ( r1_tarski(X1,X2)
           => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    inference(negated_conjecture,[],[f745])).

fof(f745,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f960,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f868])).

fof(f868,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f2224,plain,(
    k9_relat_1(sK0,k3_xboole_0(sK2,sK1)) = k2_relat_1(k7_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f1062,f1604])).

fof(f1604,plain,(
    k7_relat_1(sK0,sK1) = k7_relat_1(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(resolution,[],[f1178,f903])).

fof(f903,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f880])).

fof(f1178,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k7_relat_1(sK0,X10) = k7_relat_1(sK0,k3_xboole_0(X11,X10)) ) ),
    inference(forward_demodulation,[],[f1177,f1150])).

fof(f1150,plain,(
    ! [X10,X11] : k7_relat_1(k7_relat_1(sK0,X10),X11) = k7_relat_1(sK0,k3_xboole_0(X10,X11)) ),
    inference(resolution,[],[f914,f902])).

fof(f914,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f826])).

fof(f826,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f684])).

fof(f684,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f1177,plain,(
    ! [X10,X11] :
      ( ~ r1_tarski(X10,X11)
      | k7_relat_1(sK0,X10) = k7_relat_1(k7_relat_1(sK0,X11),X10) ) ),
    inference(resolution,[],[f909,f902])).

fof(f909,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1)
      | k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f819])).

fof(f819,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f818])).

fof(f818,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f687])).

fof(f687,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f4298,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(sK0,k3_xboole_0(sK2,sK1)) ),
    inference(superposition,[],[f904,f1839])).

fof(f1839,plain,(
    ! [X10,X11] : k9_relat_1(k7_relat_1(sK0,X10),X11) = k9_relat_1(sK0,k3_xboole_0(X10,X11)) ),
    inference(forward_demodulation,[],[f1838,f1062])).

fof(f1838,plain,(
    ! [X10,X11] : k9_relat_1(k7_relat_1(sK0,X10),X11) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(X10,X11))) ),
    inference(forward_demodulation,[],[f1834,f1150])).

fof(f1834,plain,(
    ! [X10,X11] : k9_relat_1(k7_relat_1(sK0,X10),X11) = k2_relat_1(k7_relat_1(k7_relat_1(sK0,X10),X11)) ),
    inference(resolution,[],[f1061,f902])).

fof(f1061,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_relat_1(X4)
      | k9_relat_1(k7_relat_1(X4,X5),X6) = k2_relat_1(k7_relat_1(k7_relat_1(X4,X5),X6)) ) ),
    inference(resolution,[],[f960,f934])).

fof(f934,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f848])).

fof(f848,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f904,plain,(
    k9_relat_1(sK0,sK1) != k9_relat_1(k7_relat_1(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f880])).
%------------------------------------------------------------------------------
