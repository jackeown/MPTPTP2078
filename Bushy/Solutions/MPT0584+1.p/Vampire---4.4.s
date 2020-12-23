%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t188_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:56 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  44 expanded)
%              Number of leaves         :    4 (   9 expanded)
%              Depth                    :   10
%              Number of atoms          :   47 ( 133 expanded)
%              Number of equality atoms :   25 (  60 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f207,f21])).

fof(f21,plain,(
    k7_relat_1(sK0,sK2) != k7_relat_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( k7_relat_1(X0,X2) != k7_relat_1(X1,X2)
              & k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
              & r1_tarski(X2,X3) )
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ! [X2,X3] :
                ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                  & r1_tarski(X2,X3) )
               => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2,X3] :
              ( ( k7_relat_1(X0,X3) = k7_relat_1(X1,X3)
                & r1_tarski(X2,X3) )
             => k7_relat_1(X0,X2) = k7_relat_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t188_relat_1.p',t188_relat_1)).

fof(f207,plain,(
    k7_relat_1(sK0,sK2) = k7_relat_1(sK1,sK2) ),
    inference(superposition,[],[f153,f34])).

fof(f34,plain,(
    k3_xboole_0(sK2,sK3) = sK2 ),
    inference(resolution,[],[f28,f19])).

fof(f19,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t188_relat_1.p',t28_xboole_1)).

fof(f153,plain,(
    ! [X0] : k7_relat_1(sK0,k3_xboole_0(X0,sK3)) = k7_relat_1(sK1,k3_xboole_0(X0,sK3)) ),
    inference(superposition,[],[f50,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t188_relat_1.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    ! [X0] : k7_relat_1(sK0,k3_xboole_0(sK3,X0)) = k7_relat_1(sK1,k3_xboole_0(sK3,X0)) ),
    inference(forward_demodulation,[],[f48,f43])).

fof(f43,plain,(
    ! [X2,X3] : k7_relat_1(k7_relat_1(sK0,X2),X3) = k7_relat_1(sK0,k3_xboole_0(X2,X3)) ),
    inference(resolution,[],[f31,f23])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t188_relat_1.p',t100_relat_1)).

fof(f48,plain,(
    ! [X0] : k7_relat_1(k7_relat_1(sK0,sK3),X0) = k7_relat_1(sK1,k3_xboole_0(sK3,X0)) ),
    inference(superposition,[],[f42,f20])).

fof(f20,plain,(
    k7_relat_1(sK0,sK3) = k7_relat_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] : k7_relat_1(k7_relat_1(sK1,X0),X1) = k7_relat_1(sK1,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f31,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
