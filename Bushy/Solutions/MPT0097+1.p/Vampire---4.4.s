%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t90_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:35 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   15 (  18 expanded)
%              Number of leaves         :    4 (   5 expanded)
%              Depth                    :    7
%              Number of atoms          :   18 (  24 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21,f15])).

fof(f15,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t90_xboole_1.p',t79_xboole_1)).

fof(f21,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(resolution,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t90_xboole_1.p',symmetry_r1_xboole_0)).

fof(f20,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f19,f17])).

fof(f17,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t90_xboole_1.p',t47_xboole_1)).

fof(f19,plain,(
    ~ r1_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f18,f13])).

fof(f13,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t90_xboole_1.p',t90_xboole_1)).
%------------------------------------------------------------------------------
