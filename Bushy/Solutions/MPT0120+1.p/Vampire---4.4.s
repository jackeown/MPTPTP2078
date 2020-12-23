%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t113_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:21 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :    8 (  10 expanded)
%              Number of leaves         :    2 (   3 expanded)
%              Depth                    :    5
%              Number of atoms          :    8 (  10 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t113_xboole_1.p',t4_xboole_1)).

fof(f32,plain,(
    k2_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(superposition,[],[f9,f12])).

fof(f9,plain,(
    k2_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) != k2_xboole_0(sK0,k2_xboole_0(k2_xboole_0(sK1,sK2),sK3)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) != k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_xboole_0(X0,k2_xboole_0(k2_xboole_0(X1,X2),X3)) = k2_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t113_xboole_1.p',t113_xboole_1)).
%------------------------------------------------------------------------------
