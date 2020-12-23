%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t48_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:27 EDT 2019

% Result     : Theorem 9.86s
% Output     : Refutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 105 expanded)
%              Number of leaves         :    3 (  25 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 245 expanded)
%              Number of equality atoms :   20 (  79 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1749,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1691,f1599])).

fof(f1599,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f1371,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t48_xboole_1.p',d4_xboole_0)).

fof(f1371,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f289,f86])).

fof(f86,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X3)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,X3)) ) ),
    inference(resolution,[],[f74,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f73,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t48_xboole_1.p',d5_xboole_0)).

fof(f26,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) != k3_xboole_0(X0,X1) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t48_xboole_1.p',t48_xboole_1)).

fof(f289,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1) ) ),
    inference(subsumption_resolution,[],[f112,f55])).

fof(f112,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),sK1) ) ),
    inference(resolution,[],[f56,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1691,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f1372,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f1372,plain,(
    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f172,f1371])).

fof(f172,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k3_xboole_0(sK0,sK1) != k3_xboole_0(sK0,sK1)
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f54,f74])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
