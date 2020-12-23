%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t34_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:01 EDT 2019

% Result     : Theorem 104.27s
% Output     : Refutation 104.27s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 376 expanded)
%              Number of leaves         :   15 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          :  350 (1675 expanded)
%              Number of equality atoms :   34 ( 150 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f25208,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25083,f23296])).

fof(f23296,plain,(
    ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f466,f23170])).

fof(f23170,plain,(
    r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f23037,f125])).

fof(f125,plain,(
    r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f67,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f52,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',d3_tarski)).

fof(f67,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f37,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
     => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,sK1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(sK1)))
        & v1_relat_1(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',t34_relat_1)).

fof(f23037,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f22910,f21571])).

fof(f21571,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k1_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X13,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f11331,f79])).

fof(f79,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',idempotence_k3_xboole_0)).

fof(f11331,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X1))))
      | r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f1319,f661])).

fof(f661,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(k1_relat_1(sK0),X6))
      | r2_hidden(X5,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f152,f97])).

fof(f97,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',d4_xboole_0)).

fof(f152,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK0))
      | r2_hidden(X4,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f99,f106])).

fof(f106,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f65,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',d6_relat_1)).

fof(f65,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f99,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',d3_xboole_0)).

fof(f1319,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(k1_relat_1(sK0),k1_relat_1(k3_xboole_0(sK1,X1))))
      | ~ r2_hidden(X0,k1_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X1)))) ) ),
    inference(resolution,[],[f191,f68])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f191,plain,(
    ! [X5] : r1_tarski(k1_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X5))),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(k3_xboole_0(sK1,X5)))) ),
    inference(resolution,[],[f101,f111])).

fof(f111,plain,(
    ! [X4] : v1_relat_1(k3_xboole_0(sK1,X4)) ),
    inference(resolution,[],[f66,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',fc1_relat_1)).

fof(f66,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k3_xboole_0(sK0,X0)),k3_xboole_0(k1_relat_1(sK0),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f65,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',t14_relat_1)).

fof(f22910,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK0))
      | ~ r2_hidden(X0,k3_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X0,k1_relat_1(k3_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f22832,f961])).

fof(f961,plain,(
    ! [X14,X13] :
      ( r2_hidden(X14,k2_relat_1(k3_xboole_0(sK0,X13)))
      | ~ r2_hidden(X14,k3_relat_1(k3_xboole_0(sK0,X13)))
      | r2_hidden(X14,k1_relat_1(k3_xboole_0(sK0,X13))) ) ),
    inference(superposition,[],[f100,f118])).

fof(f118,plain,(
    ! [X10] : k3_relat_1(k3_xboole_0(sK0,X10)) = k2_xboole_0(k1_relat_1(k3_xboole_0(sK0,X10)),k2_relat_1(k3_xboole_0(sK0,X10))) ),
    inference(resolution,[],[f105,f71])).

fof(f105,plain,(
    ! [X4] : v1_relat_1(k3_xboole_0(sK0,X4)) ),
    inference(resolution,[],[f65,f80])).

fof(f100,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f22832,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k2_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X13,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f11565,f79])).

fof(f11565,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X1))))
      | r2_hidden(X0,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f1355,f638])).

fof(f638,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(k2_relat_1(sK0),X6))
      | r2_hidden(X5,k3_relat_1(sK0)) ) ),
    inference(resolution,[],[f151,f97])).

fof(f151,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK0))
      | r2_hidden(X3,k3_relat_1(sK0)) ) ),
    inference(superposition,[],[f98,f106])).

fof(f98,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1355,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(k2_relat_1(sK0),k2_relat_1(k3_xboole_0(sK1,X1))))
      | ~ r2_hidden(X0,k2_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X1)))) ) ),
    inference(resolution,[],[f245,f68])).

fof(f245,plain,(
    ! [X7] : r1_tarski(k2_relat_1(k3_xboole_0(sK0,k3_xboole_0(sK1,X7))),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(k3_xboole_0(sK1,X7)))) ),
    inference(resolution,[],[f103,f111])).

fof(f103,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k2_relat_1(k3_xboole_0(sK0,X2)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(X2))) ) ),
    inference(resolution,[],[f65,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',t27_relat_1)).

fof(f466,plain,
    ( ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1))
    | ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK0)) ),
    inference(resolution,[],[f126,f95])).

fof(f95,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f126,plain,(
    ~ r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(resolution,[],[f67,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f25083,plain,(
    r2_hidden(sK2(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))),k3_relat_1(sK1)) ),
    inference(resolution,[],[f24992,f125])).

fof(f24992,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X0,k3_relat_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f24866,f23770])).

fof(f23770,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k1_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X13,k3_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f23756,f78])).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t34_relat_1.p',commutativity_k3_xboole_0)).

fof(f23756,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k1_relat_1(k3_xboole_0(sK1,sK0)))
      | r2_hidden(X13,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f11682,f79])).

fof(f11682,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X1))))
      | r2_hidden(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f1374,f694])).

fof(f694,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(k1_relat_1(sK1),X6))
      | r2_hidden(X5,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f173,f97])).

fof(f173,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k1_relat_1(sK1))
      | r2_hidden(X4,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f99,f112])).

fof(f112,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f66,f71])).

fof(f1374,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k3_xboole_0(sK0,X1))))
      | ~ r2_hidden(X0,k1_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X1)))) ) ),
    inference(resolution,[],[f306,f68])).

fof(f306,plain,(
    ! [X8] : r1_tarski(k1_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X8))),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(k3_xboole_0(sK0,X8)))) ),
    inference(resolution,[],[f107,f105])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(k1_relat_1(k3_xboole_0(sK1,X0)),k3_xboole_0(k1_relat_1(sK1),k1_relat_1(X0))) ) ),
    inference(resolution,[],[f66,f94])).

fof(f24866,plain,(
    ! [X0] :
      ( r2_hidden(X0,k3_relat_1(sK1))
      | ~ r2_hidden(X0,k3_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X0,k1_relat_1(k3_xboole_0(sK0,sK1))) ) ),
    inference(resolution,[],[f24854,f961])).

fof(f24854,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k2_relat_1(k3_xboole_0(sK0,sK1)))
      | r2_hidden(X13,k3_relat_1(sK1)) ) ),
    inference(forward_demodulation,[],[f24839,f78])).

fof(f24839,plain,(
    ! [X13] :
      ( ~ r2_hidden(X13,k2_relat_1(k3_xboole_0(sK1,sK0)))
      | r2_hidden(X13,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f11918,f79])).

fof(f11918,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X1))))
      | r2_hidden(X0,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f1485,f680])).

fof(f680,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_xboole_0(k2_relat_1(sK1),X6))
      | r2_hidden(X5,k3_relat_1(sK1)) ) ),
    inference(resolution,[],[f172,f97])).

fof(f172,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relat_1(sK1))
      | r2_hidden(X3,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f98,f112])).

fof(f1485,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k3_xboole_0(k2_relat_1(sK1),k2_relat_1(k3_xboole_0(sK0,X1))))
      | ~ r2_hidden(X0,k2_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X1)))) ) ),
    inference(resolution,[],[f376,f68])).

fof(f376,plain,(
    ! [X10] : r1_tarski(k2_relat_1(k3_xboole_0(sK1,k3_xboole_0(sK0,X10))),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(k3_xboole_0(sK0,X10)))) ),
    inference(resolution,[],[f109,f105])).

fof(f109,plain,(
    ! [X2] :
      ( ~ v1_relat_1(X2)
      | r1_tarski(k2_relat_1(k3_xboole_0(sK1,X2)),k3_xboole_0(k2_relat_1(sK1),k2_relat_1(X2))) ) ),
    inference(resolution,[],[f66,f93])).
%------------------------------------------------------------------------------
