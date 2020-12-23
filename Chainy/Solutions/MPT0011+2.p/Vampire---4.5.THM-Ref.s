%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0011+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 322 expanded)
%              Number of leaves         :    5 (  86 expanded)
%              Depth                    :   15
%              Number of atoms          :  156 (2256 expanded)
%              Number of equality atoms :   23 ( 342 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(subsumption_resolution,[],[f144,f133])).

fof(f133,plain,(
    r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f132,f92])).

fof(f92,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    inference(subsumption_resolution,[],[f89,f72])).

fof(f72,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
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
    inference(rectify,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f89,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f86,f72])).

fof(f86,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    inference(resolution,[],[f76,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f66,f75])).

fof(f75,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f76,plain,(
    ~ sQ4_eqProxy(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))) ),
    inference(equality_proxy_replacement,[],[f60,f75])).

fof(f60,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2))
   => k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) != k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,negated_conjecture,(
    ~ ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f44])).

fof(f44,conjecture,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f132,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f129,f127])).

fof(f127,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f123,f114])).

fof(f114,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),X0)
      | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,X0)) ) ),
    inference(resolution,[],[f98,f74])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f98,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f94,f73])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f94,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    inference(resolution,[],[f85,f73])).

fof(f85,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f76,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f65,f75])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f123,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    inference(resolution,[],[f95,f73])).

fof(f95,plain,
    ( ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f85,f72])).

fof(f129,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    inference(resolution,[],[f111,f74])).

fof(f111,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f110,f98])).

fof(f110,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f107,f92])).

fof(f107,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2)
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK1,sK2))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK0) ),
    inference(resolution,[],[f84,f74])).

fof(f84,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,k2_xboole_0(sK1,sK2)))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK2) ),
    inference(resolution,[],[f76,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( sQ4_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f64,f75])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f144,plain,(
    ~ r2_hidden(sK3(k2_xboole_0(sK0,sK1),sK2,k2_xboole_0(sK0,k2_xboole_0(sK1,sK2))),sK1) ),
    inference(resolution,[],[f127,f72])).
%------------------------------------------------------------------------------
