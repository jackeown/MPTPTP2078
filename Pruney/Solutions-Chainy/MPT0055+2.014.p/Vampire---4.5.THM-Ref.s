%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:06 EST 2020

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 456 expanded)
%              Number of leaves         :    7 ( 111 expanded)
%              Depth                    :   17
%              Number of atoms          :  161 (3004 expanded)
%              Number of equality atoms :   30 ( 492 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1202,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1164,f1182])).

fof(f1182,plain,(
    ! [X1] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ),
    inference(subsumption_resolution,[],[f1047,f1173])).

fof(f1173,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f935,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f935,plain,(
    ! [X8,X7] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f289,f924])).

fof(f924,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f637,f911])).

fof(f911,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f902,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f902,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f267,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f267,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f145,f65])).

fof(f145,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f137,f93])).

fof(f93,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f32,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f32,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f137,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f32,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f637,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f631])).

fof(f631,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f188,f42])).

fof(f188,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f103,f64])).

fof(f103,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f32,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f289,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(superposition,[],[f121,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f121,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f93,f65])).

fof(f1047,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f924,f64])).

fof(f1164,plain,(
    ! [X0] : r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f935,f927])).

fof(f927,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f122,f924])).

fof(f122,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f93,f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:16:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  ipcrm: permission denied for id (803700737)
% 0.13/0.36  ipcrm: permission denied for id (807370754)
% 0.13/0.37  ipcrm: permission denied for id (802422787)
% 0.13/0.37  ipcrm: permission denied for id (809664517)
% 0.13/0.37  ipcrm: permission denied for id (803831814)
% 0.13/0.37  ipcrm: permission denied for id (803897352)
% 0.13/0.37  ipcrm: permission denied for id (807501833)
% 0.13/0.37  ipcrm: permission denied for id (802455562)
% 0.13/0.38  ipcrm: permission denied for id (803962891)
% 0.13/0.38  ipcrm: permission denied for id (803995660)
% 0.13/0.38  ipcrm: permission denied for id (807534605)
% 0.20/0.38  ipcrm: permission denied for id (804061198)
% 0.20/0.38  ipcrm: permission denied for id (809730063)
% 0.20/0.38  ipcrm: permission denied for id (804126736)
% 0.20/0.39  ipcrm: permission denied for id (809828371)
% 0.20/0.39  ipcrm: permission denied for id (802553876)
% 0.20/0.39  ipcrm: permission denied for id (807698453)
% 0.20/0.39  ipcrm: permission denied for id (807731222)
% 0.20/0.39  ipcrm: permission denied for id (804356119)
% 0.20/0.39  ipcrm: permission denied for id (807763992)
% 0.20/0.39  ipcrm: permission denied for id (809861145)
% 0.20/0.39  ipcrm: permission denied for id (804454426)
% 0.20/0.39  ipcrm: permission denied for id (807829531)
% 0.20/0.40  ipcrm: permission denied for id (802619420)
% 0.20/0.40  ipcrm: permission denied for id (802652189)
% 0.20/0.40  ipcrm: permission denied for id (804519966)
% 0.20/0.40  ipcrm: permission denied for id (809893919)
% 0.20/0.40  ipcrm: permission denied for id (807927841)
% 0.20/0.40  ipcrm: permission denied for id (804651042)
% 0.20/0.40  ipcrm: permission denied for id (807960611)
% 0.20/0.41  ipcrm: permission denied for id (807993380)
% 0.20/0.41  ipcrm: permission denied for id (808026149)
% 0.20/0.41  ipcrm: permission denied for id (808058918)
% 0.20/0.41  ipcrm: permission denied for id (804814887)
% 0.20/0.41  ipcrm: permission denied for id (802750504)
% 0.20/0.41  ipcrm: permission denied for id (808157226)
% 0.20/0.42  ipcrm: permission denied for id (804945964)
% 0.20/0.42  ipcrm: permission denied for id (808222765)
% 0.20/0.42  ipcrm: permission denied for id (810025006)
% 0.20/0.42  ipcrm: permission denied for id (802848815)
% 0.20/0.42  ipcrm: permission denied for id (805044272)
% 0.20/0.42  ipcrm: permission denied for id (805077041)
% 0.20/0.42  ipcrm: permission denied for id (810057778)
% 0.20/0.42  ipcrm: permission denied for id (802881587)
% 0.20/0.42  ipcrm: permission denied for id (805142580)
% 0.20/0.43  ipcrm: permission denied for id (805175349)
% 0.20/0.43  ipcrm: permission denied for id (805208118)
% 0.20/0.43  ipcrm: permission denied for id (805273656)
% 0.20/0.43  ipcrm: permission denied for id (805306425)
% 0.20/0.43  ipcrm: permission denied for id (805339194)
% 0.20/0.43  ipcrm: permission denied for id (805404732)
% 0.20/0.44  ipcrm: permission denied for id (802979901)
% 0.20/0.44  ipcrm: permission denied for id (805470271)
% 0.20/0.44  ipcrm: permission denied for id (803045440)
% 0.20/0.44  ipcrm: permission denied for id (810188865)
% 0.20/0.45  ipcrm: permission denied for id (803078213)
% 0.20/0.45  ipcrm: permission denied for id (808583239)
% 0.20/0.45  ipcrm: permission denied for id (808648777)
% 0.20/0.45  ipcrm: permission denied for id (808681546)
% 0.20/0.45  ipcrm: permission denied for id (808714315)
% 0.20/0.45  ipcrm: permission denied for id (803143756)
% 0.20/0.46  ipcrm: permission denied for id (805863502)
% 0.20/0.46  ipcrm: permission denied for id (805929040)
% 0.20/0.46  ipcrm: permission denied for id (808812625)
% 0.20/0.46  ipcrm: permission denied for id (808845394)
% 0.20/0.46  ipcrm: permission denied for id (806027347)
% 0.20/0.46  ipcrm: permission denied for id (808878164)
% 0.20/0.46  ipcrm: permission denied for id (806092885)
% 0.20/0.47  ipcrm: permission denied for id (806125654)
% 0.20/0.47  ipcrm: permission denied for id (806158423)
% 0.20/0.47  ipcrm: permission denied for id (806191192)
% 0.20/0.47  ipcrm: permission denied for id (808943706)
% 0.20/0.47  ipcrm: permission denied for id (806289499)
% 0.20/0.47  ipcrm: permission denied for id (803209309)
% 0.20/0.48  ipcrm: permission denied for id (806355038)
% 0.20/0.48  ipcrm: permission denied for id (806387807)
% 0.20/0.48  ipcrm: permission denied for id (809009248)
% 0.20/0.48  ipcrm: permission denied for id (809042017)
% 0.20/0.48  ipcrm: permission denied for id (803274850)
% 0.20/0.48  ipcrm: permission denied for id (806486115)
% 0.20/0.48  ipcrm: permission denied for id (809074788)
% 0.20/0.48  ipcrm: permission denied for id (810516581)
% 0.20/0.48  ipcrm: permission denied for id (803307622)
% 0.20/0.49  ipcrm: permission denied for id (806584423)
% 0.20/0.49  ipcrm: permission denied for id (803340392)
% 0.20/0.49  ipcrm: permission denied for id (810549353)
% 0.20/0.49  ipcrm: permission denied for id (806649962)
% 0.20/0.49  ipcrm: permission denied for id (810582123)
% 0.20/0.49  ipcrm: permission denied for id (806715500)
% 0.20/0.49  ipcrm: permission denied for id (806748269)
% 0.20/0.49  ipcrm: permission denied for id (806781038)
% 0.20/0.50  ipcrm: permission denied for id (810614895)
% 0.20/0.50  ipcrm: permission denied for id (806879344)
% 0.20/0.50  ipcrm: permission denied for id (803471473)
% 0.20/0.50  ipcrm: permission denied for id (809238642)
% 0.20/0.50  ipcrm: permission denied for id (810647667)
% 0.20/0.50  ipcrm: permission denied for id (803569780)
% 0.20/0.50  ipcrm: permission denied for id (810680437)
% 0.20/0.50  ipcrm: permission denied for id (807010422)
% 0.20/0.51  ipcrm: permission denied for id (810778745)
% 0.20/0.51  ipcrm: permission denied for id (809435258)
% 0.20/0.51  ipcrm: permission denied for id (810811515)
% 0.20/0.51  ipcrm: permission denied for id (809500796)
% 0.20/0.51  ipcrm: permission denied for id (807239805)
% 0.20/0.51  ipcrm: permission denied for id (809533566)
% 0.20/0.51  ipcrm: permission denied for id (809566335)
% 0.36/0.63  % (26287)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.36/0.63  % (26287)Refutation not found, incomplete strategy% (26287)------------------------------
% 0.36/0.63  % (26287)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.64  % (26303)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.36/0.64  % (26287)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.64  
% 0.36/0.64  % (26287)Memory used [KB]: 10618
% 0.36/0.64  % (26287)Time elapsed: 0.061 s
% 0.36/0.64  % (26287)------------------------------
% 0.36/0.64  % (26287)------------------------------
% 0.36/0.64  % (26283)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.36/0.64  % (26283)Refutation not found, incomplete strategy% (26283)------------------------------
% 0.36/0.64  % (26283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.64  % (26283)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.64  
% 0.36/0.64  % (26283)Memory used [KB]: 6140
% 0.36/0.64  % (26283)Time elapsed: 0.086 s
% 0.36/0.64  % (26283)------------------------------
% 0.36/0.64  % (26283)------------------------------
% 0.36/0.65  % (26307)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.36/0.65  % (26299)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.36/0.66  % (26291)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.36/0.68  % (26282)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.36/0.68  % (26299)Refutation not found, incomplete strategy% (26299)------------------------------
% 0.36/0.68  % (26299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.36/0.68  % (26299)Termination reason: Refutation not found, incomplete strategy
% 0.36/0.68  
% 0.36/0.68  % (26299)Memory used [KB]: 10746
% 0.36/0.68  % (26299)Time elapsed: 0.119 s
% 0.36/0.68  % (26299)------------------------------
% 0.36/0.68  % (26299)------------------------------
% 0.36/0.68  % (26281)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.50/0.69  % (26304)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.50/0.69  % (26304)Refutation not found, incomplete strategy% (26304)------------------------------
% 0.50/0.69  % (26304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.69  % (26304)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.69  
% 0.50/0.69  % (26304)Memory used [KB]: 6140
% 0.50/0.69  % (26304)Time elapsed: 0.126 s
% 0.50/0.69  % (26304)------------------------------
% 0.50/0.69  % (26304)------------------------------
% 0.50/0.70  % (26306)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.50/0.70  % (26302)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.50/0.70  % (26305)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.50/0.70  % (26279)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.50/0.70  % (26279)Refutation not found, incomplete strategy% (26279)------------------------------
% 0.50/0.70  % (26279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.70  % (26279)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.70  
% 0.50/0.70  % (26279)Memory used [KB]: 1663
% 0.50/0.70  % (26279)Time elapsed: 0.123 s
% 0.50/0.70  % (26279)------------------------------
% 0.50/0.70  % (26279)------------------------------
% 0.50/0.70  % (26281)Refutation not found, incomplete strategy% (26281)------------------------------
% 0.50/0.70  % (26281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.70  % (26281)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.70  
% 0.50/0.70  % (26281)Memory used [KB]: 10618
% 0.50/0.70  % (26281)Time elapsed: 0.133 s
% 0.50/0.70  % (26281)------------------------------
% 0.50/0.70  % (26281)------------------------------
% 0.50/0.70  % (26284)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.50/0.70  % (26285)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.50/0.70  % (26288)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.50/0.70  % (26280)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.50/0.70  % (26308)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.50/0.70  % (26297)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.50/0.70  % (26294)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.50/0.71  % (26294)Refutation not found, incomplete strategy% (26294)------------------------------
% 0.50/0.71  % (26294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26294)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26294)Memory used [KB]: 6140
% 0.50/0.71  % (26294)Time elapsed: 0.002 s
% 0.50/0.71  % (26294)------------------------------
% 0.50/0.71  % (26294)------------------------------
% 0.50/0.71  % (26300)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.50/0.71  % (26298)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.50/0.71  % (26286)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.50/0.71  % (26300)Refutation not found, incomplete strategy% (26300)------------------------------
% 0.50/0.71  % (26300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26300)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26300)Memory used [KB]: 1663
% 0.50/0.71  % (26300)Time elapsed: 0.110 s
% 0.50/0.71  % (26300)------------------------------
% 0.50/0.71  % (26300)------------------------------
% 0.50/0.71  % (26289)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.50/0.71  % (26289)Refutation not found, incomplete strategy% (26289)------------------------------
% 0.50/0.71  % (26289)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26289)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26289)Memory used [KB]: 10618
% 0.50/0.71  % (26289)Time elapsed: 0.148 s
% 0.50/0.71  % (26289)------------------------------
% 0.50/0.71  % (26289)------------------------------
% 0.50/0.71  % (26301)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.50/0.71  % (26296)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.50/0.71  % (26292)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.50/0.71  % (26296)Refutation not found, incomplete strategy% (26296)------------------------------
% 0.50/0.71  % (26296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26296)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26296)Memory used [KB]: 10618
% 0.50/0.71  % (26296)Time elapsed: 0.147 s
% 0.50/0.71  % (26296)------------------------------
% 0.50/0.71  % (26296)------------------------------
% 0.50/0.71  % (26301)Refutation not found, incomplete strategy% (26301)------------------------------
% 0.50/0.71  % (26301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26301)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26301)Memory used [KB]: 10746
% 0.50/0.71  % (26301)Time elapsed: 0.146 s
% 0.50/0.71  % (26301)------------------------------
% 0.50/0.71  % (26301)------------------------------
% 0.50/0.71  % (26295)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.50/0.71  % (26288)Refutation not found, incomplete strategy% (26288)------------------------------
% 0.50/0.71  % (26288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.71  % (26288)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.71  
% 0.50/0.71  % (26288)Memory used [KB]: 10618
% 0.50/0.71  % (26288)Time elapsed: 0.146 s
% 0.50/0.71  % (26288)------------------------------
% 0.50/0.71  % (26288)------------------------------
% 0.50/0.71  % (26290)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.50/0.72  % (26293)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.50/0.72  % (26290)Refutation not found, incomplete strategy% (26290)------------------------------
% 0.50/0.72  % (26290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.50/0.72  % (26290)Termination reason: Refutation not found, incomplete strategy
% 0.50/0.72  
% 0.50/0.72  % (26290)Memory used [KB]: 10618
% 0.50/0.72  % (26290)Time elapsed: 0.148 s
% 0.50/0.72  % (26290)------------------------------
% 0.50/0.72  % (26290)------------------------------
% 0.97/0.76  % (26309)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.97/0.76  % (26309)Refutation not found, incomplete strategy% (26309)------------------------------
% 0.97/0.76  % (26309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.97/0.76  % (26309)Termination reason: Refutation not found, incomplete strategy
% 0.97/0.76  
% 0.97/0.76  % (26309)Memory used [KB]: 6140
% 0.97/0.76  % (26309)Time elapsed: 0.006 s
% 0.97/0.76  % (26309)------------------------------
% 0.97/0.76  % (26309)------------------------------
% 1.02/0.77  % (26310)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.03/0.81  % (26311)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.03/0.83  % (26316)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 1.03/0.84  % (26312)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 1.03/0.84  % (26314)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 1.03/0.84  % (26318)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 1.03/0.84  % (26315)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 1.03/0.85  % (26317)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 1.03/0.85  % (26317)Refutation not found, incomplete strategy% (26317)------------------------------
% 1.03/0.85  % (26317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.85  % (26317)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.85  
% 1.03/0.85  % (26317)Memory used [KB]: 1663
% 1.03/0.85  % (26317)Time elapsed: 0.105 s
% 1.03/0.85  % (26317)------------------------------
% 1.03/0.85  % (26317)------------------------------
% 1.03/0.85  % (26320)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 1.03/0.85  % (26321)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 1.03/0.86  % (26319)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 1.03/0.86  % (26313)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 1.03/0.88  % (26322)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 1.03/0.88  % (26322)Refutation not found, incomplete strategy% (26322)------------------------------
% 1.03/0.88  % (26322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.03/0.88  % (26322)Termination reason: Refutation not found, incomplete strategy
% 1.03/0.88  
% 1.03/0.88  % (26322)Memory used [KB]: 1663
% 1.03/0.88  % (26322)Time elapsed: 0.034 s
% 1.03/0.88  % (26322)------------------------------
% 1.03/0.88  % (26322)------------------------------
% 1.13/0.99  % (26323)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 1.13/1.00  % (26324)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 1.13/1.00  % (26284)Time limit reached!
% 1.13/1.00  % (26284)------------------------------
% 1.13/1.00  % (26284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/1.00  % (26284)Termination reason: Time limit
% 1.13/1.00  % (26284)Termination phase: Saturation
% 1.13/1.00  
% 1.13/1.00  % (26284)Memory used [KB]: 9722
% 1.13/1.00  % (26284)Time elapsed: 0.400 s
% 1.13/1.00  % (26284)------------------------------
% 1.13/1.00  % (26284)------------------------------
% 1.24/1.07  % (26319)Refutation found. Thanks to Tanya!
% 1.24/1.07  % SZS status Theorem for theBenchmark
% 1.24/1.07  % SZS output start Proof for theBenchmark
% 1.24/1.07  fof(f1202,plain,(
% 1.24/1.07    $false),
% 1.24/1.07    inference(subsumption_resolution,[],[f1164,f1182])).
% 1.24/1.07  fof(f1182,plain,(
% 1.24/1.07    ( ! [X1] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 1.24/1.07    inference(subsumption_resolution,[],[f1047,f1173])).
% 1.24/1.07  fof(f1173,plain,(
% 1.24/1.07    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0))) )),
% 1.24/1.07    inference(superposition,[],[f935,f40])).
% 1.24/1.07  fof(f40,plain,(
% 1.24/1.07    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 1.24/1.07    inference(cnf_transformation,[],[f9])).
% 1.24/1.07  fof(f9,axiom,(
% 1.24/1.07    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 1.24/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 1.24/1.07  fof(f935,plain,(
% 1.24/1.07    ( ! [X8,X7] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))) )),
% 1.24/1.07    inference(subsumption_resolution,[],[f289,f924])).
% 1.24/1.07  fof(f924,plain,(
% 1.24/1.07    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.24/1.07    inference(global_subsumption,[],[f637,f911])).
% 1.24/1.07  fof(f911,plain,(
% 1.24/1.07    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 1.24/1.07    inference(subsumption_resolution,[],[f902,f65])).
% 1.24/1.07  fof(f65,plain,(
% 1.24/1.07    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 1.24/1.07    inference(equality_resolution,[],[f52])).
% 1.24/1.07  fof(f52,plain,(
% 1.24/1.07    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/1.07    inference(cnf_transformation,[],[f31])).
% 1.24/1.07  fof(f31,plain,(
% 1.24/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.24/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f30])).
% 1.24/1.07  fof(f30,plain,(
% 1.24/1.07    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.24/1.07    introduced(choice_axiom,[])).
% 1.24/1.07  fof(f29,plain,(
% 1.24/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.24/1.07    inference(rectify,[],[f28])).
% 1.24/1.07  fof(f28,plain,(
% 1.24/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.24/1.07    inference(flattening,[],[f27])).
% 1.24/1.07  fof(f27,plain,(
% 1.24/1.07    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 1.24/1.07    inference(nnf_transformation,[],[f4])).
% 1.24/1.07  fof(f4,axiom,(
% 1.24/1.07    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.24/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.24/1.07  fof(f902,plain,(
% 1.24/1.07    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 1.24/1.07    inference(superposition,[],[f267,f42])).
% 1.24/1.07  fof(f42,plain,(
% 1.24/1.07    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.24/1.07    inference(cnf_transformation,[],[f15])).
% 1.24/1.07  fof(f15,axiom,(
% 1.24/1.07    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.24/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.24/1.07  fof(f267,plain,(
% 1.24/1.07    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 1.24/1.07    inference(resolution,[],[f145,f65])).
% 1.24/1.07  fof(f145,plain,(
% 1.24/1.07    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 1.24/1.07    inference(subsumption_resolution,[],[f137,f93])).
% 1.24/1.07  fof(f93,plain,(
% 1.24/1.07    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.24/1.07    inference(equality_resolution,[],[f71])).
% 1.24/1.07  fof(f71,plain,(
% 1.24/1.07    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 1.24/1.07    inference(superposition,[],[f32,f54])).
% 1.24/1.07  fof(f54,plain,(
% 1.24/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.24/1.07    inference(cnf_transformation,[],[f31])).
% 1.24/1.07  fof(f32,plain,(
% 1.24/1.07    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.24/1.07    inference(cnf_transformation,[],[f22])).
% 1.24/1.07  fof(f22,plain,(
% 1.24/1.07    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.24/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 1.24/1.07  fof(f21,plain,(
% 1.24/1.07    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.24/1.07    introduced(choice_axiom,[])).
% 1.24/1.07  fof(f19,plain,(
% 1.24/1.07    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.24/1.07    inference(ennf_transformation,[],[f17])).
% 1.24/1.07  fof(f17,negated_conjecture,(
% 1.24/1.07    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.24/1.07    inference(negated_conjecture,[],[f16])).
% 1.24/1.07  fof(f16,conjecture,(
% 1.24/1.07    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.24/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.24/1.07  fof(f137,plain,(
% 1.24/1.07    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.24/1.07    inference(resolution,[],[f95,f64])).
% 1.24/1.07  fof(f64,plain,(
% 1.24/1.07    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 1.24/1.07    inference(equality_resolution,[],[f53])).
% 1.24/1.07  fof(f53,plain,(
% 1.24/1.07    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 1.24/1.07    inference(cnf_transformation,[],[f31])).
% 1.24/1.07  fof(f95,plain,(
% 1.24/1.07    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 1.24/1.07    inference(equality_resolution,[],[f72])).
% 1.24/1.07  fof(f72,plain,(
% 1.24/1.07    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 1.24/1.07    inference(superposition,[],[f32,f55])).
% 1.24/1.07  fof(f55,plain,(
% 1.24/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.24/1.07    inference(cnf_transformation,[],[f31])).
% 1.24/1.07  fof(f637,plain,(
% 1.24/1.07    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.24/1.07    inference(duplicate_literal_removal,[],[f631])).
% 1.24/1.07  fof(f631,plain,(
% 1.24/1.07    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 1.24/1.07    inference(superposition,[],[f188,f42])).
% 1.24/1.07  fof(f188,plain,(
% 1.24/1.07    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 1.24/1.07    inference(resolution,[],[f103,f64])).
% 1.24/1.07  fof(f103,plain,(
% 1.24/1.07    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 1.24/1.07    inference(equality_resolution,[],[f73])).
% 1.24/1.07  fof(f73,plain,(
% 1.24/1.07    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 1.24/1.07    inference(superposition,[],[f32,f56])).
% 1.24/1.07  fof(f56,plain,(
% 1.24/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 1.24/1.07    inference(cnf_transformation,[],[f31])).
% 1.24/1.07  fof(f289,plain,(
% 1.24/1.07    ( ! [X8,X7] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 1.24/1.07    inference(superposition,[],[f121,f50])).
% 1.24/1.07  fof(f50,plain,(
% 1.24/1.07    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.24/1.07    inference(cnf_transformation,[],[f14])).
% 1.24/1.07  fof(f14,axiom,(
% 1.24/1.07    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.24/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.24/1.07  fof(f121,plain,(
% 1.24/1.07    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 1.24/1.07    inference(resolution,[],[f93,f65])).
% 1.24/1.07  fof(f1047,plain,(
% 1.24/1.07    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 1.24/1.07    inference(resolution,[],[f924,f64])).
% 1.24/1.07  fof(f1164,plain,(
% 1.24/1.07    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 1.24/1.07    inference(resolution,[],[f935,f927])).
% 1.24/1.07  fof(f927,plain,(
% 1.24/1.07    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 1.24/1.07    inference(subsumption_resolution,[],[f122,f924])).
% 1.24/1.07  fof(f122,plain,(
% 1.24/1.07    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 1.24/1.07    inference(resolution,[],[f93,f64])).
% 1.24/1.07  % SZS output end Proof for theBenchmark
% 1.24/1.07  % (26319)------------------------------
% 1.24/1.07  % (26319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/1.07  % (26319)Termination reason: Refutation
% 1.24/1.07  
% 1.24/1.07  % (26319)Memory used [KB]: 7291
% 1.24/1.07  % (26319)Time elapsed: 0.313 s
% 1.24/1.07  % (26319)------------------------------
% 1.24/1.07  % (26319)------------------------------
% 1.24/1.07  % (26291)Time limit reached!
% 1.24/1.07  % (26291)------------------------------
% 1.24/1.07  % (26291)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/1.07  % (26291)Termination reason: Time limit
% 1.24/1.07  % (26291)Termination phase: Saturation
% 1.24/1.07  
% 1.24/1.07  % (26291)Memory used [KB]: 10618
% 1.24/1.07  % (26291)Time elapsed: 0.500 s
% 1.24/1.07  % (26291)------------------------------
% 1.24/1.07  % (26291)------------------------------
% 1.24/1.07  % (26144)Success in time 0.703 s
%------------------------------------------------------------------------------
