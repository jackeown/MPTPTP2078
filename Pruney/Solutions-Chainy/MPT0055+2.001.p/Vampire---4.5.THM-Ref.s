%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:04 EST 2020

% Result     : Theorem 4.01s
% Output     : Refutation 4.01s
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
fof(f1213,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1175,f1193])).

fof(f1193,plain,(
    ! [X1] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ),
    inference(subsumption_resolution,[],[f1055,f1184])).

fof(f1184,plain,(
    ! [X0] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f941,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f941,plain,(
    ! [X8,X7] : ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f294,f930])).

fof(f930,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(global_subsumption,[],[f643,f917])).

fof(f917,plain,(
    ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f908,f66])).

fof(f66,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).

fof(f31,plain,(
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

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

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
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f908,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(superposition,[],[f268,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f268,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ) ),
    inference(resolution,[],[f146,f66])).

fof(f146,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f138,f94])).

fof(f94,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( k3_xboole_0(sK0,sK1) != X0
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0) ) ),
    inference(superposition,[],[f33,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f33,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f138,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(resolution,[],[f96,f65])).

fof(f65,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f96,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X1] :
      ( k3_xboole_0(sK0,sK1) != X1
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1) ) ),
    inference(superposition,[],[f33,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f643,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(duplicate_literal_removal,[],[f637])).

fof(f637,plain,
    ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ),
    inference(superposition,[],[f189,f44])).

fof(f189,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f104,f65])).

fof(f104,plain,
    ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
    | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2] :
      ( k3_xboole_0(sK0,sK1) != X2
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0)
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2) ) ),
    inference(superposition,[],[f33,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f294,plain,(
    ! [X8,X7] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(superposition,[],[f122,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1)))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) ) ),
    inference(resolution,[],[f94,f66])).

fof(f1055,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0))
      | ~ r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f930,f65])).

fof(f1175,plain,(
    ! [X0] : r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f941,f933])).

fof(f933,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(subsumption_resolution,[],[f123,f930])).

fof(f123,plain,(
    ! [X1] :
      ( r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1))
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)
      | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1) ) ),
    inference(resolution,[],[f94,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:26:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (20319)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.47  % (20303)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.52  % (20301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (20324)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.52  % (20300)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.52  % (20300)Refutation not found, incomplete strategy% (20300)------------------------------
% 0.22/0.52  % (20300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (20300)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (20300)Memory used [KB]: 6140
% 0.22/0.52  % (20300)Time elapsed: 0.109 s
% 0.22/0.52  % (20300)------------------------------
% 0.22/0.52  % (20300)------------------------------
% 0.22/0.53  % (20298)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (20299)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  % (20304)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (20298)Refutation not found, incomplete strategy% (20298)------------------------------
% 0.22/0.53  % (20298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20298)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20298)Memory used [KB]: 10618
% 0.22/0.53  % (20298)Time elapsed: 0.106 s
% 0.22/0.53  % (20298)------------------------------
% 0.22/0.53  % (20298)------------------------------
% 0.22/0.53  % (20311)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (20311)Refutation not found, incomplete strategy% (20311)------------------------------
% 0.22/0.53  % (20311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20311)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20311)Memory used [KB]: 6140
% 0.22/0.53  % (20311)Time elapsed: 0.002 s
% 0.22/0.53  % (20311)------------------------------
% 0.22/0.53  % (20311)------------------------------
% 0.22/0.53  % (20318)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (20316)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (20318)Refutation not found, incomplete strategy% (20318)------------------------------
% 0.22/0.53  % (20318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (20318)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (20318)Memory used [KB]: 10746
% 0.22/0.53  % (20318)Time elapsed: 0.084 s
% 0.22/0.53  % (20318)------------------------------
% 0.22/0.53  % (20318)------------------------------
% 0.22/0.54  % (20316)Refutation not found, incomplete strategy% (20316)------------------------------
% 0.22/0.54  % (20316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20308)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20310)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (20316)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20316)Memory used [KB]: 10746
% 0.22/0.54  % (20316)Time elapsed: 0.123 s
% 0.22/0.54  % (20316)------------------------------
% 0.22/0.54  % (20316)------------------------------
% 0.22/0.54  % (20323)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (20297)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (20322)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (20296)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (20296)Refutation not found, incomplete strategy% (20296)------------------------------
% 0.22/0.54  % (20296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20296)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20296)Memory used [KB]: 1663
% 0.22/0.54  % (20296)Time elapsed: 0.125 s
% 0.22/0.54  % (20296)------------------------------
% 0.22/0.54  % (20296)------------------------------
% 0.22/0.55  % (20307)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (20314)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (20304)Refutation not found, incomplete strategy% (20304)------------------------------
% 0.22/0.55  % (20304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20304)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20304)Memory used [KB]: 10618
% 0.22/0.55  % (20304)Time elapsed: 0.126 s
% 0.22/0.55  % (20304)------------------------------
% 0.22/0.55  % (20304)------------------------------
% 0.22/0.55  % (20302)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (20317)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (20317)Refutation not found, incomplete strategy% (20317)------------------------------
% 0.22/0.55  % (20317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20317)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20317)Memory used [KB]: 1663
% 0.22/0.55  % (20317)Time elapsed: 0.129 s
% 0.22/0.55  % (20317)------------------------------
% 0.22/0.55  % (20317)------------------------------
% 0.22/0.55  % (20320)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.55  % (20321)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (20309)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.55  % (20321)Refutation not found, incomplete strategy% (20321)------------------------------
% 0.22/0.55  % (20321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20321)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20321)Memory used [KB]: 6140
% 0.22/0.55  % (20321)Time elapsed: 0.128 s
% 0.22/0.55  % (20321)------------------------------
% 0.22/0.55  % (20321)------------------------------
% 0.22/0.55  % (20312)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (20306)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  % (20305)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (20306)Refutation not found, incomplete strategy% (20306)------------------------------
% 0.22/0.55  % (20306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20306)Memory used [KB]: 10618
% 0.22/0.55  % (20306)Time elapsed: 0.141 s
% 0.22/0.55  % (20306)------------------------------
% 0.22/0.55  % (20306)------------------------------
% 0.22/0.55  % (20305)Refutation not found, incomplete strategy% (20305)------------------------------
% 0.22/0.55  % (20305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (20305)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (20305)Memory used [KB]: 10618
% 0.22/0.55  % (20305)Time elapsed: 0.139 s
% 0.22/0.55  % (20305)------------------------------
% 0.22/0.55  % (20305)------------------------------
% 0.22/0.55  % (20315)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (20313)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (20313)Refutation not found, incomplete strategy% (20313)------------------------------
% 0.22/0.56  % (20313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20313)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20313)Memory used [KB]: 10618
% 0.22/0.56  % (20313)Time elapsed: 0.139 s
% 0.22/0.56  % (20313)------------------------------
% 0.22/0.56  % (20313)------------------------------
% 0.22/0.56  % (20325)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (20307)Refutation not found, incomplete strategy% (20307)------------------------------
% 0.22/0.57  % (20307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20307)Memory used [KB]: 10618
% 0.22/0.57  % (20307)Time elapsed: 0.150 s
% 0.22/0.57  % (20307)------------------------------
% 0.22/0.57  % (20307)------------------------------
% 2.11/0.67  % (20327)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.11/0.67  % (20329)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.11/0.67  % (20328)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.11/0.67  % (20333)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.11/0.68  % (20335)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.11/0.68  % (20332)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.11/0.68  % (20334)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.11/0.68  % (20331)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.11/0.68  % (20334)Refutation not found, incomplete strategy% (20334)------------------------------
% 2.11/0.68  % (20334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (20330)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.11/0.68  % (20334)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (20334)Memory used [KB]: 1663
% 2.11/0.68  % (20334)Time elapsed: 0.097 s
% 2.11/0.68  % (20334)------------------------------
% 2.11/0.68  % (20334)------------------------------
% 2.11/0.68  % (20326)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.11/0.68  % (20336)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.11/0.69  % (20326)Refutation not found, incomplete strategy% (20326)------------------------------
% 2.11/0.69  % (20326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.70  % (20326)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.70  
% 2.11/0.70  % (20326)Memory used [KB]: 6140
% 2.11/0.70  % (20326)Time elapsed: 0.121 s
% 2.11/0.70  % (20326)------------------------------
% 2.11/0.70  % (20326)------------------------------
% 2.63/0.71  % (20338)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.63/0.71  % (20337)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 3.06/0.79  % (20339)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 3.06/0.79  % (20339)Refutation not found, incomplete strategy% (20339)------------------------------
% 3.06/0.79  % (20339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.79  % (20339)Termination reason: Refutation not found, incomplete strategy
% 3.06/0.79  
% 3.06/0.79  % (20339)Memory used [KB]: 1663
% 3.06/0.79  % (20339)Time elapsed: 0.069 s
% 3.06/0.79  % (20339)------------------------------
% 3.06/0.79  % (20339)------------------------------
% 3.06/0.82  % (20301)Time limit reached!
% 3.06/0.82  % (20301)------------------------------
% 3.06/0.82  % (20301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.06/0.82  % (20301)Termination reason: Time limit
% 3.06/0.82  % (20301)Termination phase: Saturation
% 3.06/0.82  
% 3.06/0.82  % (20301)Memory used [KB]: 9338
% 3.06/0.82  % (20301)Time elapsed: 0.400 s
% 3.06/0.82  % (20301)------------------------------
% 3.06/0.82  % (20301)------------------------------
% 4.01/0.90  % (20341)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 4.01/0.91  % (20336)Refutation found. Thanks to Tanya!
% 4.01/0.91  % SZS status Theorem for theBenchmark
% 4.01/0.91  % SZS output start Proof for theBenchmark
% 4.01/0.91  fof(f1213,plain,(
% 4.01/0.91    $false),
% 4.01/0.91    inference(subsumption_resolution,[],[f1175,f1193])).
% 4.01/0.91  fof(f1193,plain,(
% 4.01/0.91    ( ! [X1] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.01/0.91    inference(subsumption_resolution,[],[f1055,f1184])).
% 4.01/0.91  fof(f1184,plain,(
% 4.01/0.91    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,sK0))) )),
% 4.01/0.91    inference(superposition,[],[f941,f42])).
% 4.01/0.91  fof(f42,plain,(
% 4.01/0.91    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 4.01/0.91    inference(cnf_transformation,[],[f11])).
% 4.01/0.91  fof(f11,axiom,(
% 4.01/0.91    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 4.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 4.01/0.91  fof(f941,plain,(
% 4.01/0.91    ( ! [X8,X7] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1))))) )),
% 4.01/0.91    inference(subsumption_resolution,[],[f294,f930])).
% 4.01/0.91  fof(f930,plain,(
% 4.01/0.91    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.01/0.91    inference(global_subsumption,[],[f643,f917])).
% 4.01/0.91  fof(f917,plain,(
% 4.01/0.91    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.01/0.91    inference(subsumption_resolution,[],[f908,f66])).
% 4.01/0.91  fof(f66,plain,(
% 4.01/0.91    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,k4_xboole_0(X0,X1))) )),
% 4.01/0.91    inference(equality_resolution,[],[f54])).
% 4.01/0.91  fof(f54,plain,(
% 4.01/0.91    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 4.01/0.91    inference(cnf_transformation,[],[f32])).
% 4.01/0.91  fof(f32,plain,(
% 4.01/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f30,f31])).
% 4.01/0.91  fof(f31,plain,(
% 4.01/0.91    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 4.01/0.91    introduced(choice_axiom,[])).
% 4.01/0.91  fof(f30,plain,(
% 4.01/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.91    inference(rectify,[],[f29])).
% 4.01/0.91  fof(f29,plain,(
% 4.01/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.91    inference(flattening,[],[f28])).
% 4.01/0.91  fof(f28,plain,(
% 4.01/0.91    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 4.01/0.91    inference(nnf_transformation,[],[f4])).
% 4.01/0.91  fof(f4,axiom,(
% 4.01/0.91    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 4.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 4.01/0.91  fof(f908,plain,(
% 4.01/0.91    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.01/0.91    inference(superposition,[],[f268,f44])).
% 4.01/0.91  fof(f44,plain,(
% 4.01/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.01/0.91    inference(cnf_transformation,[],[f16])).
% 4.01/0.91  fof(f16,axiom,(
% 4.01/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 4.01/0.91  fof(f268,plain,(
% 4.01/0.91    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)) )),
% 4.01/0.91    inference(resolution,[],[f146,f66])).
% 4.01/0.91  fof(f146,plain,(
% 4.01/0.91    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 4.01/0.91    inference(subsumption_resolution,[],[f138,f94])).
% 4.01/0.91  fof(f94,plain,(
% 4.01/0.91    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.01/0.91    inference(equality_resolution,[],[f72])).
% 4.01/0.91  fof(f72,plain,(
% 4.01/0.91    ( ! [X0] : (k3_xboole_0(sK0,sK1) != X0 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X0),X0)) )),
% 4.01/0.91    inference(superposition,[],[f33,f56])).
% 4.01/0.91  fof(f56,plain,(
% 4.01/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 4.01/0.91    inference(cnf_transformation,[],[f32])).
% 4.01/0.91  fof(f33,plain,(
% 4.01/0.91    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.01/0.91    inference(cnf_transformation,[],[f23])).
% 4.01/0.91  fof(f23,plain,(
% 4.01/0.91    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.01/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 4.01/0.91  fof(f22,plain,(
% 4.01/0.91    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.01/0.91    introduced(choice_axiom,[])).
% 4.01/0.91  fof(f20,plain,(
% 4.01/0.91    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.01/0.91    inference(ennf_transformation,[],[f18])).
% 4.01/0.91  fof(f18,negated_conjecture,(
% 4.01/0.91    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.01/0.91    inference(negated_conjecture,[],[f17])).
% 4.01/0.91  fof(f17,conjecture,(
% 4.01/0.91    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 4.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 4.01/0.91  fof(f138,plain,(
% 4.01/0.91    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.01/0.91    inference(resolution,[],[f96,f65])).
% 4.01/0.91  fof(f65,plain,(
% 4.01/0.91    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_xboole_0(X0,X1)) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 4.01/0.91    inference(equality_resolution,[],[f55])).
% 4.01/0.91  fof(f55,plain,(
% 4.01/0.91    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k4_xboole_0(X0,X1) != X2) )),
% 4.01/0.91    inference(cnf_transformation,[],[f32])).
% 4.01/0.91  fof(f96,plain,(
% 4.01/0.91    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.01/0.91    inference(equality_resolution,[],[f73])).
% 4.01/0.91  fof(f73,plain,(
% 4.01/0.91    ( ! [X1] : (k3_xboole_0(sK0,sK1) != X1 | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X1),X1)) )),
% 4.01/0.91    inference(superposition,[],[f33,f57])).
% 4.01/0.91  fof(f57,plain,(
% 4.01/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 4.01/0.91    inference(cnf_transformation,[],[f32])).
% 4.01/0.91  fof(f643,plain,(
% 4.01/0.91    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.01/0.91    inference(duplicate_literal_removal,[],[f637])).
% 4.01/0.91  fof(f637,plain,(
% 4.01/0.91    r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)),
% 4.01/0.91    inference(superposition,[],[f189,f44])).
% 4.01/0.91  fof(f189,plain,(
% 4.01/0.91    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.01/0.91    inference(resolution,[],[f104,f65])).
% 4.01/0.91  fof(f104,plain,(
% 4.01/0.91    ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))),
% 4.01/0.91    inference(equality_resolution,[],[f74])).
% 4.01/0.91  fof(f74,plain,(
% 4.01/0.91    ( ! [X2] : (k3_xboole_0(sK0,sK1) != X2 | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),k4_xboole_0(sK0,sK1)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),sK0) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),X2),X2)) )),
% 4.01/0.91    inference(superposition,[],[f33,f58])).
% 4.01/0.91  fof(f58,plain,(
% 4.01/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 4.01/0.91    inference(cnf_transformation,[],[f32])).
% 4.01/0.91  fof(f294,plain,(
% 4.01/0.91    ( ! [X8,X7] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X7,k2_xboole_0(X8,k3_xboole_0(sK0,sK1)))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 4.01/0.91    inference(superposition,[],[f122,f52])).
% 4.01/0.91  fof(f52,plain,(
% 4.01/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.01/0.91    inference(cnf_transformation,[],[f15])).
% 4.01/0.91  fof(f15,axiom,(
% 4.01/0.91    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.01/0.91    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 4.01/0.91  fof(f122,plain,(
% 4.01/0.91    ( ! [X0] : (~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X0,k3_xboole_0(sK0,sK1))) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0)) )),
% 4.01/0.91    inference(resolution,[],[f94,f66])).
% 4.01/0.91  fof(f1055,plain,(
% 4.01/0.91    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(X1,sK0)) | ~r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.01/0.91    inference(resolution,[],[f930,f65])).
% 4.01/0.91  fof(f1175,plain,(
% 4.01/0.91    ( ! [X0] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 4.01/0.91    inference(resolution,[],[f941,f933])).
% 4.01/0.91  fof(f933,plain,(
% 4.01/0.91    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.01/0.91    inference(subsumption_resolution,[],[f123,f930])).
% 4.01/0.91  fof(f123,plain,(
% 4.01/0.91    ( ! [X1] : (r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k4_xboole_0(k3_xboole_0(sK0,sK1),X1)) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK0) | r2_hidden(sK3(sK0,k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),X1)) )),
% 4.01/0.91    inference(resolution,[],[f94,f65])).
% 4.01/0.91  % SZS output end Proof for theBenchmark
% 4.01/0.91  % (20336)------------------------------
% 4.01/0.91  % (20336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.91  % (20336)Termination reason: Refutation
% 4.01/0.91  
% 4.01/0.91  % (20336)Memory used [KB]: 7419
% 4.01/0.91  % (20336)Time elapsed: 0.290 s
% 4.01/0.91  % (20336)------------------------------
% 4.01/0.91  % (20336)------------------------------
% 4.01/0.91  % (20295)Success in time 0.534 s
%------------------------------------------------------------------------------
