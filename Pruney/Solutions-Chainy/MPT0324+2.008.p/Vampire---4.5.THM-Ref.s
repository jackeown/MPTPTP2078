%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  59 expanded)
%              Number of leaves         :    7 (  16 expanded)
%              Depth                    :   11
%              Number of atoms          :  132 ( 267 expanded)
%              Number of equality atoms :    9 (  14 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f19])).

fof(f19,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)))
    & r2_hidden(sK1,k2_zfmisc_1(sK4,sK5))
    & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
        & r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
   => ( ~ r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)))
      & r2_hidden(sK1,k2_zfmisc_1(sK4,sK5))
      & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4)))
      & r2_hidden(X0,k2_zfmisc_1(X3,X4))
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
          & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
       => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( ( r2_hidden(X0,k2_zfmisc_1(X3,X4))
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) )
     => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).

fof(f70,plain,(
    ~ r2_hidden(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[],[f68,f31])).

fof(f31,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f8])).

fof(f8,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f68,plain,(
    ! [X2,X3] :
      ( ~ sP0(X2,X3,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))
      | ~ r2_hidden(sK1,X2) ) ),
    inference(resolution,[],[f61,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
              & r2_hidden(sK6(X0,X1,X2),X1) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f15])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X0)
            & r2_hidden(sK6(X0,X1,X2),X1) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X0)
                & r2_hidden(X3,X1) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f61,plain,(
    r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) ),
    inference(resolution,[],[f50,f32])).

fof(f32,plain,(
    ~ r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) ),
    inference(backward_demodulation,[],[f20,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f20,plain,(
    ~ r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X1] :
      ( r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),X1))
      | r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),X1)) ) ),
    inference(resolution,[],[f47,f34])).

fof(f34,plain,(
    ! [X0,X1] : sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f31,f21])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,k2_zfmisc_1(sK2,sK3),X1)
      | r2_hidden(sK1,X1)
      | r2_hidden(sK1,X0) ) ),
    inference(resolution,[],[f24,f18])).

fof(f18,plain,(
    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X2)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:02:54 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (11124)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (11116)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (11108)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (11103)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (11108)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (11104)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f70,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    r2_hidden(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))) & r2_hidden(sK1,k2_zfmisc_1(sK4,sK5)) & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f7,f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => (~r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5))) & r2_hidden(sK1,k2_zfmisc_1(sK4,sK5)) & r2_hidden(sK1,k2_zfmisc_1(sK2,sK3)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.21/0.51    inference(flattening,[],[f6])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ? [X0,X1,X2,X3,X4] : (~r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))) & (r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.21/0.51    inference(negated_conjecture,[],[f4])).
% 0.21/0.51  fof(f4,conjecture,(
% 0.21/0.51    ! [X0,X1,X2,X3,X4] : ((r2_hidden(X0,k2_zfmisc_1(X3,X4)) & r2_hidden(X0,k2_zfmisc_1(X1,X2))) => r2_hidden(X0,k2_zfmisc_1(k3_xboole_0(X1,X3),k3_xboole_0(X2,X4))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_zfmisc_1)).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k2_zfmisc_1(sK4,sK5))),
% 0.21/0.51    inference(resolution,[],[f68,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.21/0.51    inference(definition_folding,[],[f1,f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~sP0(X2,X3,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5))) | ~r2_hidden(sK1,X2)) )),
% 0.21/0.51    inference(resolution,[],[f61,f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f14,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X1)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.21/0.51    inference(rectify,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.51    inference(resolution,[],[f50,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK4,sK5)))),
% 0.21/0.51    inference(backward_demodulation,[],[f20,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k2_zfmisc_1(k3_xboole_0(sK2,sK4),k3_xboole_0(sK3,sK5)))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X1] : (r2_hidden(sK1,k3_xboole_0(k2_zfmisc_1(sK2,sK3),X1)) | r2_hidden(sK1,k4_xboole_0(k2_zfmisc_1(sK2,sK3),X1))) )),
% 0.21/0.51    inference(resolution,[],[f47,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (sP0(k4_xboole_0(X0,X1),X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(superposition,[],[f31,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~sP0(X0,k2_zfmisc_1(sK2,sK3),X1) | r2_hidden(sK1,X1) | r2_hidden(sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f24,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    r2_hidden(sK1,k2_zfmisc_1(sK2,sK3))),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,X0) | r2_hidden(X4,X2) | ~sP0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (11108)------------------------------
% 0.21/0.51  % (11108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (11108)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (11108)Memory used [KB]: 6268
% 0.21/0.51  % (11108)Time elapsed: 0.071 s
% 0.21/0.51  % (11108)------------------------------
% 0.21/0.51  % (11108)------------------------------
% 0.21/0.51  % (11107)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (11100)Success in time 0.155 s
%------------------------------------------------------------------------------
