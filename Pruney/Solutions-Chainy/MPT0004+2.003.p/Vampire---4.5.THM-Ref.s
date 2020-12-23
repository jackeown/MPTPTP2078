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
% DateTime   : Thu Dec  3 12:29:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 126 expanded)
%              Number of leaves         :    7 (  35 expanded)
%              Depth                    :   20
%              Number of atoms          :  110 ( 405 expanded)
%              Number of equality atoms :   19 (  69 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f88])).

fof(f88,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f87,f21])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f87,plain,(
    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f86,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f86,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f37])).

fof(f37,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f34])).

fof(f34,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK1)
    | k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f32,f21])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),X0)
      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X1] :
      ( r1_xboole_0(k3_xboole_0(sK0,sK1),X1)
      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f27,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f27,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_xboole_0(sK0,sK1))
      | k1_xboole_0 = k3_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    ! [X3] :
      ( r1_xboole_0(sK0,sK1)
      | ~ r2_hidden(X3,k3_xboole_0(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ( r1_xboole_0(sK0,sK1)
      & r2_hidden(sK2,k3_xboole_0(sK0,sK1)) )
    | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
      & ~ r1_xboole_0(sK0,sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) )
   => ( ( r1_xboole_0(sK0,sK1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(sK0,sK1))
        & ~ r1_xboole_0(sK0,sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))
   => r2_hidden(sK2,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      | ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ ( r1_xboole_0(X0,X1)
            & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
        & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
            & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f83,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f81,f26])).

fof(f81,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f78,f37])).

fof(f78,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f58,f17])).

fof(f17,plain,
    ( r2_hidden(sK2,k3_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2,X2)
      | ~ r1_xboole_0(X2,k1_xboole_0)
      | ~ r1_xboole_0(sK0,sK1) ) ),
    inference(forward_demodulation,[],[f44,f37])).

fof(f44,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,k3_xboole_0(sK0,sK1))
      | ~ r2_hidden(sK2,X2)
      | ~ r1_xboole_0(sK0,sK1) ) ),
    inference(resolution,[],[f24,f17])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 12:50:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.42  % (8725)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.43  % (8723)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (8723)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f89,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f88])).
% 0.22/0.43  fof(f88,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0),
% 0.22/0.43    inference(superposition,[],[f87,f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.43    inference(rectify,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.43  fof(f87,plain,(
% 0.22/0.43    k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(resolution,[],[f86,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f16,plain,(
% 0.22/0.43    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.43  fof(f86,plain,(
% 0.22/0.43    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f85])).
% 0.22/0.43  fof(f85,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.43    inference(forward_demodulation,[],[f83,f37])).
% 0.22/0.43  fof(f37,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(duplicate_literal_removal,[],[f34])).
% 0.22/0.43  fof(f34,plain,(
% 0.22/0.43    k1_xboole_0 = k3_xboole_0(sK0,sK1) | k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.43    inference(superposition,[],[f32,f21])).
% 0.22/0.43  fof(f32,plain,(
% 0.22/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,sK1),X0) | k1_xboole_0 = k3_xboole_0(sK0,sK1)) )),
% 0.22/0.43    inference(resolution,[],[f30,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f16])).
% 0.22/0.43  fof(f30,plain,(
% 0.22/0.43    ( ! [X1] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X1) | k1_xboole_0 = k3_xboole_0(sK0,sK1)) )),
% 0.22/0.43    inference(resolution,[],[f27,f22])).
% 0.22/0.43  fof(f22,plain,(
% 0.22/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f15])).
% 0.22/0.43  fof(f15,plain,(
% 0.22/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(ennf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    inference(rectify,[],[f3])).
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(sK0,sK1)) | k1_xboole_0 = k3_xboole_0(sK0,sK1)) )),
% 0.22/0.43    inference(resolution,[],[f25,f20])).
% 0.22/0.43  fof(f20,plain,(
% 0.22/0.43    ( ! [X3] : (r1_xboole_0(sK0,sK1) | ~r2_hidden(X3,k3_xboole_0(sK0,sK1))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    (r1_xboole_0(sK0,sK1) & r2_hidden(sK2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12,f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1))) => ((r1_xboole_0(sK0,sK1) & ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(sK0,sK1)) & ~r1_xboole_0(sK0,sK1)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ? [X2] : r2_hidden(X2,k3_xboole_0(sK0,sK1)) => r2_hidden(sK2,k3_xboole_0(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ? [X0,X1] : ((r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) | (! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,plain,(
% 0.22/0.44    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(rectify,[],[f5])).
% 0.22/0.44  fof(f5,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    inference(negated_conjecture,[],[f4])).
% 0.22/0.44  fof(f4,conjecture,(
% 0.22/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.44  fof(f83,plain,(
% 0.22/0.44    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k3_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(resolution,[],[f81,f26])).
% 0.22/0.44  fof(f81,plain,(
% 0.22/0.44    ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.44    inference(forward_demodulation,[],[f78,f37])).
% 0.22/0.44  fof(f78,plain,(
% 0.22/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(duplicate_literal_removal,[],[f74])).
% 0.22/0.44  fof(f74,plain,(
% 0.22/0.44    ~r1_xboole_0(k3_xboole_0(sK0,sK1),k1_xboole_0) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(resolution,[],[f58,f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    r2_hidden(sK2,k3_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f13])).
% 0.22/0.44  fof(f58,plain,(
% 0.22/0.44    ( ! [X2] : (~r2_hidden(sK2,X2) | ~r1_xboole_0(X2,k1_xboole_0) | ~r1_xboole_0(sK0,sK1)) )),
% 0.22/0.44    inference(forward_demodulation,[],[f44,f37])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ( ! [X2] : (~r1_xboole_0(X2,k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK2,X2) | ~r1_xboole_0(sK0,sK1)) )),
% 0.22/0.44    inference(resolution,[],[f24,f17])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (8723)------------------------------
% 0.22/0.44  % (8723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (8723)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (8723)Memory used [KB]: 6140
% 0.22/0.44  % (8723)Time elapsed: 0.005 s
% 0.22/0.44  % (8723)------------------------------
% 0.22/0.44  % (8723)------------------------------
% 0.22/0.44  % (8729)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (8717)Success in time 0.075 s
%------------------------------------------------------------------------------
