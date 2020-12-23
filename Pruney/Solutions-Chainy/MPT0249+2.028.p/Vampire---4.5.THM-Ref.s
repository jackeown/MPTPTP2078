%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:14 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 483 expanded)
%              Number of leaves         :   18 ( 140 expanded)
%              Depth                    :   20
%              Number of atoms          :  209 (1387 expanded)
%              Number of equality atoms :  111 ( 907 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f946,plain,(
    $false ),
    inference(subsumption_resolution,[],[f945,f47])).

fof(f47,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f945,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f943,f919])).

fof(f919,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f918,f45])).

fof(f45,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f30])).

fof(f918,plain,
    ( sK1 = sK2
    | ~ r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f855,f862])).

fof(f862,plain,(
    r1_tarski(sK2,sK1) ),
    inference(superposition,[],[f55,f762])).

fof(f762,plain,(
    sK2 = k3_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f708,f239])).

fof(f239,plain,(
    ! [X6,X7] : k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6 ),
    inference(superposition,[],[f224,f224])).

fof(f224,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f212,f49])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f212,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f177,f167])).

fof(f167,plain,(
    ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    inference(superposition,[],[f72,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f177,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f159,f141])).

fof(f141,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f140,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f140,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f135,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f135,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f58,f48])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f72,f48])).

fof(f708,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) ),
    inference(backward_demodulation,[],[f139,f705])).

fof(f705,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f102,f704])).

fof(f704,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f702,f46])).

fof(f46,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f30])).

fof(f702,plain,
    ( r2_hidden(sK0,sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f51,f700])).

fof(f700,plain,(
    sK0 = sK3(sK1) ),
    inference(subsumption_resolution,[],[f699,f46])).

fof(f699,plain,
    ( k1_xboole_0 = sK1
    | sK0 = sK3(sK1) ),
    inference(resolution,[],[f127,f85])).

fof(f85,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f54,f44])).

fof(f44,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | sK3(X0) = X1 ) ),
    inference(resolution,[],[f105,f81])).

fof(f81,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f105,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK3(X5),X6)
      | ~ r1_tarski(X5,X6)
      | k1_xboole_0 = X5 ) ),
    inference(resolution,[],[f62,f51])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f102,plain,
    ( ~ r2_hidden(sK0,sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f101,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f101,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | sK1 = k1_tarski(sK0) ),
    inference(resolution,[],[f61,f85])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,(
    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0)) ),
    inference(superposition,[],[f58,f44])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f855,plain,(
    ! [X5] :
      ( ~ r1_tarski(X5,sK1)
      | sK1 = X5
      | ~ r2_hidden(sK0,X5) ) ),
    inference(superposition,[],[f100,f705])).

fof(f100,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,k1_tarski(X6))
      | k1_tarski(X6) = X5
      | ~ r2_hidden(X6,X5) ) ),
    inference(resolution,[],[f61,f70])).

fof(f943,plain,
    ( r2_hidden(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f51,f941])).

fof(f941,plain,(
    sK0 = sK3(sK2) ),
    inference(subsumption_resolution,[],[f940,f47])).

fof(f940,plain,
    ( k1_xboole_0 = sK2
    | sK0 = sK3(sK2) ),
    inference(resolution,[],[f860,f862])).

fof(f860,plain,(
    ! [X12] :
      ( ~ r1_tarski(X12,sK1)
      | k1_xboole_0 = X12
      | sK0 = sK3(X12) ) ),
    inference(superposition,[],[f127,f705])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:50:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (16209)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (16201)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (16193)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (16185)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (16189)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (16204)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (16196)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (16194)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (16195)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.21/0.52  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (16194)Memory used [KB]: 10746
% 0.21/0.52  % (16194)Time elapsed: 0.107 s
% 0.21/0.52  % (16194)------------------------------
% 0.21/0.52  % (16194)------------------------------
% 0.21/0.52  % (16196)Refutation not found, incomplete strategy% (16196)------------------------------
% 0.21/0.52  % (16196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16190)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.31/0.53  % (16187)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.53  % (16196)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (16196)Memory used [KB]: 10618
% 1.31/0.53  % (16196)Time elapsed: 0.110 s
% 1.31/0.53  % (16196)------------------------------
% 1.31/0.53  % (16196)------------------------------
% 1.31/0.53  % (16187)Refutation not found, incomplete strategy% (16187)------------------------------
% 1.31/0.53  % (16187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.53  % (16187)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.53  
% 1.31/0.53  % (16187)Memory used [KB]: 10746
% 1.31/0.53  % (16187)Time elapsed: 0.117 s
% 1.31/0.53  % (16187)------------------------------
% 1.31/0.53  % (16187)------------------------------
% 1.31/0.53  % (16208)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.31/0.53  % (16202)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.53  % (16199)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.53  % (16203)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.53  % (16213)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.53  % (16215)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.53  % (16188)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (16192)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.54  % (16186)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (16198)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.54  % (16200)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.31/0.54  % (16211)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.31/0.54  % (16216)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.44/0.54  % (16206)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.44/0.55  % (16205)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.44/0.55  % (16212)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.44/0.55  % (16214)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.44/0.55  % (16207)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.44/0.55  % (16197)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.44/0.57  % (16193)Refutation found. Thanks to Tanya!
% 1.44/0.57  % SZS status Theorem for theBenchmark
% 1.44/0.57  % SZS output start Proof for theBenchmark
% 1.44/0.57  fof(f946,plain,(
% 1.44/0.57    $false),
% 1.44/0.57    inference(subsumption_resolution,[],[f945,f47])).
% 1.44/0.57  fof(f47,plain,(
% 1.44/0.57    k1_xboole_0 != sK2),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f30,plain,(
% 1.44/0.57    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29])).
% 1.44/0.57  fof(f29,plain,(
% 1.44/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f26,plain,(
% 1.44/0.57    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.44/0.57    inference(ennf_transformation,[],[f23])).
% 1.44/0.57  fof(f23,negated_conjecture,(
% 1.44/0.57    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.44/0.57    inference(negated_conjecture,[],[f22])).
% 1.44/0.57  fof(f22,conjecture,(
% 1.44/0.57    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 1.44/0.57  fof(f945,plain,(
% 1.44/0.57    k1_xboole_0 = sK2),
% 1.44/0.57    inference(subsumption_resolution,[],[f943,f919])).
% 1.44/0.57  fof(f919,plain,(
% 1.44/0.57    ~r2_hidden(sK0,sK2)),
% 1.44/0.57    inference(subsumption_resolution,[],[f918,f45])).
% 1.44/0.57  fof(f45,plain,(
% 1.44/0.57    sK1 != sK2),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f918,plain,(
% 1.44/0.57    sK1 = sK2 | ~r2_hidden(sK0,sK2)),
% 1.44/0.57    inference(resolution,[],[f855,f862])).
% 1.44/0.57  fof(f862,plain,(
% 1.44/0.57    r1_tarski(sK2,sK1)),
% 1.44/0.57    inference(superposition,[],[f55,f762])).
% 1.44/0.57  fof(f762,plain,(
% 1.44/0.57    sK2 = k3_xboole_0(sK1,sK2)),
% 1.44/0.57    inference(forward_demodulation,[],[f708,f239])).
% 1.44/0.57  fof(f239,plain,(
% 1.44/0.57    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X7,X6),X7) = X6) )),
% 1.44/0.57    inference(superposition,[],[f224,f224])).
% 1.44/0.57  fof(f224,plain,(
% 1.44/0.57    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 1.44/0.57    inference(forward_demodulation,[],[f212,f49])).
% 1.44/0.57  fof(f49,plain,(
% 1.44/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f7])).
% 1.44/0.57  fof(f7,axiom,(
% 1.44/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.44/0.57  fof(f212,plain,(
% 1.44/0.57    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 1.44/0.57    inference(superposition,[],[f177,f167])).
% 1.44/0.57  fof(f167,plain,(
% 1.44/0.57    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) )),
% 1.44/0.57    inference(superposition,[],[f72,f48])).
% 1.44/0.57  fof(f48,plain,(
% 1.44/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f10])).
% 1.44/0.57  fof(f10,axiom,(
% 1.44/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.44/0.57  fof(f72,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f9])).
% 1.44/0.57  fof(f9,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.44/0.57  fof(f177,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.44/0.57    inference(forward_demodulation,[],[f159,f141])).
% 1.44/0.57  fof(f141,plain,(
% 1.44/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.44/0.57    inference(forward_demodulation,[],[f140,f52])).
% 1.44/0.57  fof(f52,plain,(
% 1.44/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f24])).
% 1.44/0.57  fof(f24,plain,(
% 1.44/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.57    inference(rectify,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.44/0.57  fof(f140,plain,(
% 1.44/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.44/0.57    inference(forward_demodulation,[],[f135,f53])).
% 1.44/0.57  fof(f53,plain,(
% 1.44/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f25])).
% 1.44/0.57  fof(f25,plain,(
% 1.44/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.44/0.57    inference(rectify,[],[f2])).
% 1.44/0.57  fof(f2,axiom,(
% 1.44/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.44/0.57  fof(f135,plain,(
% 1.44/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.44/0.57    inference(superposition,[],[f58,f48])).
% 1.44/0.57  fof(f58,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f11])).
% 1.44/0.57  fof(f11,axiom,(
% 1.44/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.44/0.57  fof(f159,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.44/0.57    inference(superposition,[],[f72,f48])).
% 1.44/0.57  fof(f708,plain,(
% 1.44/0.57    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)),
% 1.44/0.57    inference(backward_demodulation,[],[f139,f705])).
% 1.44/0.57  fof(f705,plain,(
% 1.44/0.57    sK1 = k1_tarski(sK0)),
% 1.44/0.57    inference(subsumption_resolution,[],[f102,f704])).
% 1.44/0.57  fof(f704,plain,(
% 1.44/0.57    r2_hidden(sK0,sK1)),
% 1.44/0.57    inference(subsumption_resolution,[],[f702,f46])).
% 1.44/0.57  fof(f46,plain,(
% 1.44/0.57    k1_xboole_0 != sK1),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f702,plain,(
% 1.44/0.57    r2_hidden(sK0,sK1) | k1_xboole_0 = sK1),
% 1.44/0.57    inference(superposition,[],[f51,f700])).
% 1.44/0.57  fof(f700,plain,(
% 1.44/0.57    sK0 = sK3(sK1)),
% 1.44/0.57    inference(subsumption_resolution,[],[f699,f46])).
% 1.44/0.57  fof(f699,plain,(
% 1.44/0.57    k1_xboole_0 = sK1 | sK0 = sK3(sK1)),
% 1.44/0.57    inference(resolution,[],[f127,f85])).
% 1.44/0.57  fof(f85,plain,(
% 1.44/0.57    r1_tarski(sK1,k1_tarski(sK0))),
% 1.44/0.57    inference(superposition,[],[f54,f44])).
% 1.44/0.57  fof(f44,plain,(
% 1.44/0.57    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.44/0.57    inference(cnf_transformation,[],[f30])).
% 1.44/0.57  fof(f54,plain,(
% 1.44/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f8])).
% 1.44/0.57  fof(f8,axiom,(
% 1.44/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.44/0.57  fof(f127,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | sK3(X0) = X1) )),
% 1.44/0.57    inference(resolution,[],[f105,f81])).
% 1.44/0.57  fof(f81,plain,(
% 1.44/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.44/0.57    inference(equality_resolution,[],[f65])).
% 1.44/0.57  fof(f65,plain,(
% 1.44/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.44/0.57    inference(cnf_transformation,[],[f42])).
% 1.44/0.57  fof(f42,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f40,f41])).
% 1.44/0.57  fof(f41,plain,(
% 1.44/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f40,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.44/0.57    inference(rectify,[],[f39])).
% 1.44/0.57  fof(f39,plain,(
% 1.44/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.44/0.57    inference(nnf_transformation,[],[f12])).
% 1.44/0.57  fof(f12,axiom,(
% 1.44/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.44/0.57  fof(f105,plain,(
% 1.44/0.57    ( ! [X6,X5] : (r2_hidden(sK3(X5),X6) | ~r1_tarski(X5,X6) | k1_xboole_0 = X5) )),
% 1.44/0.57    inference(resolution,[],[f62,f51])).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f38])).
% 1.44/0.57  fof(f38,plain,(
% 1.44/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f36,f37])).
% 1.44/0.57  fof(f37,plain,(
% 1.44/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f36,plain,(
% 1.44/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.57    inference(rectify,[],[f35])).
% 1.44/0.57  fof(f35,plain,(
% 1.44/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.44/0.57    inference(nnf_transformation,[],[f28])).
% 1.44/0.57  fof(f28,plain,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f1])).
% 1.44/0.57  fof(f1,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.44/0.57  fof(f51,plain,(
% 1.44/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f32])).
% 1.44/0.57  fof(f32,plain,(
% 1.44/0.57    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.44/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f27,f31])).
% 1.44/0.57  fof(f31,plain,(
% 1.44/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.44/0.57    introduced(choice_axiom,[])).
% 1.44/0.57  fof(f27,plain,(
% 1.44/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.44/0.57    inference(ennf_transformation,[],[f4])).
% 1.44/0.57  fof(f4,axiom,(
% 1.44/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.44/0.57  fof(f102,plain,(
% 1.44/0.57    ~r2_hidden(sK0,sK1) | sK1 = k1_tarski(sK0)),
% 1.44/0.57    inference(resolution,[],[f101,f70])).
% 1.44/0.57  fof(f70,plain,(
% 1.44/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f43])).
% 1.44/0.57  fof(f43,plain,(
% 1.44/0.57    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.44/0.57    inference(nnf_transformation,[],[f20])).
% 1.44/0.57  fof(f20,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.44/0.57  fof(f101,plain,(
% 1.44/0.57    ~r1_tarski(k1_tarski(sK0),sK1) | sK1 = k1_tarski(sK0)),
% 1.44/0.57    inference(resolution,[],[f61,f85])).
% 1.44/0.57  fof(f61,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.44/0.57    inference(cnf_transformation,[],[f34])).
% 1.44/0.57  fof(f34,plain,(
% 1.44/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.57    inference(flattening,[],[f33])).
% 1.44/0.57  fof(f33,plain,(
% 1.44/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.44/0.57    inference(nnf_transformation,[],[f5])).
% 1.44/0.57  fof(f5,axiom,(
% 1.44/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.57  fof(f139,plain,(
% 1.44/0.57    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),k1_tarski(sK0))),
% 1.44/0.57    inference(superposition,[],[f58,f44])).
% 1.44/0.57  fof(f55,plain,(
% 1.44/0.57    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f6])).
% 1.44/0.57  fof(f6,axiom,(
% 1.44/0.57    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.44/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.44/0.57  fof(f855,plain,(
% 1.44/0.57    ( ! [X5] : (~r1_tarski(X5,sK1) | sK1 = X5 | ~r2_hidden(sK0,X5)) )),
% 1.44/0.57    inference(superposition,[],[f100,f705])).
% 1.44/0.57  fof(f100,plain,(
% 1.44/0.57    ( ! [X6,X5] : (~r1_tarski(X5,k1_tarski(X6)) | k1_tarski(X6) = X5 | ~r2_hidden(X6,X5)) )),
% 1.44/0.57    inference(resolution,[],[f61,f70])).
% 1.44/0.57  fof(f943,plain,(
% 1.44/0.57    r2_hidden(sK0,sK2) | k1_xboole_0 = sK2),
% 1.44/0.57    inference(superposition,[],[f51,f941])).
% 1.44/0.57  fof(f941,plain,(
% 1.44/0.57    sK0 = sK3(sK2)),
% 1.44/0.57    inference(subsumption_resolution,[],[f940,f47])).
% 1.44/0.57  fof(f940,plain,(
% 1.44/0.57    k1_xboole_0 = sK2 | sK0 = sK3(sK2)),
% 1.44/0.57    inference(resolution,[],[f860,f862])).
% 1.44/0.57  fof(f860,plain,(
% 1.44/0.57    ( ! [X12] : (~r1_tarski(X12,sK1) | k1_xboole_0 = X12 | sK0 = sK3(X12)) )),
% 1.44/0.57    inference(superposition,[],[f127,f705])).
% 1.44/0.57  % SZS output end Proof for theBenchmark
% 1.44/0.57  % (16193)------------------------------
% 1.44/0.57  % (16193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (16193)Termination reason: Refutation
% 1.44/0.57  
% 1.44/0.57  % (16193)Memory used [KB]: 7036
% 1.44/0.57  % (16193)Time elapsed: 0.115 s
% 1.44/0.57  % (16193)------------------------------
% 1.44/0.57  % (16193)------------------------------
% 1.44/0.57  % (16180)Success in time 0.208 s
%------------------------------------------------------------------------------
