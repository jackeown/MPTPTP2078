%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:43 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 114 expanded)
%              Number of leaves         :   16 (  30 expanded)
%              Depth                    :   16
%              Number of atoms          :  219 ( 407 expanded)
%              Number of equality atoms :   42 (  63 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(subsumption_resolution,[],[f308,f78])).

fof(f78,plain,(
    sK2 != k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(superposition,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
    & r2_hidden(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK2 != k2_xboole_0(k1_tarski(sK1),sK2)
      & r2_hidden(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f308,plain,(
    sK2 = k2_xboole_0(sK2,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f300,f44])).

fof(f44,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f300,plain,(
    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f51,f272])).

fof(f272,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2) ),
    inference(backward_demodulation,[],[f166,f264])).

fof(f264,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f94,f259])).

fof(f259,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(X9,X9) ),
    inference(resolution,[],[f248,f143])).

fof(f143,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(resolution,[],[f55,f90])).

fof(f90,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f57,f74])).

fof(f74,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f46,f43])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f248,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f198,f73])).

fof(f73,plain,(
    ! [X0,X1] : sP0(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f4,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f198,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ sP0(X2,X5,k4_xboole_0(X2,X3))
      | r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X4,X2,X5,X3] :
      ( r1_tarski(k4_xboole_0(X2,X3),X4)
      | ~ sP0(X2,X5,k4_xboole_0(X2,X3))
      | r1_tarski(k4_xboole_0(X2,X3),X4) ) ),
    inference(resolution,[],[f178,f159])).

fof(f159,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r2_hidden(sK3(X5,X6),X7)
      | ~ sP0(X7,X8,X5)
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f63,f57])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & r2_hidden(sK4(X0,X1,X2),X1) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X1) )
            & ( ( ~ r2_hidden(X4,X0)
                & r2_hidden(X4,X1) )
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X0)
              & r2_hidden(X3,X1) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & r2_hidden(sK4(X0,X1,X2),X1) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0)
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f155,f73])).

fof(f155,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ sP0(X8,X7,X5)
      | r2_hidden(sK3(X5,X6),X7)
      | r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f62,f57])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f50,f88])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f52,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f166,plain,(
    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) ),
    inference(superposition,[],[f50,f163])).

fof(f163,plain,(
    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2) ),
    inference(resolution,[],[f89,f41])).

fof(f41,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f89,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2) ) ),
    inference(resolution,[],[f52,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:29:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (19949)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (19965)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (19957)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (19949)Refutation not found, incomplete strategy% (19949)------------------------------
% 0.22/0.52  % (19949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19949)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19949)Memory used [KB]: 10618
% 0.22/0.52  % (19949)Time elapsed: 0.101 s
% 0.22/0.52  % (19949)------------------------------
% 0.22/0.52  % (19949)------------------------------
% 0.22/0.52  % (19957)Refutation not found, incomplete strategy% (19957)------------------------------
% 0.22/0.52  % (19957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (19957)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (19957)Memory used [KB]: 10618
% 0.22/0.52  % (19957)Time elapsed: 0.108 s
% 0.22/0.52  % (19957)------------------------------
% 0.22/0.52  % (19957)------------------------------
% 0.22/0.52  % (19971)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (19959)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (19948)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.53  % (19954)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (19961)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (19963)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (19953)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (19947)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (19950)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (19951)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (19973)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (19968)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.54  % (19962)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (19974)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (19975)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (19955)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (19955)Refutation not found, incomplete strategy% (19955)------------------------------
% 1.41/0.55  % (19955)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (19955)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (19955)Memory used [KB]: 10618
% 1.41/0.55  % (19955)Time elapsed: 0.138 s
% 1.41/0.55  % (19955)------------------------------
% 1.41/0.55  % (19955)------------------------------
% 1.41/0.55  % (19967)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (19956)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.56  % (19969)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.41/0.56  % (19954)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f309,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(subsumption_resolution,[],[f308,f78])).
% 1.41/0.56  fof(f78,plain,(
% 1.41/0.56    sK2 != k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.41/0.56    inference(superposition,[],[f42,f47])).
% 1.41/0.56  fof(f47,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    sK2 != k2_xboole_0(k1_tarski(sK1),sK2)),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2)),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f20,f26])).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK2 != k2_xboole_0(k1_tarski(sK1),sK2) & r2_hidden(sK1,sK2))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f18])).
% 1.41/0.56  fof(f18,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.41/0.56    inference(negated_conjecture,[],[f17])).
% 1.41/0.56  fof(f17,conjecture,(
% 1.41/0.56    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 1.41/0.56  fof(f308,plain,(
% 1.41/0.56    sK2 = k2_xboole_0(sK2,k1_tarski(sK1))),
% 1.41/0.56    inference(forward_demodulation,[],[f300,f44])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f8])).
% 1.41/0.56  fof(f8,axiom,(
% 1.41/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.41/0.56  fof(f300,plain,(
% 1.41/0.56    k2_xboole_0(sK2,k1_tarski(sK1)) = k2_xboole_0(sK2,k1_xboole_0)),
% 1.41/0.56    inference(superposition,[],[f51,f272])).
% 1.41/0.56  fof(f272,plain,(
% 1.41/0.56    k1_xboole_0 = k4_xboole_0(k1_tarski(sK1),sK2)),
% 1.41/0.56    inference(backward_demodulation,[],[f166,f264])).
% 1.41/0.56  fof(f264,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.41/0.56    inference(backward_demodulation,[],[f94,f259])).
% 1.41/0.56  fof(f259,plain,(
% 1.41/0.56    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(X9,X9)) )),
% 1.41/0.56    inference(resolution,[],[f248,f143])).
% 1.41/0.56  fof(f143,plain,(
% 1.41/0.56    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 1.41/0.56    inference(resolution,[],[f55,f90])).
% 1.41/0.56  fof(f90,plain,(
% 1.41/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.41/0.56    inference(resolution,[],[f57,f74])).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.41/0.56    inference(resolution,[],[f46,f43])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    v1_xboole_0(k1_xboole_0)),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    v1_xboole_0(k1_xboole_0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f21])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.41/0.56    inference(ennf_transformation,[],[f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.56    inference(unused_predicate_definition_removal,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.41/0.56  fof(f57,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f33])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(rectify,[],[f30])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.41/0.56    inference(nnf_transformation,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.41/0.56  fof(f55,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.56    inference(flattening,[],[f28])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.41/0.56    inference(nnf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.41/0.56  fof(f248,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 1.41/0.56    inference(resolution,[],[f198,f73])).
% 1.41/0.56  fof(f73,plain,(
% 1.41/0.56    ( ! [X0,X1] : (sP0(X1,X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(equality_resolution,[],[f68])).
% 1.41/0.56  fof(f68,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.56    inference(cnf_transformation,[],[f40])).
% 1.41/0.56  fof(f40,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 1.41/0.56    inference(nnf_transformation,[],[f25])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.41/0.56    inference(definition_folding,[],[f4,f24])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.56  fof(f198,plain,(
% 1.41/0.56    ( ! [X4,X2,X5,X3] : (~sP0(X2,X5,k4_xboole_0(X2,X3)) | r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 1.41/0.56    inference(duplicate_literal_removal,[],[f189])).
% 1.41/0.56  fof(f189,plain,(
% 1.41/0.56    ( ! [X4,X2,X5,X3] : (r1_tarski(k4_xboole_0(X2,X3),X4) | ~sP0(X2,X5,k4_xboole_0(X2,X3)) | r1_tarski(k4_xboole_0(X2,X3),X4)) )),
% 1.41/0.56    inference(resolution,[],[f178,f159])).
% 1.41/0.56  fof(f159,plain,(
% 1.41/0.56    ( ! [X6,X8,X7,X5] : (~r2_hidden(sK3(X5,X6),X7) | ~sP0(X7,X8,X5) | r1_tarski(X5,X6)) )),
% 1.41/0.56    inference(resolution,[],[f63,f57])).
% 1.41/0.56  fof(f63,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | ~sP0(X0,X1,X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2))) => ((r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((~r2_hidden(sK4(X0,X1,X2),X0) & r2_hidden(sK4(X0,X1,X2),X1)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : ((r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X0) & r2_hidden(X3,X1)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X0) | ~r2_hidden(X4,X1)) & ((~r2_hidden(X4,X0) & r2_hidden(X4,X1)) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.41/0.56    inference(rectify,[],[f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.41/0.56    inference(flattening,[],[f35])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.41/0.56    inference(nnf_transformation,[],[f24])).
% 1.41/0.56  fof(f178,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(k4_xboole_0(X0,X1),X2),X0) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 1.41/0.56    inference(resolution,[],[f155,f73])).
% 1.41/0.56  fof(f155,plain,(
% 1.41/0.56    ( ! [X6,X8,X7,X5] : (~sP0(X8,X7,X5) | r2_hidden(sK3(X5,X6),X7) | r1_tarski(X5,X6)) )),
% 1.41/0.56    inference(resolution,[],[f62,f57])).
% 1.41/0.56  fof(f62,plain,(
% 1.41/0.56    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~sP0(X0,X1,X2)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f39])).
% 1.41/0.56  fof(f94,plain,(
% 1.41/0.56    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.41/0.56    inference(superposition,[],[f50,f88])).
% 1.41/0.56  fof(f88,plain,(
% 1.41/0.56    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.41/0.56    inference(resolution,[],[f52,f71])).
% 1.41/0.56  fof(f71,plain,(
% 1.41/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.41/0.56    inference(equality_resolution,[],[f54])).
% 1.41/0.56  fof(f54,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.41/0.56    inference(cnf_transformation,[],[f29])).
% 1.41/0.56  fof(f52,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.41/0.56  fof(f50,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.56  fof(f166,plain,(
% 1.41/0.56    k4_xboole_0(k1_tarski(sK1),sK2) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))),
% 1.41/0.56    inference(superposition,[],[f50,f163])).
% 1.41/0.56  fof(f163,plain,(
% 1.41/0.56    k1_tarski(sK1) = k3_xboole_0(k1_tarski(sK1),sK2)),
% 1.41/0.56    inference(resolution,[],[f89,f41])).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    r2_hidden(sK1,sK2)),
% 1.41/0.56    inference(cnf_transformation,[],[f27])).
% 1.41/0.56  fof(f89,plain,(
% 1.41/0.56    ( ! [X2,X1] : (~r2_hidden(X1,X2) | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)) )),
% 1.41/0.56    inference(resolution,[],[f52,f60])).
% 1.41/0.56  fof(f60,plain,(
% 1.41/0.56    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.41/0.56    inference(nnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,axiom,(
% 1.41/0.56    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,axiom,(
% 1.41/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (19954)------------------------------
% 1.41/0.56  % (19954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (19954)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (19954)Memory used [KB]: 6396
% 1.41/0.56  % (19954)Time elapsed: 0.120 s
% 1.41/0.56  % (19954)------------------------------
% 1.41/0.56  % (19954)------------------------------
% 1.41/0.56  % (19969)Refutation not found, incomplete strategy% (19969)------------------------------
% 1.41/0.56  % (19969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (19969)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (19969)Memory used [KB]: 10746
% 1.41/0.56  % (19969)Time elapsed: 0.149 s
% 1.41/0.56  % (19969)------------------------------
% 1.41/0.56  % (19969)------------------------------
% 1.41/0.56  % (19958)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (19946)Success in time 0.194 s
%------------------------------------------------------------------------------
