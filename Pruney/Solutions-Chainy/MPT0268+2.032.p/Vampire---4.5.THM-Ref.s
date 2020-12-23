%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:40 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 365 expanded)
%              Number of leaves         :   16 ( 107 expanded)
%              Depth                    :   17
%              Number of atoms          :  126 ( 533 expanded)
%              Number of equality atoms :   81 ( 352 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1095,f1071])).

fof(f1071,plain,(
    r2_hidden(sK1,sK0) ),
    inference(subsumption_resolution,[],[f35,f1070])).

fof(f1070,plain,(
    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f1045,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1045,plain,(
    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f46,f1043])).

fof(f1043,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(duplicate_literal_removal,[],[f1032])).

fof(f1032,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f628,f1027])).

fof(f1027,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f1026,f41])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1026,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(forward_demodulation,[],[f1020,f87])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f82,f62])).

fof(f62,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f61])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f60,f36])).

fof(f36,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f60,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0) ),
    inference(superposition,[],[f43,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f82,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f46,f39])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1020,plain,
    ( k3_xboole_0(k1_tarski(sK1),sK0) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1))
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(superposition,[],[f193,f581])).

% (4352)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f581,plain,
    ( k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(resolution,[],[f75,f34])).

fof(f34,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( r2_hidden(sK1,sK0)
      | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
    & ( ~ r2_hidden(sK1,sK0)
      | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
        & ( ~ r2_hidden(X1,X0)
          | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) )
   => ( ( r2_hidden(sK1,sK0)
        | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) )
      & ( ~ r2_hidden(sK1,sK0)
        | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f49,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f193,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10) ),
    inference(forward_demodulation,[],[f189,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f189,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k4_xboole_0(X9,X10)) ),
    inference(superposition,[],[f83,f65])).

fof(f65,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f48,f40])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f83,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f46,f41])).

fof(f628,plain,(
    ! [X28,X27] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27)) ),
    inference(forward_demodulation,[],[f627,f66])).

fof(f66,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(resolution,[],[f48,f59])).

fof(f59,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f40,f42])).

fof(f627,plain,(
    ! [X28,X27] : k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X28,k1_tarski(X27))) ),
    inference(forward_demodulation,[],[f615,f41])).

fof(f615,plain,(
    ! [X28,X27] : k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27)) = k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_xboole_0) ),
    inference(superposition,[],[f285,f595])).

fof(f595,plain,(
    ! [X2,X1] : k1_xboole_0 = k3_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1))) ),
    inference(forward_demodulation,[],[f589,f87])).

fof(f589,plain,(
    ! [X2,X1] : k3_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(superposition,[],[f193,f578])).

fof(f578,plain,(
    ! [X0,X1] : k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0))) ),
    inference(resolution,[],[f75,f58])).

fof(f58,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f285,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f276,f193])).

fof(f276,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f193,f194])).

fof(f194,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f135,f41])).

fof(f135,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(backward_demodulation,[],[f78,f126])).

fof(f126,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f65,f41])).

fof(f78,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f45,f45])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,
    ( sK0 != k4_xboole_0(sK0,k1_tarski(sK1))
    | r2_hidden(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f1095,plain,(
    ~ r2_hidden(sK1,sK0) ),
    inference(superposition,[],[f58,f1070])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (4337)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (4333)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (4342)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (4338)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (4334)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.57  % (4330)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.57  % (4332)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (4327)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.58  % (4347)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (4331)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.58  % (4356)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  % (4347)Refutation not found, incomplete strategy% (4347)------------------------------
% 0.21/0.58  % (4347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (4349)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.59  % (4349)Refutation not found, incomplete strategy% (4349)------------------------------
% 0.21/0.59  % (4349)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (4349)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (4349)Memory used [KB]: 10746
% 0.21/0.59  % (4349)Time elapsed: 0.156 s
% 0.21/0.59  % (4349)------------------------------
% 0.21/0.59  % (4349)------------------------------
% 0.21/0.59  % (4347)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (4347)Memory used [KB]: 10746
% 0.21/0.59  % (4347)Time elapsed: 0.154 s
% 0.21/0.59  % (4347)------------------------------
% 0.21/0.59  % (4347)------------------------------
% 0.21/0.59  % (4329)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.59  % (4345)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.59  % (4329)Refutation not found, incomplete strategy% (4329)------------------------------
% 0.21/0.59  % (4329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (4329)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (4329)Memory used [KB]: 10746
% 0.21/0.59  % (4329)Time elapsed: 0.160 s
% 0.21/0.59  % (4329)------------------------------
% 0.21/0.59  % (4329)------------------------------
% 0.21/0.59  % (4350)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.60  % (4354)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.60  % (4343)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.60  % (4328)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.60  % (4353)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.60  % (4341)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.60  % (4348)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.61  % (4351)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.61  % (4346)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.61  % (4355)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.61  % (4335)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.61  % (4340)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.62  % (4335)Refutation not found, incomplete strategy% (4335)------------------------------
% 1.58/0.62  % (4335)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.62  % (4335)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.62  
% 1.58/0.62  % (4335)Memory used [KB]: 10746
% 1.58/0.62  % (4335)Time elapsed: 0.193 s
% 1.58/0.62  % (4335)------------------------------
% 1.58/0.62  % (4335)------------------------------
% 1.58/0.62  % (4339)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.62  % (4334)Refutation found. Thanks to Tanya!
% 1.58/0.62  % SZS status Theorem for theBenchmark
% 1.58/0.63  % (4348)Refutation not found, incomplete strategy% (4348)------------------------------
% 1.58/0.63  % (4348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (4348)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.63  
% 1.58/0.63  % (4348)Memory used [KB]: 1663
% 1.58/0.63  % (4348)Time elapsed: 0.173 s
% 1.58/0.63  % (4348)------------------------------
% 1.58/0.63  % (4348)------------------------------
% 1.58/0.63  % SZS output start Proof for theBenchmark
% 1.58/0.63  fof(f1102,plain,(
% 1.58/0.63    $false),
% 1.58/0.63    inference(subsumption_resolution,[],[f1095,f1071])).
% 1.58/0.63  fof(f1071,plain,(
% 1.58/0.63    r2_hidden(sK1,sK0)),
% 1.58/0.63    inference(subsumption_resolution,[],[f35,f1070])).
% 1.58/0.63  fof(f1070,plain,(
% 1.58/0.63    sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(forward_demodulation,[],[f1045,f37])).
% 1.58/0.63  fof(f37,plain,(
% 1.58/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f8])).
% 1.58/0.63  fof(f8,axiom,(
% 1.58/0.63    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.58/0.63  fof(f1045,plain,(
% 1.58/0.63    k4_xboole_0(sK0,k1_tarski(sK1)) = k5_xboole_0(sK0,k1_xboole_0)),
% 1.58/0.63    inference(superposition,[],[f46,f1043])).
% 1.58/0.63  fof(f1043,plain,(
% 1.58/0.63    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(duplicate_literal_removal,[],[f1032])).
% 1.58/0.63  fof(f1032,plain,(
% 1.58/0.63    k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(superposition,[],[f628,f1027])).
% 1.58/0.63  fof(f1027,plain,(
% 1.58/0.63    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | k1_xboole_0 = k3_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(forward_demodulation,[],[f1026,f41])).
% 1.58/0.63  fof(f41,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f1])).
% 1.58/0.63  fof(f1,axiom,(
% 1.58/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.58/0.63  fof(f1026,plain,(
% 1.58/0.63    k1_xboole_0 = k3_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(forward_demodulation,[],[f1020,f87])).
% 1.58/0.63  fof(f87,plain,(
% 1.58/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.58/0.63    inference(forward_demodulation,[],[f82,f62])).
% 1.58/0.63  fof(f62,plain,(
% 1.58/0.63    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.58/0.63    inference(superposition,[],[f42,f61])).
% 1.58/0.63  fof(f61,plain,(
% 1.58/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.58/0.63    inference(forward_demodulation,[],[f60,f36])).
% 1.58/0.63  fof(f36,plain,(
% 1.58/0.63    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f19])).
% 1.58/0.63  fof(f19,axiom,(
% 1.58/0.63    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 1.58/0.63  fof(f60,plain,(
% 1.58/0.63    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = k2_xboole_0(X0,X0)) )),
% 1.58/0.63    inference(superposition,[],[f43,f38])).
% 1.58/0.63  fof(f38,plain,(
% 1.58/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f10])).
% 1.58/0.63  fof(f10,axiom,(
% 1.58/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.63  fof(f43,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.58/0.63    inference(cnf_transformation,[],[f18])).
% 1.58/0.63  fof(f18,axiom,(
% 1.58/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.58/0.63  fof(f42,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f6])).
% 1.58/0.63  fof(f6,axiom,(
% 1.58/0.63    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.58/0.63  fof(f82,plain,(
% 1.58/0.63    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.58/0.63    inference(superposition,[],[f46,f39])).
% 1.58/0.63  fof(f39,plain,(
% 1.58/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f23])).
% 1.58/0.63  fof(f23,plain,(
% 1.58/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.63    inference(rectify,[],[f2])).
% 1.58/0.63  fof(f2,axiom,(
% 1.58/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.58/0.63  fof(f1020,plain,(
% 1.58/0.63    k3_xboole_0(k1_tarski(sK1),sK0) = k5_xboole_0(k1_tarski(sK1),k1_tarski(sK1)) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(superposition,[],[f193,f581])).
% 1.58/0.63  % (4352)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.63  fof(f581,plain,(
% 1.58/0.63    k1_tarski(sK1) = k4_xboole_0(k1_tarski(sK1),sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(resolution,[],[f75,f34])).
% 1.58/0.63  fof(f34,plain,(
% 1.58/0.63    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 1.58/0.63    inference(cnf_transformation,[],[f31])).
% 1.58/0.63  fof(f31,plain,(
% 1.58/0.63    (r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)))),
% 1.58/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 1.58/0.63  fof(f30,plain,(
% 1.58/0.63    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0)) => ((r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))) & (~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))))),
% 1.58/0.63    introduced(choice_axiom,[])).
% 1.58/0.63  fof(f29,plain,(
% 1.58/0.63    ? [X0,X1] : ((r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0))),
% 1.58/0.63    inference(nnf_transformation,[],[f25])).
% 1.58/0.63  fof(f25,plain,(
% 1.58/0.63    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 1.58/0.63    inference(ennf_transformation,[],[f22])).
% 1.58/0.63  fof(f22,negated_conjecture,(
% 1.58/0.63    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.58/0.63    inference(negated_conjecture,[],[f21])).
% 1.58/0.63  fof(f21,conjecture,(
% 1.58/0.63    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.58/0.63  fof(f75,plain,(
% 1.58/0.63    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.58/0.63    inference(resolution,[],[f49,f47])).
% 1.58/0.63  fof(f47,plain,(
% 1.58/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f26])).
% 1.58/0.63  fof(f26,plain,(
% 1.58/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.58/0.63    inference(ennf_transformation,[],[f17])).
% 1.58/0.63  fof(f17,axiom,(
% 1.58/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.58/0.63  fof(f49,plain,(
% 1.58/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f28])).
% 1.58/0.63  fof(f28,plain,(
% 1.58/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.58/0.63    inference(ennf_transformation,[],[f24])).
% 1.58/0.63  fof(f24,plain,(
% 1.58/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.58/0.63    inference(unused_predicate_definition_removal,[],[f9])).
% 1.58/0.63  fof(f9,axiom,(
% 1.58/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.58/0.63  fof(f193,plain,(
% 1.58/0.63    ( ! [X10,X9] : (k5_xboole_0(X9,k4_xboole_0(X9,X10)) = k3_xboole_0(X9,X10)) )),
% 1.58/0.63    inference(forward_demodulation,[],[f189,f45])).
% 1.58/0.63  fof(f45,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.63    inference(cnf_transformation,[],[f7])).
% 1.58/0.63  fof(f7,axiom,(
% 1.58/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.63  fof(f189,plain,(
% 1.58/0.63    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X9,X10)) = k5_xboole_0(X9,k4_xboole_0(X9,X10))) )),
% 1.58/0.63    inference(superposition,[],[f83,f65])).
% 1.58/0.63  fof(f65,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 1.58/0.63    inference(resolution,[],[f48,f40])).
% 1.58/0.63  fof(f40,plain,(
% 1.58/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.58/0.63    inference(cnf_transformation,[],[f5])).
% 1.58/0.63  fof(f5,axiom,(
% 1.58/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.58/0.63  fof(f48,plain,(
% 1.58/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.58/0.63    inference(cnf_transformation,[],[f27])).
% 1.58/0.63  fof(f27,plain,(
% 1.58/0.63    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.58/0.63    inference(ennf_transformation,[],[f4])).
% 1.58/0.63  fof(f4,axiom,(
% 1.58/0.63    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.58/0.63  fof(f83,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.58/0.63    inference(superposition,[],[f46,f41])).
% 1.58/0.63  fof(f628,plain,(
% 1.58/0.63    ( ! [X28,X27] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27))) )),
% 1.58/0.63    inference(forward_demodulation,[],[f627,f66])).
% 1.58/0.63  fof(f66,plain,(
% 1.58/0.63    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 1.58/0.63    inference(resolution,[],[f48,f59])).
% 1.58/0.63  fof(f59,plain,(
% 1.58/0.63    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.58/0.63    inference(superposition,[],[f40,f42])).
% 1.58/0.63  fof(f627,plain,(
% 1.58/0.63    ( ! [X28,X27] : (k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27)) = k3_xboole_0(k1_xboole_0,k4_xboole_0(X28,k1_tarski(X27)))) )),
% 1.58/0.63    inference(forward_demodulation,[],[f615,f41])).
% 1.58/0.63  fof(f615,plain,(
% 1.58/0.63    ( ! [X28,X27] : (k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_tarski(X27)) = k3_xboole_0(k4_xboole_0(X28,k1_tarski(X27)),k1_xboole_0)) )),
% 1.58/0.63    inference(superposition,[],[f285,f595])).
% 1.58/0.63  fof(f595,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1)))) )),
% 1.58/0.63    inference(forward_demodulation,[],[f589,f87])).
% 1.58/0.63  fof(f589,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k3_xboole_0(k1_tarski(X1),k4_xboole_0(X2,k1_tarski(X1))) = k5_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 1.58/0.63    inference(superposition,[],[f193,f578])).
% 1.58/0.63  fof(f578,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k4_xboole_0(X1,k1_tarski(X0)))) )),
% 1.58/0.63    inference(resolution,[],[f75,f58])).
% 1.58/0.63  fof(f58,plain,(
% 1.58/0.63    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.58/0.63    inference(equality_resolution,[],[f52])).
% 1.58/0.63  fof(f52,plain,(
% 1.58/0.63    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.58/0.63    inference(cnf_transformation,[],[f33])).
% 1.58/0.63  fof(f33,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.58/0.63    inference(flattening,[],[f32])).
% 1.58/0.63  fof(f32,plain,(
% 1.58/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.58/0.63    inference(nnf_transformation,[],[f20])).
% 1.58/0.63  fof(f20,axiom,(
% 1.58/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.58/0.63  fof(f285,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.58/0.63    inference(forward_demodulation,[],[f276,f193])).
% 1.58/0.63  fof(f276,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.58/0.63    inference(superposition,[],[f193,f194])).
% 1.58/0.63  fof(f194,plain,(
% 1.58/0.63    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.58/0.63    inference(superposition,[],[f135,f41])).
% 1.58/0.63  fof(f135,plain,(
% 1.58/0.63    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 1.58/0.63    inference(backward_demodulation,[],[f78,f126])).
% 1.58/0.63  fof(f126,plain,(
% 1.58/0.63    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 1.58/0.63    inference(superposition,[],[f65,f41])).
% 1.58/0.63  fof(f78,plain,(
% 1.58/0.63    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 1.58/0.63    inference(superposition,[],[f45,f45])).
% 1.58/0.63  fof(f46,plain,(
% 1.58/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.58/0.63    inference(cnf_transformation,[],[f3])).
% 1.58/0.63  fof(f3,axiom,(
% 1.58/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.58/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.58/0.63  fof(f35,plain,(
% 1.58/0.63    sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) | r2_hidden(sK1,sK0)),
% 1.58/0.63    inference(cnf_transformation,[],[f31])).
% 1.58/0.63  fof(f1095,plain,(
% 1.58/0.63    ~r2_hidden(sK1,sK0)),
% 1.58/0.63    inference(superposition,[],[f58,f1070])).
% 1.58/0.63  % SZS output end Proof for theBenchmark
% 1.58/0.63  % (4334)------------------------------
% 1.58/0.63  % (4334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.63  % (4334)Termination reason: Refutation
% 1.58/0.63  
% 1.58/0.63  % (4334)Memory used [KB]: 6780
% 1.58/0.63  % (4334)Time elapsed: 0.145 s
% 1.58/0.63  % (4334)------------------------------
% 1.58/0.63  % (4334)------------------------------
% 1.58/0.63  % (4326)Success in time 0.262 s
%------------------------------------------------------------------------------
