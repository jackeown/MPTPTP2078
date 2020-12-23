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
% DateTime   : Thu Dec  3 13:16:37 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 100 expanded)
%              Number of leaves         :   18 (  26 expanded)
%              Depth                    :   16
%              Number of atoms          :  171 ( 247 expanded)
%              Number of equality atoms :   90 ( 117 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f222,plain,(
    $false ),
    inference(subsumption_resolution,[],[f221,f133])).

fof(f133,plain,(
    k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f132,f95])).

fof(f95,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f81,f94])).

fof(f94,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f93,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f59,f55])).

fof(f55,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f81,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f132,plain,
    ( k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0))
    | k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(resolution,[],[f99,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

% (14441)Refutation not found, incomplete strategy% (14441)------------------------------
% (14441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f99,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f98,f46])).

fof(f46,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f98,plain,
    ( k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(forward_demodulation,[],[f97,f82])).

fof(f82,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f50,f48])).

fof(f48,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f50,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f97,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(k1_zfmisc_1(k1_xboole_0)))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f52,f87])).

fof(f87,plain,(
    ! [X0] : r2_hidden(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f79,f76])).

fof(f76,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f79,plain,(
    ! [X0,X3] :
      ( ~ r1_tarski(X3,X0)
      | r2_hidden(X3,k1_zfmisc_1(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f52,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f221,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f44,f219])).

fof(f219,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f196,f45])).

fof(f45,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f196,plain,
    ( k3_tarski(k1_xboole_0) = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f49,f175])).

fof(f175,plain,
    ( k1_xboole_0 = k1_zfmisc_1(sK0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f174])).

fof(f174,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k1_zfmisc_1(sK0) ),
    inference(superposition,[],[f44,f157])).

fof(f157,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))
      | k1_xboole_0 = X0
      | k1_xboole_0 = k1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f131,f53])).

fof(f131,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ) ),
    inference(forward_demodulation,[],[f128,f82])).

fof(f128,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X0)))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f108,f52])).

fof(f108,plain,(
    ! [X1] :
      ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f85,f79])).

fof(f85,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f63,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f49,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f44,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f35])).

fof(f35,plain,
    ( ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))
   => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (14425)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.48  % (14425)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (14441)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f222,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f221,f133])).
% 0.22/0.48  fof(f133,plain,(
% 0.22/0.48    k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0))),
% 0.22/0.48    inference(subsumption_resolution,[],[f132,f95])).
% 0.22/0.48  fof(f95,plain,(
% 0.22/0.48    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.48    inference(backward_demodulation,[],[f81,f94])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(forward_demodulation,[],[f93,f47])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.22/0.48  fof(f93,plain,(
% 0.22/0.48    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.48    inference(superposition,[],[f59,f55])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.48    inference(rectify,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f69])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,axiom,(
% 0.22/0.48    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0)) | k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.22/0.48    inference(resolution,[],[f99,f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.22/0.49  % (14441)Refutation not found, incomplete strategy% (14441)------------------------------
% 0.22/0.49  % (14441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    v1_xboole_0(k1_tarski(k1_xboole_0)) | k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0))),
% 0.22/0.49    inference(forward_demodulation,[],[f98,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,axiom,(
% 0.22/0.49    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    k1_xboole_0 = k3_yellow_0(k3_yellow_1(k1_xboole_0)) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    inference(forward_demodulation,[],[f97,f82])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f50,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,axiom,(
% 0.22/0.49    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,axiom,(
% 0.22/0.49    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    k1_xboole_0 = k3_yellow_0(k2_yellow_1(k1_zfmisc_1(k1_xboole_0))) | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.49    inference(resolution,[],[f52,f87])).
% 0.22/0.49  fof(f87,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(X0,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(resolution,[],[f79,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.49    inference(equality_resolution,[],[f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(flattening,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X3] : (~r1_tarski(X3,X0) | r2_hidden(X3,k1_zfmisc_1(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.49    inference(rectify,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X0] : (~r2_hidden(k1_xboole_0,X0) | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : ((k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k1_xboole_0,X0)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k1_xboole_0,X0) => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    k1_xboole_0 != k3_yellow_0(k3_yellow_1(k1_xboole_0))),
% 0.22/0.50    inference(backward_demodulation,[],[f44,f219])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    k1_xboole_0 = sK0),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f218])).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(forward_demodulation,[],[f196,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,axiom,(
% 0.22/0.50    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    k3_tarski(k1_xboole_0) = sK0 | k1_xboole_0 = sK0),
% 0.22/0.50    inference(superposition,[],[f49,f175])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    k1_xboole_0 = k1_zfmisc_1(sK0) | k1_xboole_0 = sK0),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f174])).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k1_zfmisc_1(sK0)),
% 0.22/0.50    inference(superposition,[],[f44,f157])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = k1_zfmisc_1(X0)) )),
% 0.22/0.50    inference(resolution,[],[f131,f53])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    ( ! [X0] : (v1_xboole_0(k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))) )),
% 0.22/0.50    inference(forward_demodulation,[],[f128,f82])).
% 0.22/0.50  fof(f128,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 = k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X0))) | v1_xboole_0(k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(resolution,[],[f108,f52])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = X1) )),
% 0.22/0.50    inference(resolution,[],[f85,f79])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(resolution,[],[f63,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_xboole_1)).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) => (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,axiom,(
% 0.22/0.50    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0)) => k1_xboole_0 != k3_yellow_0(k3_yellow_1(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ? [X0] : k1_xboole_0 != k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f26])).
% 0.22/0.50  fof(f26,negated_conjecture,(
% 0.22/0.50    ~! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.50    inference(negated_conjecture,[],[f25])).
% 0.22/0.50  fof(f25,conjecture,(
% 0.22/0.50    ! [X0] : k1_xboole_0 = k3_yellow_0(k3_yellow_1(X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_yellow_1)).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14425)------------------------------
% 0.22/0.50  % (14425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14425)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14425)Memory used [KB]: 1791
% 0.22/0.50  % (14425)Time elapsed: 0.070 s
% 0.22/0.50  % (14425)------------------------------
% 0.22/0.50  % (14425)------------------------------
% 0.22/0.50  % (14417)Success in time 0.133 s
%------------------------------------------------------------------------------
