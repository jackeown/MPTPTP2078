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
% DateTime   : Thu Dec  3 13:16:40 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 232 expanded)
%              Number of leaves         :   14 (  65 expanded)
%              Depth                    :   16
%              Number of atoms          :  132 ( 516 expanded)
%              Number of equality atoms :   60 ( 231 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f211,plain,(
    $false ),
    inference(subsumption_resolution,[],[f203,f36])).

fof(f36,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f203,plain,(
    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f151,f188])).

fof(f188,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(backward_demodulation,[],[f50,f147])).

fof(f147,plain,(
    k1_xboole_0 = k9_setfam_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f78,f85])).

fof(f85,plain,(
    k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f84,f31])).

fof(f31,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f84,plain,(
    k3_tarski(k1_xboole_0) = sK0 ),
    inference(superposition,[],[f51,f78])).

fof(f51,plain,(
    ! [X0] : k3_tarski(k9_setfam_1(X0)) = X0 ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(f35,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f78,plain,(
    k1_xboole_0 = k9_setfam_1(sK0) ),
    inference(unit_resulting_resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f77,plain,(
    v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X0] : r2_hidden(X0,k9_setfam_1(X0)) ),
    inference(unit_resulting_resolution,[],[f56,f58])).

fof(f58,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k9_setfam_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k9_setfam_1(X0) != X1 ) ),
    inference(definition_unfolding,[],[f46,f34])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f29])).

% (20553)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f28,plain,(
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

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f56,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f76,plain,
    ( ~ r2_hidden(sK0,k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(forward_demodulation,[],[f75,f51])).

fof(f75,plain,
    ( ~ r2_hidden(k3_tarski(k9_setfam_1(sK0)),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(subsumption_resolution,[],[f74,f51])).

fof(f74,plain,
    ( sK0 != k3_tarski(k9_setfam_1(sK0))
    | ~ r2_hidden(k3_tarski(k9_setfam_1(sK0)),k9_setfam_1(sK0))
    | v1_xboole_0(k9_setfam_1(sK0)) ),
    inference(superposition,[],[f49,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f49,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0))) ),
    inference(definition_unfolding,[],[f30,f37])).

fof(f37,plain,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(f30,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).

% (20553)Refutation not found, incomplete strategy% (20553)------------------------------
% (20553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (20553)Termination reason: Refutation not found, incomplete strategy

% (20553)Memory used [KB]: 6140
% (20553)Time elapsed: 0.160 s
% (20553)------------------------------
% (20553)------------------------------
fof(f22,plain,
    ( ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0
   => sK0 != k4_yellow_0(k3_yellow_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

fof(f50,plain,(
    k1_tarski(k1_xboole_0) = k9_setfam_1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f32,f34])).

fof(f32,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f151,plain,(
    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_tarski(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f87,f85])).

fof(f87,plain,(
    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f80,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).

fof(f80,plain,(
    sK0 != k4_yellow_0(k2_yellow_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f49,f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:37:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (20536)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (20554)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (20543)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (20543)Refutation not found, incomplete strategy% (20543)------------------------------
% 0.21/0.53  % (20543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20554)Refutation not found, incomplete strategy% (20554)------------------------------
% 0.21/0.53  % (20554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20543)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20543)Memory used [KB]: 1663
% 0.21/0.53  % (20543)Time elapsed: 0.123 s
% 0.21/0.53  % (20543)------------------------------
% 0.21/0.53  % (20543)------------------------------
% 0.21/0.53  % (20554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20554)Memory used [KB]: 10618
% 0.21/0.53  % (20554)Time elapsed: 0.124 s
% 0.21/0.53  % (20554)------------------------------
% 0.21/0.53  % (20554)------------------------------
% 0.21/0.55  % (20529)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (20527)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.56  % (20551)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.55/0.56  % (20530)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.56  % (20537)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.56  % (20534)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.55/0.56  % (20537)Refutation not found, incomplete strategy% (20537)------------------------------
% 1.55/0.56  % (20537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (20537)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (20537)Memory used [KB]: 10618
% 1.55/0.56  % (20537)Time elapsed: 0.131 s
% 1.55/0.56  % (20537)------------------------------
% 1.55/0.56  % (20537)------------------------------
% 1.55/0.56  % (20539)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.55/0.56  % (20535)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.55/0.56  % (20529)Refutation found. Thanks to Tanya!
% 1.55/0.56  % SZS status Theorem for theBenchmark
% 1.55/0.56  % SZS output start Proof for theBenchmark
% 1.55/0.56  fof(f211,plain,(
% 1.55/0.56    $false),
% 1.55/0.56    inference(subsumption_resolution,[],[f203,f36])).
% 1.55/0.56  fof(f36,plain,(
% 1.55/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f3])).
% 1.55/0.56  fof(f3,axiom,(
% 1.55/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.55/0.56  fof(f203,plain,(
% 1.55/0.56    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_xboole_0)),
% 1.55/0.56    inference(backward_demodulation,[],[f151,f188])).
% 1.55/0.56  fof(f188,plain,(
% 1.55/0.56    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 1.55/0.56    inference(backward_demodulation,[],[f50,f147])).
% 1.55/0.56  fof(f147,plain,(
% 1.55/0.56    k1_xboole_0 = k9_setfam_1(k1_xboole_0)),
% 1.55/0.56    inference(backward_demodulation,[],[f78,f85])).
% 1.55/0.56  fof(f85,plain,(
% 1.55/0.56    k1_xboole_0 = sK0),
% 1.55/0.56    inference(forward_demodulation,[],[f84,f31])).
% 1.55/0.56  fof(f31,plain,(
% 1.55/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.55/0.56    inference(cnf_transformation,[],[f8])).
% 1.55/0.56  fof(f8,axiom,(
% 1.55/0.56    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.55/0.56  fof(f84,plain,(
% 1.55/0.56    k3_tarski(k1_xboole_0) = sK0),
% 1.55/0.56    inference(superposition,[],[f51,f78])).
% 1.55/0.56  fof(f51,plain,(
% 1.55/0.56    ( ! [X0] : (k3_tarski(k9_setfam_1(X0)) = X0) )),
% 1.55/0.56    inference(definition_unfolding,[],[f35,f34])).
% 1.55/0.56  fof(f34,plain,(
% 1.55/0.56    ( ! [X0] : (k1_zfmisc_1(X0) = k9_setfam_1(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f11])).
% 1.55/0.56  fof(f11,axiom,(
% 1.55/0.56    ! [X0] : k1_zfmisc_1(X0) = k9_setfam_1(X0)),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).
% 1.55/0.56  fof(f35,plain,(
% 1.55/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.55/0.56    inference(cnf_transformation,[],[f10])).
% 1.55/0.56  fof(f10,axiom,(
% 1.55/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.55/0.56  fof(f78,plain,(
% 1.55/0.56    k1_xboole_0 = k9_setfam_1(sK0)),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f77,f39])).
% 1.55/0.56  fof(f39,plain,(
% 1.55/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f19])).
% 1.55/0.56  fof(f19,plain,(
% 1.55/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f1])).
% 1.55/0.56  fof(f1,axiom,(
% 1.55/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.55/0.56  fof(f77,plain,(
% 1.55/0.56    v1_xboole_0(k9_setfam_1(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f76,f66])).
% 1.55/0.56  fof(f66,plain,(
% 1.55/0.56    ( ! [X0] : (r2_hidden(X0,k9_setfam_1(X0))) )),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f56,f58])).
% 1.55/0.56  fof(f58,plain,(
% 1.55/0.56    ( ! [X0,X3] : (r2_hidden(X3,k9_setfam_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.55/0.56    inference(equality_resolution,[],[f54])).
% 1.55/0.56  fof(f54,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k9_setfam_1(X0) != X1) )),
% 1.55/0.56    inference(definition_unfolding,[],[f46,f34])).
% 1.55/0.56  fof(f46,plain,(
% 1.55/0.56    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f29])).
% 1.55/0.56  % (20553)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.56  fof(f29,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 1.55/0.56  fof(f28,plain,(
% 1.55/0.56    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f27,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.56    inference(rectify,[],[f26])).
% 1.55/0.56  fof(f26,plain,(
% 1.55/0.56    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.55/0.56    inference(nnf_transformation,[],[f5])).
% 1.55/0.56  fof(f5,axiom,(
% 1.55/0.56    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.55/0.56  fof(f56,plain,(
% 1.55/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.55/0.56    inference(equality_resolution,[],[f43])).
% 1.55/0.56  fof(f43,plain,(
% 1.55/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f25])).
% 1.55/0.56  fof(f25,plain,(
% 1.55/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.56    inference(flattening,[],[f24])).
% 1.55/0.56  fof(f24,plain,(
% 1.55/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.55/0.56    inference(nnf_transformation,[],[f2])).
% 1.55/0.56  fof(f2,axiom,(
% 1.55/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.55/0.56  fof(f76,plain,(
% 1.55/0.56    ~r2_hidden(sK0,k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 1.55/0.56    inference(forward_demodulation,[],[f75,f51])).
% 1.55/0.56  fof(f75,plain,(
% 1.55/0.56    ~r2_hidden(k3_tarski(k9_setfam_1(sK0)),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 1.55/0.56    inference(subsumption_resolution,[],[f74,f51])).
% 1.55/0.56  fof(f74,plain,(
% 1.55/0.56    sK0 != k3_tarski(k9_setfam_1(sK0)) | ~r2_hidden(k3_tarski(k9_setfam_1(sK0)),k9_setfam_1(sK0)) | v1_xboole_0(k9_setfam_1(sK0))),
% 1.55/0.56    inference(superposition,[],[f49,f38])).
% 1.55/0.56  fof(f38,plain,(
% 1.55/0.56    ( ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0)) )),
% 1.55/0.56    inference(cnf_transformation,[],[f18])).
% 1.55/0.56  fof(f18,plain,(
% 1.55/0.56    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 1.55/0.56    inference(flattening,[],[f17])).
% 1.55/0.56  fof(f17,plain,(
% 1.55/0.56    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 1.55/0.56    inference(ennf_transformation,[],[f12])).
% 1.55/0.56  fof(f12,axiom,(
% 1.55/0.56    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 1.55/0.56  fof(f49,plain,(
% 1.55/0.56    sK0 != k4_yellow_0(k2_yellow_1(k9_setfam_1(sK0)))),
% 1.55/0.56    inference(definition_unfolding,[],[f30,f37])).
% 1.55/0.56  fof(f37,plain,(
% 1.55/0.56    ( ! [X0] : (k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))) )),
% 1.55/0.56    inference(cnf_transformation,[],[f13])).
% 1.55/0.56  fof(f13,axiom,(
% 1.55/0.56    ! [X0] : k3_yellow_1(X0) = k2_yellow_1(k9_setfam_1(X0))),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).
% 1.55/0.56  fof(f30,plain,(
% 1.55/0.56    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.55/0.56    inference(cnf_transformation,[],[f23])).
% 1.55/0.56  fof(f23,plain,(
% 1.55/0.56    sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.55/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f22])).
% 1.55/0.56  % (20553)Refutation not found, incomplete strategy% (20553)------------------------------
% 1.55/0.56  % (20553)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (20553)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (20553)Memory used [KB]: 6140
% 1.55/0.56  % (20553)Time elapsed: 0.160 s
% 1.55/0.56  % (20553)------------------------------
% 1.55/0.56  % (20553)------------------------------
% 1.55/0.56  fof(f22,plain,(
% 1.55/0.56    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0 => sK0 != k4_yellow_0(k3_yellow_1(sK0))),
% 1.55/0.56    introduced(choice_axiom,[])).
% 1.55/0.56  fof(f16,plain,(
% 1.55/0.56    ? [X0] : k4_yellow_0(k3_yellow_1(X0)) != X0),
% 1.55/0.56    inference(ennf_transformation,[],[f15])).
% 1.55/0.56  fof(f15,negated_conjecture,(
% 1.55/0.56    ~! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 1.55/0.56    inference(negated_conjecture,[],[f14])).
% 1.55/0.56  fof(f14,conjecture,(
% 1.55/0.56    ! [X0] : k4_yellow_0(k3_yellow_1(X0)) = X0),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).
% 1.55/0.56  fof(f50,plain,(
% 1.55/0.56    k1_tarski(k1_xboole_0) = k9_setfam_1(k1_xboole_0)),
% 1.55/0.56    inference(definition_unfolding,[],[f32,f34])).
% 1.55/0.56  fof(f32,plain,(
% 1.55/0.56    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.55/0.56    inference(cnf_transformation,[],[f7])).
% 1.55/0.56  fof(f7,axiom,(
% 1.55/0.56    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 1.55/0.56  fof(f151,plain,(
% 1.55/0.56    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_tarski(k1_xboole_0))),
% 1.55/0.56    inference(backward_demodulation,[],[f87,f85])).
% 1.55/0.56  fof(f87,plain,(
% 1.55/0.56    k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))) != k2_xboole_0(k1_tarski(k4_yellow_0(k2_yellow_1(k1_xboole_0))),k1_tarski(sK0))),
% 1.55/0.56    inference(unit_resulting_resolution,[],[f80,f41])).
% 1.55/0.56  fof(f41,plain,(
% 1.55/0.56    ( ! [X0,X1] : (k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.55/0.56    inference(cnf_transformation,[],[f21])).
% 1.55/0.56  fof(f21,plain,(
% 1.55/0.56    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 1.55/0.56    inference(ennf_transformation,[],[f6])).
% 1.55/0.56  fof(f6,axiom,(
% 1.55/0.56    ! [X0,X1] : (k1_tarski(X0) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.55/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_zfmisc_1)).
% 1.55/0.56  fof(f80,plain,(
% 1.55/0.56    sK0 != k4_yellow_0(k2_yellow_1(k1_xboole_0))),
% 1.55/0.56    inference(backward_demodulation,[],[f49,f78])).
% 1.55/0.56  % SZS output end Proof for theBenchmark
% 1.55/0.56  % (20531)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.56  % (20529)------------------------------
% 1.55/0.56  % (20529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (20529)Termination reason: Refutation
% 1.55/0.56  
% 1.55/0.56  % (20529)Memory used [KB]: 1791
% 1.55/0.56  % (20529)Time elapsed: 0.134 s
% 1.55/0.56  % (20529)------------------------------
% 1.55/0.56  % (20529)------------------------------
% 1.55/0.57  % (20524)Success in time 0.209 s
%------------------------------------------------------------------------------
