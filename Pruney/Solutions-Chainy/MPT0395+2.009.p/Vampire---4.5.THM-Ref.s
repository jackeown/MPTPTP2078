%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:04 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   38 (  56 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 146 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f70,plain,(
    ~ r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1)) ),
    inference(resolution,[],[f65,f43])).

fof(f43,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_tarski(X1),sK1)
      | ~ r1_tarski(sK2(sK0,sK1),X1) ) ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_tarski(sK2(sK0,sK1),X0) ) ),
    inference(resolution,[],[f21,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( r1_setfam_1(X0,X1)
      | ~ r1_tarski(sK2(X0,X1),X3)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) )
     => ( ! [X3] :
            ( ~ r1_tarski(sK2(X0,X1),X3)
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | ? [X2] :
          ( ! [X3] :
              ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) )
     => r1_setfam_1(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f21,plain,(
    ~ r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_setfam_1(sK0,sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( ~ r1_setfam_1(X0,X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_setfam_1(sK0,sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => r1_setfam_1(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).

fof(f65,plain,(
    r1_tarski(k1_tarski(sK2(sK0,sK1)),sK1) ),
    inference(resolution,[],[f58,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | r1_tarski(k1_tarski(sK2(sK0,sK1)),X0) ) ),
    inference(superposition,[],[f30,f50])).

fof(f50,plain,(
    sK0 = k2_xboole_0(k1_tarski(sK2(sK0,sK1)),sK0) ),
    inference(resolution,[],[f39,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f39,plain,(
    r1_tarski(k1_tarski(sK2(sK0,sK1)),sK0) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    r2_hidden(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.09  % Command    : run_vampire %s %d
% 0.08/0.27  % Computer   : n014.cluster.edu
% 0.08/0.27  % Model      : x86_64 x86_64
% 0.08/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.27  % Memory     : 8042.1875MB
% 0.08/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.27  % CPULimit   : 60
% 0.08/0.27  % WCLimit    : 600
% 0.08/0.27  % DateTime   : Tue Dec  1 14:30:37 EST 2020
% 0.08/0.27  % CPUTime    : 
% 0.12/0.36  % (30295)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.12/0.36  % (30294)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.12/0.36  % (30294)Refutation not found, incomplete strategy% (30294)------------------------------
% 0.12/0.36  % (30294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.36  % (30294)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.36  
% 0.12/0.36  % (30294)Memory used [KB]: 10490
% 0.12/0.36  % (30294)Time elapsed: 0.049 s
% 0.12/0.36  % (30294)------------------------------
% 0.12/0.36  % (30294)------------------------------
% 0.12/0.37  % (30299)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.12/0.37  % (30299)Refutation not found, incomplete strategy% (30299)------------------------------
% 0.12/0.37  % (30299)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.37  % (30299)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.37  
% 0.12/0.37  % (30299)Memory used [KB]: 6012
% 0.12/0.37  % (30299)Time elapsed: 0.054 s
% 0.12/0.37  % (30299)------------------------------
% 0.12/0.37  % (30299)------------------------------
% 0.12/0.37  % (30301)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.12/0.38  % (30304)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.12/0.38  % (30309)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.12/0.38  % (30295)Refutation not found, incomplete strategy% (30295)------------------------------
% 0.12/0.38  % (30295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (30295)Termination reason: Refutation not found, incomplete strategy
% 0.12/0.38  
% 0.12/0.38  % (30295)Memory used [KB]: 10618
% 0.12/0.38  % (30295)Time elapsed: 0.065 s
% 0.12/0.38  % (30295)------------------------------
% 0.12/0.38  % (30295)------------------------------
% 0.12/0.38  % (30303)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.12/0.38  % (30303)Refutation found. Thanks to Tanya!
% 0.12/0.38  % SZS status Theorem for theBenchmark
% 0.12/0.38  % SZS output start Proof for theBenchmark
% 0.12/0.38  fof(f75,plain,(
% 0.12/0.38    $false),
% 0.12/0.38    inference(subsumption_resolution,[],[f70,f32])).
% 0.12/0.38  fof(f32,plain,(
% 0.12/0.38    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.12/0.38    inference(equality_resolution,[],[f23])).
% 0.12/0.38  fof(f23,plain,(
% 0.12/0.38    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.12/0.38    inference(cnf_transformation,[],[f16])).
% 0.12/0.38  fof(f16,plain,(
% 0.12/0.38    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.38    inference(flattening,[],[f15])).
% 0.12/0.38  fof(f15,plain,(
% 0.12/0.38    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.12/0.38    inference(nnf_transformation,[],[f1])).
% 0.12/0.38  fof(f1,axiom,(
% 0.12/0.38    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.12/0.38  fof(f70,plain,(
% 0.12/0.38    ~r1_tarski(sK2(sK0,sK1),sK2(sK0,sK1))),
% 0.12/0.38    inference(resolution,[],[f65,f43])).
% 0.12/0.38  fof(f43,plain,(
% 0.12/0.38    ( ! [X1] : (~r1_tarski(k1_tarski(X1),sK1) | ~r1_tarski(sK2(sK0,sK1),X1)) )),
% 0.12/0.38    inference(resolution,[],[f37,f28])).
% 0.12/0.38  fof(f28,plain,(
% 0.12/0.38    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f19])).
% 0.12/0.38  fof(f19,plain,(
% 0.12/0.38    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.12/0.38    inference(nnf_transformation,[],[f4])).
% 0.12/0.38  fof(f4,axiom,(
% 0.12/0.38    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.12/0.38  fof(f37,plain,(
% 0.12/0.38    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r1_tarski(sK2(sK0,sK1),X0)) )),
% 0.12/0.38    inference(resolution,[],[f21,f27])).
% 0.12/0.38  fof(f27,plain,(
% 0.12/0.38    ( ! [X0,X3,X1] : (r1_setfam_1(X0,X1) | ~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f18])).
% 0.12/0.38  fof(f18,plain,(
% 0.12/0.38    ! [X0,X1] : (r1_setfam_1(X0,X1) | (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.12/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f17])).
% 0.12/0.38  fof(f17,plain,(
% 0.12/0.38    ! [X1,X0] : (? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => (! [X3] : (~r1_tarski(sK2(X0,X1),X3) | ~r2_hidden(X3,X1)) & r2_hidden(sK2(X0,X1),X0)))),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f11,plain,(
% 0.12/0.38    ! [X0,X1] : (r1_setfam_1(X0,X1) | ? [X2] : (! [X3] : (~r1_tarski(X2,X3) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.12/0.38    inference(ennf_transformation,[],[f8])).
% 0.12/0.38  fof(f8,plain,(
% 0.12/0.38    ! [X0,X1] : (! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)) => r1_setfam_1(X0,X1))),
% 0.12/0.38    inference(unused_predicate_definition_removal,[],[f5])).
% 0.12/0.38  fof(f5,axiom,(
% 0.12/0.38    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.12/0.38  fof(f21,plain,(
% 0.12/0.38    ~r1_setfam_1(sK0,sK1)),
% 0.12/0.38    inference(cnf_transformation,[],[f14])).
% 0.12/0.38  fof(f14,plain,(
% 0.12/0.38    ~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1)),
% 0.12/0.38    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f13])).
% 0.12/0.38  fof(f13,plain,(
% 0.12/0.38    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1)) => (~r1_setfam_1(sK0,sK1) & r1_tarski(sK0,sK1))),
% 0.12/0.38    introduced(choice_axiom,[])).
% 0.12/0.38  fof(f9,plain,(
% 0.12/0.38    ? [X0,X1] : (~r1_setfam_1(X0,X1) & r1_tarski(X0,X1))),
% 0.12/0.38    inference(ennf_transformation,[],[f7])).
% 0.12/0.38  fof(f7,negated_conjecture,(
% 0.12/0.38    ~! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.12/0.38    inference(negated_conjecture,[],[f6])).
% 0.12/0.38  fof(f6,conjecture,(
% 0.12/0.38    ! [X0,X1] : (r1_tarski(X0,X1) => r1_setfam_1(X0,X1))),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_setfam_1)).
% 0.12/0.38  fof(f65,plain,(
% 0.12/0.38    r1_tarski(k1_tarski(sK2(sK0,sK1)),sK1)),
% 0.12/0.38    inference(resolution,[],[f58,f20])).
% 0.12/0.38  fof(f20,plain,(
% 0.12/0.38    r1_tarski(sK0,sK1)),
% 0.12/0.38    inference(cnf_transformation,[],[f14])).
% 0.12/0.38  fof(f58,plain,(
% 0.12/0.38    ( ! [X0] : (~r1_tarski(sK0,X0) | r1_tarski(k1_tarski(sK2(sK0,sK1)),X0)) )),
% 0.12/0.38    inference(superposition,[],[f30,f50])).
% 0.12/0.38  fof(f50,plain,(
% 0.12/0.38    sK0 = k2_xboole_0(k1_tarski(sK2(sK0,sK1)),sK0)),
% 0.12/0.38    inference(resolution,[],[f39,f22])).
% 0.12/0.38  fof(f22,plain,(
% 0.12/0.38    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f10])).
% 0.12/0.38  fof(f10,plain,(
% 0.12/0.38    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.12/0.38    inference(ennf_transformation,[],[f3])).
% 0.12/0.38  fof(f3,axiom,(
% 0.12/0.38    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.12/0.38  fof(f39,plain,(
% 0.12/0.38    r1_tarski(k1_tarski(sK2(sK0,sK1)),sK0)),
% 0.12/0.38    inference(resolution,[],[f36,f29])).
% 0.12/0.38  fof(f29,plain,(
% 0.12/0.38    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f19])).
% 0.12/0.38  fof(f36,plain,(
% 0.12/0.38    r2_hidden(sK2(sK0,sK1),sK0)),
% 0.12/0.38    inference(resolution,[],[f21,f26])).
% 0.12/0.38  fof(f26,plain,(
% 0.12/0.38    ( ! [X0,X1] : (r1_setfam_1(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f18])).
% 0.12/0.38  fof(f30,plain,(
% 0.12/0.38    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.12/0.38    inference(cnf_transformation,[],[f12])).
% 0.12/0.38  fof(f12,plain,(
% 0.12/0.38    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.12/0.38    inference(ennf_transformation,[],[f2])).
% 0.12/0.38  fof(f2,axiom,(
% 0.12/0.38    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.12/0.38    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.12/0.38  % SZS output end Proof for theBenchmark
% 0.12/0.38  % (30303)------------------------------
% 0.12/0.38  % (30303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.38  % (30303)Termination reason: Refutation
% 0.12/0.38  
% 0.12/0.38  % (30303)Memory used [KB]: 1663
% 0.12/0.38  % (30303)Time elapsed: 0.062 s
% 0.12/0.38  % (30303)------------------------------
% 0.12/0.38  % (30303)------------------------------
% 0.12/0.38  % (30308)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.12/0.38  % (30293)Success in time 0.098 s
%------------------------------------------------------------------------------
