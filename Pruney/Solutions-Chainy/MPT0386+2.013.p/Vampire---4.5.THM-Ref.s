%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:45:44 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :   13
%              Number of atoms          :   99 ( 132 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(subsumption_resolution,[],[f284,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f284,plain,(
    r2_hidden(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f283])).

fof(f283,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f281,f25])).

fof(f25,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),X0)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => r1_tarski(k1_setfam_1(X1),X0) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f281,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(k1_setfam_1(sK1),sK0) ),
    inference(resolution,[],[f275,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f275,plain,
    ( r2_hidden(sK6(k1_setfam_1(sK1),sK0),sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f273,f24])).

fof(f273,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(sK6(k1_setfam_1(sK1),sK0),X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f271,f61])).

fof(f61,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,k1_setfam_1(X0))
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_xboole_0 = X0
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X3)
      | ~ r2_hidden(X2,X1)
      | k1_setfam_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 )
        | k1_xboole_0 != X0 )
      & ( ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X2,X3)
                  | ~ r2_hidden(X3,X0) ) ) )
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = X0
       => ( k1_setfam_1(X0) = X1
        <=> k1_xboole_0 = X1 ) )
      & ( k1_xboole_0 != X0
       => ( k1_setfam_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ! [X3] :
                  ( r2_hidden(X3,X0)
                 => r2_hidden(X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

fof(f271,plain,(
    r2_hidden(sK6(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(trivial_inequality_removal,[],[f256])).

fof(f256,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK6(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1)) ),
    inference(superposition,[],[f52,f255])).

fof(f255,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK6(k1_setfam_1(sK1),sK0),sK6(k1_setfam_1(sK1),sK0)),k1_setfam_1(sK1)) ),
    inference(resolution,[],[f102,f25])).

fof(f102,plain,(
    ! [X4,X5] :
      ( r1_tarski(X4,X5)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(sK6(X4,X5),sK6(X4,X5)),X4) ) ),
    inference(resolution,[],[f53,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f47,f28])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f28])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f24,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:00:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.45/0.56  % (19497)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.56  % (19513)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.57  % (19497)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.58  % (19514)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.58  % (19505)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.45/0.58  % (19506)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.58  % (19513)Refutation not found, incomplete strategy% (19513)------------------------------
% 1.45/0.58  % (19513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f290,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(subsumption_resolution,[],[f284,f69])).
% 1.45/0.58  fof(f69,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.45/0.58    inference(resolution,[],[f39,f26])).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.58    inference(ennf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,plain,(
% 1.45/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.58    inference(rectify,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.58  fof(f284,plain,(
% 1.45/0.58    r2_hidden(sK0,k1_xboole_0)),
% 1.45/0.58    inference(backward_demodulation,[],[f24,f283])).
% 1.45/0.58  fof(f283,plain,(
% 1.45/0.58    k1_xboole_0 = sK1),
% 1.45/0.58    inference(subsumption_resolution,[],[f281,f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ~r1_tarski(k1_setfam_1(sK1),sK0)),
% 1.45/0.58    inference(cnf_transformation,[],[f17])).
% 1.45/0.58  fof(f17,plain,(
% 1.45/0.58    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),X0) & r2_hidden(X0,X1))),
% 1.45/0.58    inference(ennf_transformation,[],[f14])).
% 1.45/0.58  fof(f14,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.45/0.58    inference(negated_conjecture,[],[f13])).
% 1.45/0.58  fof(f13,conjecture,(
% 1.45/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.45/0.58  fof(f281,plain,(
% 1.45/0.58    k1_xboole_0 = sK1 | r1_tarski(k1_setfam_1(sK1),sK0)),
% 1.45/0.58    inference(resolution,[],[f275,f44])).
% 1.45/0.58  fof(f44,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f21])).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f16])).
% 1.45/0.58  fof(f16,plain,(
% 1.45/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.45/0.58    inference(unused_predicate_definition_removal,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.45/0.58  fof(f275,plain,(
% 1.45/0.58    r2_hidden(sK6(k1_setfam_1(sK1),sK0),sK0) | k1_xboole_0 = sK1),
% 1.45/0.58    inference(resolution,[],[f273,f24])).
% 1.45/0.58  fof(f273,plain,(
% 1.45/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(sK6(k1_setfam_1(sK1),sK0),X0) | k1_xboole_0 = sK1) )),
% 1.45/0.58    inference(resolution,[],[f271,f61])).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X2,X0,X3] : (~r2_hidden(X2,k1_setfam_1(X0)) | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | k1_xboole_0 = X0) )),
% 1.45/0.58    inference(equality_resolution,[],[f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = X0 | ~r2_hidden(X3,X0) | r2_hidden(X2,X3) | ~r2_hidden(X2,X1) | k1_setfam_1(X0) != X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ! [X0,X1] : (((k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1) | k1_xboole_0 != X0) & ((k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X2,X3) | ~r2_hidden(X3,X0)))) | k1_xboole_0 = X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,axiom,(
% 1.45/0.58    ! [X0,X1] : ((k1_xboole_0 = X0 => (k1_setfam_1(X0) = X1 <=> k1_xboole_0 = X1)) & (k1_xboole_0 != X0 => (k1_setfam_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ! [X3] : (r2_hidden(X3,X0) => r2_hidden(X2,X3))))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).
% 1.45/0.58  fof(f271,plain,(
% 1.45/0.58    r2_hidden(sK6(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f256])).
% 1.45/0.58  fof(f256,plain,(
% 1.45/0.58    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK6(k1_setfam_1(sK1),sK0),k1_setfam_1(sK1))),
% 1.45/0.58    inference(superposition,[],[f52,f255])).
% 1.45/0.58  fof(f255,plain,(
% 1.45/0.58    k1_xboole_0 = k4_xboole_0(k2_tarski(sK6(k1_setfam_1(sK1),sK0),sK6(k1_setfam_1(sK1),sK0)),k1_setfam_1(sK1))),
% 1.45/0.58    inference(resolution,[],[f102,f25])).
% 1.45/0.58  fof(f102,plain,(
% 1.45/0.58    ( ! [X4,X5] : (r1_tarski(X4,X5) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK6(X4,X5),sK6(X4,X5)),X4)) )),
% 1.45/0.58    inference(resolution,[],[f53,f43])).
% 1.45/0.58  fof(f43,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f21])).
% 1.45/0.58  fof(f53,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f47,f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f9])).
% 1.45/0.58  fof(f9,axiom,(
% 1.45/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f10])).
% 1.45/0.58  fof(f10,axiom,(
% 1.45/0.58    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 1.45/0.58  fof(f52,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f48,f28])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f10])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    r2_hidden(sK0,sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f17])).
% 1.45/0.58  % SZS output end Proof for theBenchmark
% 1.45/0.58  % (19497)------------------------------
% 1.45/0.58  % (19497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (19497)Termination reason: Refutation
% 1.45/0.58  
% 1.45/0.58  % (19497)Memory used [KB]: 6396
% 1.45/0.58  % (19497)Time elapsed: 0.139 s
% 1.45/0.58  % (19497)------------------------------
% 1.45/0.58  % (19497)------------------------------
% 1.45/0.58  % (19490)Success in time 0.221 s
%------------------------------------------------------------------------------
