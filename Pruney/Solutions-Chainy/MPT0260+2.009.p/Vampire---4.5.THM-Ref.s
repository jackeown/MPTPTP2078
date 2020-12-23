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
% DateTime   : Thu Dec  3 12:40:08 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   20 (  25 expanded)
%              Number of leaves         :    4 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  68 expanded)
%              Number of equality atoms :   12 (  20 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f28,f30,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_enumset1(X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f20])).

fof(f20,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f30,plain,(
    ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f24,f11,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
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

fof(f11,plain,(
    r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( r2_hidden(X0,X2)
      & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r2_hidden(X0,X2)
          & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f24,plain,(
    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f10,f12])).

fof(f12,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f10,plain,(
    r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X4,X2,X0] : sP5(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:40:11 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.22/0.52  % (27488)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (27469)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.53  % (27476)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (27480)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.26/0.54  % (27487)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.26/0.54  % (27479)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.26/0.54  % (27488)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f50,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f28,f30,f26])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_enumset1(X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 1.26/0.54    inference(equality_resolution,[],[f20])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.26/0.54    inference(cnf_transformation,[],[f9])).
% 1.26/0.54  fof(f9,plain,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.26/0.54    inference(ennf_transformation,[],[f2])).
% 1.26/0.54  fof(f2,axiom,(
% 1.26/0.54    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK1))),
% 1.26/0.54    inference(unit_resulting_resolution,[],[f24,f11,f13])).
% 1.26/0.54  fof(f13,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f8])).
% 1.26/0.54  fof(f8,plain,(
% 1.26/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.26/0.54    inference(ennf_transformation,[],[f6])).
% 1.26/0.54  fof(f6,plain,(
% 1.26/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.54    inference(rectify,[],[f1])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.26/0.54  fof(f11,plain,(
% 1.26/0.54    r2_hidden(sK0,sK2)),
% 1.26/0.54    inference(cnf_transformation,[],[f7])).
% 1.26/0.54  fof(f7,plain,(
% 1.26/0.54    ? [X0,X1,X2] : (r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.26/0.54    inference(ennf_transformation,[],[f5])).
% 1.26/0.54  fof(f5,negated_conjecture,(
% 1.26/0.54    ~! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.26/0.54    inference(negated_conjecture,[],[f4])).
% 1.26/0.54  fof(f4,conjecture,(
% 1.26/0.54    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.26/0.54  fof(f24,plain,(
% 1.26/0.54    r1_xboole_0(k1_enumset1(sK0,sK0,sK1),sK2)),
% 1.26/0.54    inference(definition_unfolding,[],[f10,f12])).
% 1.26/0.54  fof(f12,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f3])).
% 1.26/0.54  fof(f3,axiom,(
% 1.26/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.26/0.54  fof(f10,plain,(
% 1.26/0.54    r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.26/0.54    inference(cnf_transformation,[],[f7])).
% 1.26/0.54  fof(f28,plain,(
% 1.26/0.54    ( ! [X4,X2,X0] : (sP5(X4,X2,X4,X0)) )),
% 1.26/0.54    inference(equality_resolution,[],[f17])).
% 1.26/0.54  fof(f17,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP5(X4,X2,X1,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f9])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (27470)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.26/0.54  % (27488)------------------------------
% 1.26/0.54  % (27488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (27488)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (27488)Memory used [KB]: 6140
% 1.26/0.54  % (27488)Time elapsed: 0.118 s
% 1.26/0.54  % (27488)------------------------------
% 1.26/0.54  % (27488)------------------------------
% 1.26/0.54  % (27463)Success in time 0.169 s
%------------------------------------------------------------------------------
