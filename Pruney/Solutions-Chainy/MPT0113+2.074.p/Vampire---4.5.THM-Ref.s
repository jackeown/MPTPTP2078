%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  57 expanded)
%              Number of leaves         :    7 (  14 expanded)
%              Depth                    :   16
%              Number of atoms          :   81 ( 138 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f87,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(resolution,[],[f83,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f83,plain,(
    ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f58,f15])).

fof(f15,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f58,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_xboole_0(sK2,X0) ) ),
    inference(superposition,[],[f39,f18])).

fof(f18,plain,(
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
    ! [X0] : ~ r1_xboole_0(sK2,k2_xboole_0(sK0,X0)) ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f38,plain,(
    ~ r1_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f35,f19])).

fof(f35,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f33,f16])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f33,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    inference(resolution,[],[f32,f15])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f30,f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK0,X0)
      | ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(X0,sK1)
      | r1_tarski(sK0,sK1) ) ),
    inference(resolution,[],[f29,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,sK1),X1)
      | ~ r1_tarski(sK0,X0)
      | ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,sK1),X0)
      | ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,X0) ) ),
    inference(resolution,[],[f26,f20])).

fof(f26,plain,
    ( r2_hidden(sK3(sK0,sK1),sK0)
    | ~ r1_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f14,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (11187)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (11196)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.50  % (11179)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (11177)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (11177)Refutation not found, incomplete strategy% (11177)------------------------------
% 0.20/0.51  % (11177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11177)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (11177)Memory used [KB]: 10618
% 0.20/0.51  % (11177)Time elapsed: 0.109 s
% 0.20/0.51  % (11177)------------------------------
% 0.20/0.51  % (11177)------------------------------
% 0.20/0.51  % (11187)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f87,f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~r1_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 0.20/0.51    inference(resolution,[],[f83,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.51  fof(f83,plain,(
% 0.20/0.51    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(resolution,[],[f58,f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.51    inference(negated_conjecture,[],[f7])).
% 0.20/0.51  fof(f7,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_xboole_0(sK2,X0)) )),
% 0.20/0.51    inference(superposition,[],[f39,f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_xboole_0(sK2,k2_xboole_0(sK0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f38,f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ~r1_xboole_0(sK2,sK0)),
% 0.20/0.51    inference(resolution,[],[f35,f19])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f33,f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 0.20/0.51    inference(resolution,[],[f32,f15])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_xboole_0(sK0,sK2) | ~r1_tarski(X0,sK1)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f30,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ~r1_tarski(sK0,sK1) | ~r1_xboole_0(sK0,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (~r1_tarski(sK0,X0) | ~r1_xboole_0(sK0,sK2) | ~r1_tarski(X0,sK1) | r1_tarski(sK0,sK1)) )),
% 0.20/0.51    inference(resolution,[],[f29,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK3(sK0,sK1),X1) | ~r1_tarski(sK0,X0) | ~r1_xboole_0(sK0,sK2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(resolution,[],[f27,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(sK0,sK1),X0) | ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,X0)) )),
% 0.20/0.51    inference(resolution,[],[f26,f20])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    r2_hidden(sK3(sK0,sK1),sK0) | ~r1_xboole_0(sK0,sK2)),
% 0.20/0.51    inference(resolution,[],[f14,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11187)------------------------------
% 0.20/0.51  % (11187)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11187)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11187)Memory used [KB]: 1663
% 0.20/0.51  % (11187)Time elapsed: 0.109 s
% 0.20/0.51  % (11187)------------------------------
% 0.20/0.51  % (11187)------------------------------
% 0.20/0.51  % (11165)Success in time 0.16 s
%------------------------------------------------------------------------------
