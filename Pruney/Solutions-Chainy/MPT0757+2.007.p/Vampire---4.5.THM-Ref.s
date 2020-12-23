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
% DateTime   : Thu Dec  3 12:55:48 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   25 (  48 expanded)
%              Number of leaves         :    4 (  10 expanded)
%              Depth                    :   13
%              Number of atoms          :   61 ( 168 expanded)
%              Number of equality atoms :    9 (  32 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f10])).

fof(f10,plain,(
    ~ r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_xboole_0(X1,X0)
          & X0 != X1
          & ~ r2_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ~ ( ~ r2_xboole_0(X1,X0)
                & X0 != X1
                & ~ r2_xboole_0(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f56,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(subsumption_resolution,[],[f55,f11])).

fof(f11,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f52,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f52,plain,(
    r1_tarski(sK0,sK1) ),
    inference(subsumption_resolution,[],[f51,f12])).

fof(f12,plain,(
    ~ r2_xboole_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f51,plain,
    ( r1_tarski(sK0,sK1)
    | r2_xboole_0(sK1,sK0) ),
    inference(subsumption_resolution,[],[f50,f11])).

fof(f50,plain,
    ( r1_tarski(sK0,sK1)
    | sK0 = sK1
    | r2_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f32,f17])).

fof(f32,plain,
    ( r1_tarski(sK1,sK0)
    | r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r1_tarski(X1,X0)
      | ~ r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f29,plain,(
    r3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f22,f13])).

fof(f13,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | r3_xboole_0(X0,sK1) ) ),
    inference(resolution,[],[f9,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r3_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).

fof(f9,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.47  % (27310)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.47  % (27310)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % (27301)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.48  % (27316)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f56,f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ~r2_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : ((~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    r2_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f55,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    sK0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    sK0 = sK1 | r2_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f52,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f51,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ~r2_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | r2_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f50,f11])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    r1_tarski(sK0,sK1) | sK0 = sK1 | r2_xboole_0(sK1,sK0)),
% 0.22/0.48    inference(resolution,[],[f32,f17])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    r1_tarski(sK1,sK0) | r1_tarski(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f29,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r1_tarski(X1,X0) | ~r3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    r3_xboole_0(sK0,sK1)),
% 0.22/0.48    inference(resolution,[],[f22,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    v3_ordinal1(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0] : (~v3_ordinal1(X0) | r3_xboole_0(X0,sK1)) )),
% 0.22/0.48    inference(resolution,[],[f9,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r3_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (r3_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => r3_xboole_0(X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_ordinal1)).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    v3_ordinal1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f7])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (27310)------------------------------
% 0.22/0.48  % (27310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (27310)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (27310)Memory used [KB]: 1535
% 0.22/0.48  % (27310)Time elapsed: 0.050 s
% 0.22/0.48  % (27310)------------------------------
% 0.22/0.48  % (27310)------------------------------
% 0.22/0.48  % (27296)Success in time 0.119 s
%------------------------------------------------------------------------------
