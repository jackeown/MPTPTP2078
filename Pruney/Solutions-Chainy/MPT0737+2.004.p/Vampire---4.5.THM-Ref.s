%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:17 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   35 (  90 expanded)
%              Number of leaves         :    6 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 299 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(global_subsumption,[],[f51,f61])).

fof(f61,plain,(
    r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f17,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r3_xboole_0(sK0,sK1)
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_xboole_0(X0,X1)
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ~ r3_xboole_0(sK0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( ~ r3_xboole_0(sK0,X1)
        & v3_ordinal1(X1) )
   => ( ~ r3_xboole_0(sK0,sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_xboole_0(X0,X1)
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => r3_xboole_0(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => r3_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).

fof(f60,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f58,f18])).

fof(f18,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,
    ( r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f45,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f45,plain,(
    ~ r1_ordinal1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f44,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(subsumption_resolution,[],[f42,f18])).

fof(f42,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0) ),
    inference(resolution,[],[f38,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f38,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(resolution,[],[f19,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r3_xboole_0(X0,X1)
        | ( ~ r1_tarski(X1,X0)
          & ~ r1_tarski(X0,X1) ) )
      & ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1)
        | ~ r3_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
    <=> ( r1_tarski(X1,X0)
        | r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).

fof(f19,plain,(
    ~ r3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,(
    ~ r1_ordinal1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f50,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(subsumption_resolution,[],[f48,f17])).

fof(f48,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1) ),
    inference(resolution,[],[f39,f21])).

fof(f39,plain,(
    ~ r1_tarski(sK1,sK0) ),
    inference(resolution,[],[f19,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r3_xboole_0(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.36  ipcrm: permission denied for id (818216960)
% 0.19/0.36  ipcrm: permission denied for id (818282499)
% 0.19/0.37  ipcrm: permission denied for id (818348039)
% 0.19/0.37  ipcrm: permission denied for id (818380809)
% 0.19/0.37  ipcrm: permission denied for id (818446348)
% 0.19/0.38  ipcrm: permission denied for id (818479121)
% 0.19/0.38  ipcrm: permission denied for id (818511891)
% 0.19/0.38  ipcrm: permission denied for id (818544662)
% 0.19/0.41  ipcrm: permission denied for id (818741290)
% 0.19/0.41  ipcrm: permission denied for id (818774059)
% 0.19/0.41  ipcrm: permission denied for id (818806833)
% 0.19/0.43  ipcrm: permission denied for id (818872386)
% 0.19/0.44  ipcrm: permission denied for id (818937925)
% 0.19/0.44  ipcrm: permission denied for id (819003467)
% 0.19/0.44  ipcrm: permission denied for id (819036236)
% 0.19/0.45  ipcrm: permission denied for id (819167315)
% 0.19/0.46  ipcrm: permission denied for id (819265627)
% 0.19/0.47  ipcrm: permission denied for id (819331170)
% 0.19/0.47  ipcrm: permission denied for id (819396711)
% 0.19/0.48  ipcrm: permission denied for id (819429482)
% 0.19/0.48  ipcrm: permission denied for id (819527791)
% 0.19/0.49  ipcrm: permission denied for id (819560562)
% 0.19/0.50  ipcrm: permission denied for id (819593338)
% 0.19/0.50  ipcrm: permission denied for id (819626109)
% 0.99/0.61  % (16207)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.99/0.61  % (16207)Refutation found. Thanks to Tanya!
% 0.99/0.61  % SZS status Theorem for theBenchmark
% 0.99/0.61  % SZS output start Proof for theBenchmark
% 0.99/0.61  fof(f62,plain,(
% 0.99/0.61    $false),
% 0.99/0.61    inference(global_subsumption,[],[f51,f61])).
% 0.99/0.61  fof(f61,plain,(
% 0.99/0.61    r1_ordinal1(sK1,sK0)),
% 0.99/0.61    inference(subsumption_resolution,[],[f60,f17])).
% 0.99/0.61  fof(f17,plain,(
% 0.99/0.61    v3_ordinal1(sK0)),
% 0.99/0.61    inference(cnf_transformation,[],[f13])).
% 0.99/0.61  fof(f13,plain,(
% 0.99/0.61    (~r3_xboole_0(sK0,sK1) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.99/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.99/0.61  fof(f11,plain,(
% 0.99/0.61    ? [X0] : (? [X1] : (~r3_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (~r3_xboole_0(sK0,X1) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.99/0.61    introduced(choice_axiom,[])).
% 0.99/0.61  fof(f12,plain,(
% 0.99/0.61    ? [X1] : (~r3_xboole_0(sK0,X1) & v3_ordinal1(X1)) => (~r3_xboole_0(sK0,sK1) & v3_ordinal1(sK1))),
% 0.99/0.61    introduced(choice_axiom,[])).
% 0.99/0.61  fof(f6,plain,(
% 0.99/0.61    ? [X0] : (? [X1] : (~r3_xboole_0(X0,X1) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.99/0.61    inference(ennf_transformation,[],[f5])).
% 0.99/0.61  fof(f5,negated_conjecture,(
% 0.99/0.61    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => r3_xboole_0(X0,X1)))),
% 0.99/0.61    inference(negated_conjecture,[],[f4])).
% 0.99/0.61  fof(f4,conjecture,(
% 0.99/0.61    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => r3_xboole_0(X0,X1)))),
% 0.99/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_ordinal1)).
% 0.99/0.61  fof(f60,plain,(
% 0.99/0.61    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0)),
% 0.99/0.61    inference(subsumption_resolution,[],[f58,f18])).
% 0.99/0.61  fof(f18,plain,(
% 0.99/0.61    v3_ordinal1(sK1)),
% 0.99/0.61    inference(cnf_transformation,[],[f13])).
% 0.99/0.61  fof(f58,plain,(
% 0.99/0.61    r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.99/0.61    inference(resolution,[],[f45,f20])).
% 0.99/0.61  fof(f20,plain,(
% 0.99/0.61    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.99/0.61    inference(cnf_transformation,[],[f8])).
% 0.99/0.61  fof(f8,plain,(
% 0.99/0.61    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.99/0.61    inference(flattening,[],[f7])).
% 0.99/0.61  fof(f7,plain,(
% 0.99/0.61    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.99/0.61    inference(ennf_transformation,[],[f2])).
% 0.99/0.61  fof(f2,axiom,(
% 0.99/0.61    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.99/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.99/0.61  fof(f45,plain,(
% 0.99/0.61    ~r1_ordinal1(sK0,sK1)),
% 0.99/0.61    inference(subsumption_resolution,[],[f44,f17])).
% 0.99/0.61  fof(f44,plain,(
% 0.99/0.61    ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK0)),
% 0.99/0.61    inference(subsumption_resolution,[],[f42,f18])).
% 0.99/0.61  fof(f42,plain,(
% 0.99/0.61    ~r1_ordinal1(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0)),
% 0.99/0.61    inference(resolution,[],[f38,f21])).
% 0.99/0.61  fof(f21,plain,(
% 0.99/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.99/0.61    inference(cnf_transformation,[],[f14])).
% 0.99/0.61  fof(f14,plain,(
% 0.99/0.61    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.99/0.61    inference(nnf_transformation,[],[f10])).
% 0.99/0.61  fof(f10,plain,(
% 0.99/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.99/0.61    inference(flattening,[],[f9])).
% 0.99/0.61  fof(f9,plain,(
% 0.99/0.61    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.99/0.61    inference(ennf_transformation,[],[f3])).
% 0.99/0.61  fof(f3,axiom,(
% 0.99/0.61    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.99/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.99/0.61  fof(f38,plain,(
% 0.99/0.61    ~r1_tarski(sK0,sK1)),
% 0.99/0.61    inference(resolution,[],[f19,f24])).
% 0.99/0.61  fof(f24,plain,(
% 0.99/0.61    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.99/0.61    inference(cnf_transformation,[],[f16])).
% 0.99/0.61  fof(f16,plain,(
% 0.99/0.61    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & (r1_tarski(X1,X0) | r1_tarski(X0,X1) | ~r3_xboole_0(X0,X1)))),
% 0.99/0.61    inference(flattening,[],[f15])).
% 0.99/0.61  fof(f15,plain,(
% 0.99/0.61    ! [X0,X1] : ((r3_xboole_0(X0,X1) | (~r1_tarski(X1,X0) & ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) | r1_tarski(X0,X1)) | ~r3_xboole_0(X0,X1)))),
% 0.99/0.61    inference(nnf_transformation,[],[f1])).
% 0.99/0.61  fof(f1,axiom,(
% 0.99/0.61    ! [X0,X1] : (r3_xboole_0(X0,X1) <=> (r1_tarski(X1,X0) | r1_tarski(X0,X1)))),
% 0.99/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_xboole_0)).
% 0.99/0.61  fof(f19,plain,(
% 0.99/0.61    ~r3_xboole_0(sK0,sK1)),
% 0.99/0.61    inference(cnf_transformation,[],[f13])).
% 0.99/0.61  fof(f51,plain,(
% 0.99/0.61    ~r1_ordinal1(sK1,sK0)),
% 0.99/0.61    inference(subsumption_resolution,[],[f50,f18])).
% 0.99/0.61  fof(f50,plain,(
% 0.99/0.61    ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK1)),
% 0.99/0.61    inference(subsumption_resolution,[],[f48,f17])).
% 0.99/0.61  fof(f48,plain,(
% 0.99/0.61    ~r1_ordinal1(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1)),
% 0.99/0.61    inference(resolution,[],[f39,f21])).
% 0.99/0.61  fof(f39,plain,(
% 0.99/0.61    ~r1_tarski(sK1,sK0)),
% 0.99/0.61    inference(resolution,[],[f19,f25])).
% 0.99/0.61  fof(f25,plain,(
% 0.99/0.61    ( ! [X0,X1] : (r3_xboole_0(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.99/0.61    inference(cnf_transformation,[],[f16])).
% 0.99/0.61  % SZS output end Proof for theBenchmark
% 0.99/0.61  % (16207)------------------------------
% 0.99/0.61  % (16207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.99/0.61  % (16207)Termination reason: Refutation
% 0.99/0.61  
% 0.99/0.61  % (16207)Memory used [KB]: 5373
% 0.99/0.61  % (16207)Time elapsed: 0.066 s
% 0.99/0.61  % (16207)------------------------------
% 0.99/0.61  % (16207)------------------------------
% 0.99/0.61  % (16051)Success in time 0.257 s
%------------------------------------------------------------------------------
