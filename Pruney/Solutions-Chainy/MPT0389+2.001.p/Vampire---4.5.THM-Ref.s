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
% DateTime   : Thu Dec  3 12:45:46 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   37 (  51 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :   13
%              Number of atoms          :  108 ( 162 expanded)
%              Number of equality atoms :   30 (  44 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f140,plain,(
    $false ),
    inference(subsumption_resolution,[],[f139,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      & k1_xboole_0 != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f139,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f138,f17])).

fof(f17,plain,(
    ~ r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f138,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0
    | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) ),
    inference(resolution,[],[f77,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ? [X2] :
          ( ~ r1_tarski(X1,X2)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X1,X2) )
     => ( r1_tarski(X1,k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).

fof(f77,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK2(X1,k1_setfam_1(sK1)),sK0)
      | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(X1))
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,k1_setfam_1(X1)),X1)
      | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_setfam_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(X0,X1))
      | k1_xboole_0 = X0
      | r1_tarski(X1,k1_setfam_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2] :
      ( r2_hidden(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(superposition,[],[f36,f65])).

fof(f65,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f61,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f60,f33])).

fof(f33,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f26,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK3(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (27892)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (27872)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (27880)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.29/0.52  % (27883)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.29/0.52  % (27889)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.29/0.53  % (27889)Refutation found. Thanks to Tanya!
% 1.29/0.53  % SZS status Theorem for theBenchmark
% 1.47/0.54  % (27876)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.47/0.54  % SZS output start Proof for theBenchmark
% 1.47/0.54  fof(f140,plain,(
% 1.47/0.54    $false),
% 1.47/0.54    inference(subsumption_resolution,[],[f139,f16])).
% 1.47/0.54  fof(f16,plain,(
% 1.47/0.54    k1_xboole_0 != sK0),
% 1.47/0.54    inference(cnf_transformation,[],[f9])).
% 1.47/0.54  fof(f9,plain,(
% 1.47/0.54    ? [X0,X1] : (~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0 & r1_tarski(X0,X1))),
% 1.47/0.54    inference(flattening,[],[f8])).
% 1.47/0.54  fof(f8,plain,(
% 1.47/0.54    ? [X0,X1] : ((~r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) & k1_xboole_0 != X0) & r1_tarski(X0,X1))),
% 1.47/0.54    inference(ennf_transformation,[],[f7])).
% 1.47/0.54  fof(f7,negated_conjecture,(
% 1.47/0.54    ~! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.47/0.54    inference(negated_conjecture,[],[f6])).
% 1.47/0.54  fof(f6,conjecture,(
% 1.47/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.47/0.54  fof(f139,plain,(
% 1.47/0.54    k1_xboole_0 = sK0),
% 1.47/0.54    inference(subsumption_resolution,[],[f138,f17])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    ~r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 1.47/0.54    inference(cnf_transformation,[],[f9])).
% 1.47/0.54  fof(f138,plain,(
% 1.47/0.54    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0),
% 1.47/0.54    inference(duplicate_literal_removal,[],[f137])).
% 1.47/0.54  fof(f137,plain,(
% 1.47/0.54    r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0)) | k1_xboole_0 = sK0 | k1_xboole_0 = sK0 | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(sK0))),
% 1.47/0.54    inference(resolution,[],[f77,f19])).
% 1.47/0.54  fof(f19,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f12])).
% 1.47/0.54  fof(f12,plain,(
% 1.47/0.54    ! [X0,X1] : (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0 | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.47/0.54    inference(flattening,[],[f11])).
% 1.47/0.54  fof(f11,plain,(
% 1.47/0.54    ! [X0,X1] : ((r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0) | ? [X2] : (~r1_tarski(X1,X2) & r2_hidden(X2,X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f5])).
% 1.47/0.54  fof(f5,axiom,(
% 1.47/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X1,X2)) => (r1_tarski(X1,k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_setfam_1)).
% 1.47/0.54  fof(f77,plain,(
% 1.47/0.54    ( ! [X1] : (~r2_hidden(sK2(X1,k1_setfam_1(sK1)),sK0) | r1_tarski(k1_setfam_1(sK1),k1_setfam_1(X1)) | k1_xboole_0 = X1) )),
% 1.47/0.54    inference(resolution,[],[f70,f48])).
% 1.47/0.54  fof(f48,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r2_hidden(sK2(X0,k1_setfam_1(X1)),X1) | r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) )),
% 1.47/0.54    inference(resolution,[],[f20,f18])).
% 1.47/0.54  fof(f18,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f10])).
% 1.47/0.54  fof(f10,plain,(
% 1.47/0.54    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),X0) | ~r2_hidden(X0,X1))),
% 1.47/0.54    inference(ennf_transformation,[],[f4])).
% 1.47/0.54  fof(f4,axiom,(
% 1.47/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_setfam_1(X1),X0))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).
% 1.47/0.54  fof(f20,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r1_tarski(X1,sK2(X0,X1)) | k1_xboole_0 = X0 | r1_tarski(X1,k1_setfam_1(X0))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f12])).
% 1.47/0.54  fof(f70,plain,(
% 1.47/0.54    ( ! [X2] : (r2_hidden(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 1.47/0.54    inference(superposition,[],[f36,f65])).
% 1.47/0.54  fof(f65,plain,(
% 1.47/0.54    sK0 = k3_xboole_0(sK0,sK1)),
% 1.47/0.54    inference(resolution,[],[f61,f15])).
% 1.47/0.54  fof(f15,plain,(
% 1.47/0.54    r1_tarski(sK0,sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f9])).
% 1.47/0.54  fof(f61,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f60,f33])).
% 1.47/0.54  fof(f33,plain,(
% 1.47/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.47/0.54    inference(equality_resolution,[],[f22])).
% 1.47/0.54  fof(f22,plain,(
% 1.47/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.47/0.54    inference(cnf_transformation,[],[f2])).
% 1.47/0.54  fof(f2,axiom,(
% 1.47/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.47/0.54  fof(f60,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.54    inference(duplicate_literal_removal,[],[f57])).
% 1.47/0.54  fof(f57,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k3_xboole_0(X0,X1) = X0) )),
% 1.47/0.54    inference(resolution,[],[f26,f24])).
% 1.47/0.54  fof(f24,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 1.47/0.54    inference(cnf_transformation,[],[f14])).
% 1.47/0.54  fof(f14,plain,(
% 1.47/0.54    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.47/0.54    inference(flattening,[],[f13])).
% 1.47/0.54  fof(f13,plain,(
% 1.47/0.54    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.47/0.54    inference(ennf_transformation,[],[f3])).
% 1.47/0.54  fof(f3,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).
% 1.47/0.54  fof(f26,plain,(
% 1.47/0.54    ( ! [X2,X0,X1] : (~r1_tarski(sK3(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k3_xboole_0(X1,X2) = X0) )),
% 1.47/0.54    inference(cnf_transformation,[],[f14])).
% 1.47/0.54  fof(f36,plain,(
% 1.47/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k3_xboole_0(X0,X1)) | r2_hidden(X3,X1)) )),
% 1.47/0.54    inference(equality_resolution,[],[f31])).
% 1.47/0.54  fof(f31,plain,(
% 1.47/0.54    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.47/0.54    inference(cnf_transformation,[],[f1])).
% 1.47/0.54  fof(f1,axiom,(
% 1.47/0.54    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.47/0.54  % SZS output end Proof for theBenchmark
% 1.47/0.54  % (27889)------------------------------
% 1.47/0.54  % (27889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (27889)Termination reason: Refutation
% 1.47/0.54  
% 1.47/0.54  % (27889)Memory used [KB]: 1791
% 1.47/0.54  % (27889)Time elapsed: 0.093 s
% 1.47/0.54  % (27889)------------------------------
% 1.47/0.54  % (27889)------------------------------
% 1.47/0.55  % (27864)Success in time 0.187 s
%------------------------------------------------------------------------------
