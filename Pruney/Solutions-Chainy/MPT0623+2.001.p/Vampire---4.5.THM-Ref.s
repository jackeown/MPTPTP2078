%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:02 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   61 (1153 expanded)
%              Number of leaves         :   10 ( 323 expanded)
%              Depth                    :   18
%              Number of atoms          :  129 (2980 expanded)
%              Number of equality atoms :   49 (1167 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f366,plain,(
    $false ),
    inference(global_subsumption,[],[f60,f365])).

fof(f365,plain,(
    k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f363,f362])).

fof(f362,plain,(
    k1_xboole_0 = k1_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f287,f345,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f345,plain,(
    ! [X0] : ~ sP6(X0,sK0) ),
    inference(unit_resulting_resolution,[],[f289,f41])).

fof(f41,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f289,plain,(
    ! [X0] : ~ r2_hidden(X0,sK0) ),
    inference(backward_demodulation,[],[f132,f278])).

fof(f278,plain,(
    ! [X0] : sK3(k1_tarski(X0),sK0) = X0 ),
    inference(unit_resulting_resolution,[],[f133,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f133,plain,(
    ! [X0] : r2_hidden(sK3(k1_tarski(X0),sK0),k1_tarski(X0)) ),
    inference(backward_demodulation,[],[f99,f128])).

fof(f128,plain,(
    ! [X0] : k1_tarski(X0) = k2_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f26,f58])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(global_subsumption,[],[f52,f54,f57])).

fof(f57,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f56,f25])).

fof(f25,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f56,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f21,f24])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f54,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f23,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f52,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f99,plain,(
    ! [X0] : r2_hidden(sK3(k2_relat_1(sK2(sK1,X0)),sK0),k2_relat_1(sK2(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f89,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f89,plain,(
    ! [X0] : ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f63,f61,f83,f21])).

fof(f83,plain,(
    ! [X0] : sK1 = k1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f61,plain,(
    ! [X0] : v1_relat_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,(
    ! [X0] : v1_funct_1(sK2(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_tarski(X0),sK0),sK0) ),
    inference(backward_demodulation,[],[f98,f128])).

fof(f98,plain,(
    ! [X0] : ~ r2_hidden(sK3(k2_relat_1(sK2(sK1,X0)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f287,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f206,f278])).

fof(f206,plain,(
    ! [X0] : ~ r2_hidden(sK3(k1_tarski(X0),sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f132,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f363,plain,(
    sK0 = k1_relat_1(sK0) ),
    inference(unit_resulting_resolution,[],[f289,f345,f45])).

fof(f60,plain,(
    k1_xboole_0 != sK0 ),
    inference(unit_resulting_resolution,[],[f59,f22])).

fof(f22,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:41:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.51  % (21245)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (21231)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (21231)Refutation not found, incomplete strategy% (21231)------------------------------
% 0.22/0.51  % (21231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (21253)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (21244)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.51  % (21254)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.52  % (21236)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (21238)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (21238)Refutation not found, incomplete strategy% (21238)------------------------------
% 0.22/0.52  % (21238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (21238)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21238)Memory used [KB]: 10746
% 0.22/0.52  % (21238)Time elapsed: 0.127 s
% 0.22/0.52  % (21238)------------------------------
% 0.22/0.52  % (21238)------------------------------
% 0.22/0.52  % (21231)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (21231)Memory used [KB]: 10746
% 0.22/0.52  % (21231)Time elapsed: 0.106 s
% 0.22/0.52  % (21231)------------------------------
% 0.22/0.52  % (21231)------------------------------
% 0.22/0.52  % (21229)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (21232)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.53  % (21241)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.28/0.53  % (21234)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (21254)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f366,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(global_subsumption,[],[f60,f365])).
% 1.28/0.54  fof(f365,plain,(
% 1.28/0.54    k1_xboole_0 = sK0),
% 1.28/0.54    inference(backward_demodulation,[],[f363,f362])).
% 1.28/0.54  fof(f362,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relat_1(sK0)),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f287,f345,f45])).
% 1.28/0.54  fof(f45,plain,(
% 1.28/0.54    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.28/0.54    inference(cnf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.28/0.54  fof(f345,plain,(
% 1.28/0.54    ( ! [X0] : (~sP6(X0,sK0)) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f289,f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK7(X0,X2)),X0) | ~sP6(X2,X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f6])).
% 1.28/0.54  fof(f289,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(X0,sK0)) )),
% 1.28/0.54    inference(backward_demodulation,[],[f132,f278])).
% 1.28/0.54  fof(f278,plain,(
% 1.28/0.54    ( ! [X0] : (sK3(k1_tarski(X0),sK0) = X0) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f133,f47])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.28/0.54    inference(equality_resolution,[],[f38])).
% 1.28/0.54  fof(f38,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.28/0.54    inference(cnf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.28/0.54  fof(f133,plain,(
% 1.28/0.54    ( ! [X0] : (r2_hidden(sK3(k1_tarski(X0),sK0),k1_tarski(X0))) )),
% 1.28/0.54    inference(backward_demodulation,[],[f99,f128])).
% 1.28/0.54  fof(f128,plain,(
% 1.28/0.54    ( ! [X0] : (k1_tarski(X0) = k2_relat_1(sK2(sK1,X0))) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f59,f32])).
% 1.28/0.54  fof(f32,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f17])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.28/0.54    inference(ennf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    k1_xboole_0 != sK1),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f26,f58])).
% 1.28/0.54  fof(f58,plain,(
% 1.28/0.54    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0)),
% 1.28/0.54    inference(global_subsumption,[],[f52,f54,f57])).
% 1.28/0.54  fof(f57,plain,(
% 1.28/0.54    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.28/0.54    inference(forward_demodulation,[],[f56,f25])).
% 1.28/0.54  fof(f25,plain,(
% 1.28/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.28/0.54    inference(cnf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.28/0.54  fof(f56,plain,(
% 1.28/0.54    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.28/0.54    inference(superposition,[],[f21,f24])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.28/0.54    inference(cnf_transformation,[],[f7])).
% 1.28/0.54  fof(f21,plain,(
% 1.28/0.54    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f14])).
% 1.28/0.54  fof(f14,plain,(
% 1.28/0.54    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.28/0.54    inference(flattening,[],[f13])).
% 1.28/0.54  fof(f13,plain,(
% 1.28/0.54    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f12])).
% 1.28/0.54  fof(f12,negated_conjecture,(
% 1.28/0.54    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.28/0.54    inference(negated_conjecture,[],[f11])).
% 1.28/0.54  fof(f11,conjecture,(
% 1.28/0.54    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.28/0.54  fof(f54,plain,(
% 1.28/0.54    v1_relat_1(k1_xboole_0)),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f23,f28])).
% 1.28/0.54  fof(f28,plain,(
% 1.28/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    v1_xboole_0(k1_xboole_0)),
% 1.28/0.54    inference(cnf_transformation,[],[f2])).
% 1.28/0.54  fof(f2,axiom,(
% 1.28/0.54    v1_xboole_0(k1_xboole_0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.28/0.54  fof(f52,plain,(
% 1.28/0.54    v1_funct_1(k1_xboole_0)),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f23,f27])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    ( ! [X0] : (~v1_xboole_0(X0) | v1_funct_1(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f15])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_1)).
% 1.28/0.54  fof(f26,plain,(
% 1.28/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f3])).
% 1.28/0.54  fof(f3,axiom,(
% 1.28/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.28/0.54  fof(f99,plain,(
% 1.28/0.54    ( ! [X0] : (r2_hidden(sK3(k2_relat_1(sK2(sK1,X0)),sK0),k2_relat_1(sK2(sK1,X0)))) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f89,f35])).
% 1.28/0.54  fof(f35,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f20,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f89,plain,(
% 1.28/0.54    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f63,f61,f83,f21])).
% 1.28/0.54  fof(f83,plain,(
% 1.28/0.54    ( ! [X0] : (sK1 = k1_relat_1(sK2(sK1,X0))) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f59,f31])).
% 1.28/0.54  fof(f31,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f17])).
% 1.28/0.54  fof(f61,plain,(
% 1.28/0.54    ( ! [X0] : (v1_relat_1(sK2(sK1,X0))) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f59,f29])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f17])).
% 1.28/0.54  fof(f63,plain,(
% 1.28/0.54    ( ! [X0] : (v1_funct_1(sK2(sK1,X0))) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f59,f30])).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f17])).
% 1.28/0.54  fof(f132,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(sK3(k1_tarski(X0),sK0),sK0)) )),
% 1.28/0.54    inference(backward_demodulation,[],[f98,f128])).
% 1.28/0.54  fof(f98,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(sK3(k2_relat_1(sK2(sK1,X0)),sK0),sK0)) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f89,f36])).
% 1.28/0.54  fof(f36,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f287,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.28/0.54    inference(backward_demodulation,[],[f206,f278])).
% 1.28/0.54  fof(f206,plain,(
% 1.28/0.54    ( ! [X0] : (~r2_hidden(sK3(k1_tarski(X0),sK0),k1_xboole_0)) )),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f26,f132,f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f20])).
% 1.28/0.54  fof(f363,plain,(
% 1.28/0.54    sK0 = k1_relat_1(sK0)),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f289,f345,f45])).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    k1_xboole_0 != sK0),
% 1.28/0.54    inference(unit_resulting_resolution,[],[f59,f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.28/0.54    inference(cnf_transformation,[],[f14])).
% 1.28/0.54  % SZS output end Proof for theBenchmark
% 1.28/0.54  % (21254)------------------------------
% 1.28/0.54  % (21254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (21254)Termination reason: Refutation
% 1.28/0.54  
% 1.28/0.54  % (21254)Memory used [KB]: 6524
% 1.28/0.54  % (21254)Time elapsed: 0.121 s
% 1.28/0.54  % (21254)------------------------------
% 1.28/0.54  % (21254)------------------------------
% 1.28/0.54  % (21224)Success in time 0.179 s
%------------------------------------------------------------------------------
