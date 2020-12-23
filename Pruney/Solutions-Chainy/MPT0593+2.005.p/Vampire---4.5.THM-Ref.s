%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   29 (  70 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 293 expanded)
%              Number of equality atoms :   42 ( 169 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f11,f21,f47,f22])).

fof(f22,plain,(
    ! [X0] :
      ( sQ2_eqProxy(k1_xboole_0,X0)
      | ~ sQ2_eqProxy(k1_xboole_0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f17,f18,f18])).

fof(f18,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f47,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,sK0) ),
    inference(subsumption_resolution,[],[f46,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != sK1
    & k1_xboole_0 = k2_relat_1(sK1)
    & k1_xboole_0 = k2_relat_1(sK0)
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9,f8])).

fof(f8,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & k1_xboole_0 = k2_relat_1(X1)
            & k1_xboole_0 = k2_relat_1(X0)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(sK0)
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,
    ( ? [X1] :
        ( sK0 != X1
        & k1_xboole_0 = k2_relat_1(X1)
        & k1_xboole_0 = k2_relat_1(sK0)
        & v1_relat_1(X1) )
   => ( sK0 != sK1
      & k1_xboole_0 = k2_relat_1(sK1)
      & k1_xboole_0 = k2_relat_1(sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f4])).

fof(f4,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & k1_xboole_0 = k2_relat_1(X1)
          & k1_xboole_0 = k2_relat_1(X0)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( ( k1_xboole_0 = k2_relat_1(X1)
                & k1_xboole_0 = k2_relat_1(X0) )
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( ( k1_xboole_0 = k2_relat_1(X1)
              & k1_xboole_0 = k2_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).

fof(f46,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,sK0)
    | ~ v1_relat_1(sK1) ),
    inference(subsumption_resolution,[],[f42,f20])).

fof(f20,plain,(
    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f14,f18])).

fof(f14,plain,(
    k1_xboole_0 = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,sK0)
    | ~ sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f36,f22])).

fof(f36,plain,(
    ! [X2] :
      ( ~ sQ2_eqProxy(X2,sK1)
      | ~ sQ2_eqProxy(X2,sK0) ) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f18])).

fof(f32,plain,(
    ! [X0] :
      ( ~ sQ2_eqProxy(sK0,X0)
      | ~ sQ2_eqProxy(X0,sK1) ) ),
    inference(resolution,[],[f29,f19])).

fof(f19,plain,(
    ~ sQ2_eqProxy(sK0,sK1) ),
    inference(equality_proxy_replacement,[],[f15,f18])).

fof(f15,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sQ2_eqProxy(X0,X2)
      | ~ sQ2_eqProxy(X1,X2)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f18])).

fof(f21,plain,(
    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0)) ),
    inference(equality_proxy_replacement,[],[f13,f18])).

fof(f13,plain,(
    k1_xboole_0 = k2_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:37:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.44  % (19628)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.45  % (19636)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.45  % (19628)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f11,f21,f47,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0] : (sQ2_eqProxy(k1_xboole_0,X0) | ~sQ2_eqProxy(k1_xboole_0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f17,f18,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.45    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f6])).
% 0.20/0.45  fof(f6,plain,(
% 0.20/0.45    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ~sQ2_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f46,f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    v1_relat_1(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f5,f9,f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X1] : (sK0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(X1)) => (sK0 != sK1 & k1_xboole_0 = k2_relat_1(sK1) & k1_xboole_0 = k2_relat_1(sK0) & v1_relat_1(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f5,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (X0 != X1 & k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f4])).
% 0.20/0.45  fof(f4,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : ((X0 != X1 & (k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,negated_conjecture,(
% 0.20/0.45    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.20/0.45    inference(negated_conjecture,[],[f2])).
% 0.20/0.45  fof(f2,conjecture,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ((k1_xboole_0 = k2_relat_1(X1) & k1_xboole_0 = k2_relat_1(X0)) => X0 = X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t197_relat_1)).
% 0.20/0.45  fof(f46,plain,(
% 0.20/0.45    ~sQ2_eqProxy(k1_xboole_0,sK0) | ~v1_relat_1(sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f42,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK1))),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f14,f18])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ~sQ2_eqProxy(k1_xboole_0,sK0) | ~sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK1)) | ~v1_relat_1(sK1)),
% 0.20/0.45    inference(resolution,[],[f36,f22])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2] : (~sQ2_eqProxy(X2,sK1) | ~sQ2_eqProxy(X2,sK0)) )),
% 0.20/0.45    inference(resolution,[],[f32,f28])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f18])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0] : (~sQ2_eqProxy(sK0,X0) | ~sQ2_eqProxy(X0,sK1)) )),
% 0.20/0.45    inference(resolution,[],[f29,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ~sQ2_eqProxy(sK0,sK1)),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f15,f18])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    sK0 != sK1),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (sQ2_eqProxy(X0,X2) | ~sQ2_eqProxy(X1,X2) | ~sQ2_eqProxy(X0,X1)) )),
% 0.20/0.45    inference(equality_proxy_axiom,[],[f18])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    sQ2_eqProxy(k1_xboole_0,k2_relat_1(sK0))),
% 0.20/0.45    inference(equality_proxy_replacement,[],[f13,f18])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    k1_xboole_0 = k2_relat_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    v1_relat_1(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (19628)------------------------------
% 0.20/0.45  % (19628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (19628)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (19628)Memory used [KB]: 6140
% 0.20/0.45  % (19628)Time elapsed: 0.047 s
% 0.20/0.45  % (19628)------------------------------
% 0.20/0.45  % (19628)------------------------------
% 0.20/0.45  % (19620)Success in time 0.1 s
%------------------------------------------------------------------------------
