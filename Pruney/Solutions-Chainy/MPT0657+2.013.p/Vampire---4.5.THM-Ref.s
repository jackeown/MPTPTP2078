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
% DateTime   : Thu Dec  3 12:53:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 146 expanded)
%              Number of leaves         :    8 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  144 ( 728 expanded)
%              Number of equality atoms :   60 ( 271 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f149,plain,(
    $false ),
    inference(subsumption_resolution,[],[f148,f94])).

fof(f94,plain,(
    sK1 != k4_relat_1(sK0) ),
    inference(superposition,[],[f26,f61])).

fof(f61,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f60,f27])).

fof(f27,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

% (3542)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
          & k1_relat_1(X0) = k2_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
                & k1_relat_1(X0) = k2_relat_1(X1)
                & v2_funct_1(X0) )
             => k2_funct_1(X0) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f60,plain,
    ( ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f59,f28])).

fof(f28,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f35,f23])).

fof(f23,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f26,plain,(
    sK1 != k2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f148,plain,(
    sK1 = k4_relat_1(sK0) ),
    inference(forward_demodulation,[],[f147,f50])).

fof(f50,plain,(
    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(resolution,[],[f30,f21])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f147,plain,(
    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) ),
    inference(forward_demodulation,[],[f146,f80])).

fof(f80,plain,(
    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f75,f41])).

fof(f41,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f32,f27])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f75,plain,(
    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0)) ),
    inference(resolution,[],[f39,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f39,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f29,f27])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f146,plain,(
    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f142,f66])).

fof(f66,plain,(
    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f65,f24])).

fof(f24,plain,(
    k1_relat_1(sK0) = k2_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f64,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f63,f27])).

fof(f63,plain,
    ( ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f62,f28])).

fof(f62,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0)) ),
    inference(resolution,[],[f36,f23])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f142,plain,(
    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0))) ),
    inference(resolution,[],[f111,f39])).

fof(f111,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(sK1,k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X1) ) ),
    inference(forward_demodulation,[],[f106,f25])).

fof(f25,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,sK0),X1) = k5_relat_1(sK1,k5_relat_1(sK0,X1)) ) ),
    inference(resolution,[],[f71,f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:41:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (3549)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (3543)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (3557)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.48  % (3546)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (3557)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f148,f94])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    sK1 != k4_relat_1(sK0)),
% 0.21/0.48    inference(superposition,[],[f26,f61])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    v1_relat_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  % (3542)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    v1_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.21/0.48    inference(resolution,[],[f35,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    v2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    sK1 != k2_funct_1(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    sK1 = k4_relat_1(sK0)),
% 0.21/0.48    inference(forward_demodulation,[],[f147,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sK1 = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.48    inference(resolution,[],[f30,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v1_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k4_relat_1(sK0) = k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1)))),
% 0.21/0.48    inference(forward_demodulation,[],[f146,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f75,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f32,f27])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    k4_relat_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(k4_relat_1(sK0))),k4_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f39,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_relat_1(k4_relat_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f29,f27])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    k5_relat_1(sK1,k6_relat_1(k2_relat_1(sK1))) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f142,f66])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    k6_relat_1(k2_relat_1(sK1)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f65,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    k1_relat_1(sK0) = k2_relat_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.21/0.48    inference(forward_demodulation,[],[f64,f61])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f63,f27])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f28])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k2_funct_1(sK0))),
% 0.21/0.48    inference(resolution,[],[f36,f23])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    k5_relat_1(k6_relat_1(k2_relat_1(sK0)),k4_relat_1(sK0)) = k5_relat_1(sK1,k5_relat_1(sK0,k4_relat_1(sK0)))),
% 0.21/0.48    inference(resolution,[],[f111,f39])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(sK1,k5_relat_1(sK0,X1)) = k5_relat_1(k6_relat_1(k2_relat_1(sK0)),X1)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f106,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,sK0),X1) = k5_relat_1(sK1,k5_relat_1(sK0,X1))) )),
% 0.21/0.48    inference(resolution,[],[f71,f27])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK1,X0),X1) = k5_relat_1(sK1,k5_relat_1(X0,X1))) )),
% 0.21/0.48    inference(resolution,[],[f34,f21])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (3557)------------------------------
% 0.21/0.48  % (3557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (3557)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (3557)Memory used [KB]: 1791
% 0.21/0.48  % (3557)Time elapsed: 0.060 s
% 0.21/0.48  % (3557)------------------------------
% 0.21/0.48  % (3557)------------------------------
% 0.21/0.48  % (3554)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (3539)Success in time 0.12 s
%------------------------------------------------------------------------------
