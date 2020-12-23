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
% DateTime   : Thu Dec  3 12:53:09 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 239 expanded)
%              Number of leaves         :    7 (  42 expanded)
%              Depth                    :   19
%              Number of atoms          :  215 ( 811 expanded)
%              Number of equality atoms :   65 ( 213 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(subsumption_resolution,[],[f319,f23])).

fof(f23,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( k2_funct_1(k2_funct_1(X0)) != X0
      & v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ( v2_funct_1(X0)
         => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f319,plain,(
    ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f318,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f318,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f317,f59])).

fof(f59,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f53,f57])).

fof(f57,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f24,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f56,plain,
    ( ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f41,f23])).

fof(f41,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f53,plain,(
    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f52,f24])).

fof(f52,plain,
    ( ~ v2_funct_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f39,f23])).

fof(f39,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0)) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f317,plain,
    ( k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,
    ( k2_relat_1(sK0) != k2_relat_1(sK0)
    | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k4_relat_1(sK0))
    | ~ v1_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(equality_resolution,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( sK0 != X0
      | k2_relat_1(X0) != k2_relat_1(sK0)
      | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k4_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f134,f43])).

fof(f43,plain,(
    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f22,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f134,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != k2_relat_1(sK0)
      | sK0 != X0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0)) ) ),
    inference(forward_demodulation,[],[f133,f42])).

fof(f42,plain,(
    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0)) ),
    inference(resolution,[],[f22,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f133,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0))
      | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f132,f74])).

fof(f74,plain,(
    v2_funct_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f73,f57])).

fof(f73,plain,(
    v2_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f72,f24])).

fof(f72,plain,
    ( ~ v2_funct_1(sK0)
    | v2_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f48,f23])).

fof(f48,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v2_funct_1(sK0)
    | v2_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f22,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f132,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k4_relat_1(sK0))
      | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0))
      | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f131,f65])).

fof(f65,plain,(
    v1_funct_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f64,f57])).

fof(f64,plain,(
    v1_funct_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f45,f23])).

fof(f45,plain,
    ( ~ v1_funct_1(sK0)
    | v1_funct_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f131,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ v1_funct_1(k4_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k4_relat_1(sK0))
      | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0))
      | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0)) ) ),
    inference(subsumption_resolution,[],[f127,f63])).

fof(f63,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f62,f57])).

fof(f62,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f44,plain,
    ( ~ v1_funct_1(sK0)
    | v1_relat_1(k2_funct_1(sK0)) ),
    inference(resolution,[],[f22,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ v1_relat_1(k4_relat_1(sK0))
      | ~ v1_funct_1(k4_relat_1(sK0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(k4_relat_1(sK0))
      | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0))
      | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0)) ) ),
    inference(superposition,[],[f61,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f61,plain,(
    sK0 != k2_funct_1(k4_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f25,f57])).

fof(f25,plain,(
    sK0 != k2_funct_1(k2_funct_1(sK0)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.22/0.35  % WCLimit    : 600
% 0.22/0.35  % DateTime   : Tue Dec  1 17:09:21 EST 2020
% 0.22/0.35  % CPUTime    : 
% 0.23/0.51  % (26611)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.23/0.52  % (26618)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.23/0.53  % (26606)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.23/0.54  % (26621)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.23/0.55  % (26623)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.23/0.55  % (26623)Refutation found. Thanks to Tanya!
% 0.23/0.55  % SZS status Theorem for theBenchmark
% 0.23/0.55  % SZS output start Proof for theBenchmark
% 0.23/0.55  fof(f320,plain,(
% 0.23/0.55    $false),
% 0.23/0.55    inference(subsumption_resolution,[],[f319,f23])).
% 0.23/0.55  fof(f23,plain,(
% 0.23/0.55    v1_funct_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f10])).
% 0.23/0.55  fof(f10,plain,(
% 0.23/0.55    ? [X0] : (k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.23/0.55    inference(flattening,[],[f9])).
% 0.23/0.55  fof(f9,plain,(
% 0.23/0.55    ? [X0] : ((k2_funct_1(k2_funct_1(X0)) != X0 & v2_funct_1(X0)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.23/0.55    inference(ennf_transformation,[],[f8])).
% 0.23/0.55  fof(f8,negated_conjecture,(
% 0.23/0.55    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.23/0.55    inference(negated_conjecture,[],[f7])).
% 0.23/0.55  fof(f7,conjecture,(
% 0.23/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.23/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 0.23/0.55  fof(f319,plain,(
% 0.23/0.55    ~v1_funct_1(sK0)),
% 0.23/0.55    inference(subsumption_resolution,[],[f318,f22])).
% 0.23/0.55  fof(f22,plain,(
% 0.23/0.55    v1_relat_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f10])).
% 0.23/0.55  fof(f318,plain,(
% 0.23/0.55    ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.23/0.55    inference(subsumption_resolution,[],[f317,f59])).
% 0.23/0.55  fof(f59,plain,(
% 0.23/0.55    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,k4_relat_1(sK0))),
% 0.23/0.55    inference(backward_demodulation,[],[f53,f57])).
% 0.23/0.55  fof(f57,plain,(
% 0.23/0.55    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.23/0.55    inference(subsumption_resolution,[],[f56,f24])).
% 0.23/0.55  fof(f24,plain,(
% 0.23/0.55    v2_funct_1(sK0)),
% 0.23/0.55    inference(cnf_transformation,[],[f10])).
% 0.23/0.55  fof(f56,plain,(
% 0.23/0.55    ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.23/0.55    inference(subsumption_resolution,[],[f41,f23])).
% 0.23/0.55  fof(f41,plain,(
% 0.23/0.55    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.23/0.55    inference(resolution,[],[f22,f29])).
% 0.23/0.55  fof(f29,plain,(
% 0.23/0.55    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 0.23/0.55    inference(cnf_transformation,[],[f16])).
% 0.23/0.55  fof(f16,plain,(
% 0.23/0.55    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.55    inference(flattening,[],[f15])).
% 0.23/0.56  fof(f15,plain,(
% 0.23/0.56    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f2])).
% 0.23/0.56  fof(f2,axiom,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.23/0.56  fof(f53,plain,(
% 0.23/0.56    k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f52,f24])).
% 0.23/0.56  fof(f52,plain,(
% 0.23/0.56    ~v2_funct_1(sK0) | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f39,f23])).
% 0.23/0.56  fof(f39,plain,(
% 0.23/0.56    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | k5_relat_1(sK0,k2_funct_1(sK0)) = k6_relat_1(k1_relat_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f27])).
% 0.23/0.56  fof(f27,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f14])).
% 0.23/0.56  fof(f14,plain,(
% 0.23/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(flattening,[],[f13])).
% 0.23/0.56  fof(f13,plain,(
% 0.23/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f5])).
% 0.23/0.56  fof(f5,axiom,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.23/0.56  fof(f317,plain,(
% 0.23/0.56    k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k4_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.23/0.56    inference(trivial_inequality_removal,[],[f316])).
% 0.23/0.56  fof(f316,plain,(
% 0.23/0.56    k2_relat_1(sK0) != k2_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(sK0,k4_relat_1(sK0)) | ~v1_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.23/0.56    inference(equality_resolution,[],[f135])).
% 0.23/0.56  fof(f135,plain,(
% 0.23/0.56    ( ! [X0] : (sK0 != X0 | k2_relat_1(X0) != k2_relat_1(sK0) | k6_relat_1(k1_relat_1(sK0)) != k5_relat_1(X0,k4_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0)) )),
% 0.23/0.56    inference(forward_demodulation,[],[f134,f43])).
% 0.23/0.56  fof(f43,plain,(
% 0.23/0.56    k1_relat_1(sK0) = k2_relat_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f31])).
% 0.23/0.56  fof(f31,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f17,plain,(
% 0.23/0.56    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(ennf_transformation,[],[f1])).
% 0.23/0.56  fof(f1,axiom,(
% 0.23/0.56    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.23/0.56  fof(f134,plain,(
% 0.23/0.56    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK0) | sK0 != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0))) )),
% 0.23/0.56    inference(forward_demodulation,[],[f133,f42])).
% 0.23/0.56  fof(f42,plain,(
% 0.23/0.56    k2_relat_1(sK0) = k1_relat_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f30])).
% 0.23/0.56  fof(f30,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f17])).
% 0.23/0.56  fof(f133,plain,(
% 0.23/0.56    ( ! [X0] : (sK0 != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0)) | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0))) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f132,f74])).
% 0.23/0.56  fof(f74,plain,(
% 0.23/0.56    v2_funct_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(forward_demodulation,[],[f73,f57])).
% 0.23/0.56  fof(f73,plain,(
% 0.23/0.56    v2_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f72,f24])).
% 0.23/0.56  fof(f72,plain,(
% 0.23/0.56    ~v2_funct_1(sK0) | v2_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f48,f23])).
% 0.23/0.56  fof(f48,plain,(
% 0.23/0.56    ~v1_funct_1(sK0) | ~v2_funct_1(sK0) | v2_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f36])).
% 0.23/0.56  fof(f36,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f21])).
% 0.23/0.56  fof(f21,plain,(
% 0.23/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(flattening,[],[f20])).
% 0.23/0.56  fof(f20,plain,(
% 0.23/0.56    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f4])).
% 0.23/0.56  fof(f4,axiom,(
% 0.23/0.56    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.23/0.56  fof(f132,plain,(
% 0.23/0.56    ( ! [X0] : (sK0 != X0 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k4_relat_1(sK0)) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0)) | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0))) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f131,f65])).
% 0.23/0.56  fof(f65,plain,(
% 0.23/0.56    v1_funct_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(forward_demodulation,[],[f64,f57])).
% 0.23/0.56  fof(f64,plain,(
% 0.23/0.56    v1_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f45,f23])).
% 0.23/0.56  fof(f45,plain,(
% 0.23/0.56    ~v1_funct_1(sK0) | v1_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f33])).
% 0.23/0.56  fof(f33,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f19])).
% 0.23/0.56  fof(f19,plain,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(flattening,[],[f18])).
% 0.23/0.56  fof(f18,plain,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f3])).
% 0.23/0.56  fof(f3,axiom,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.23/0.56  fof(f131,plain,(
% 0.23/0.56    ( ! [X0] : (sK0 != X0 | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k4_relat_1(sK0)) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0)) | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0))) )),
% 0.23/0.56    inference(subsumption_resolution,[],[f127,f63])).
% 0.23/0.56  fof(f63,plain,(
% 0.23/0.56    v1_relat_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(forward_demodulation,[],[f62,f57])).
% 0.23/0.56  fof(f62,plain,(
% 0.23/0.56    v1_relat_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(subsumption_resolution,[],[f44,f23])).
% 0.23/0.56  fof(f44,plain,(
% 0.23/0.56    ~v1_funct_1(sK0) | v1_relat_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(resolution,[],[f22,f32])).
% 0.23/0.56  fof(f32,plain,(
% 0.23/0.56    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.23/0.56    inference(cnf_transformation,[],[f19])).
% 0.23/0.56  fof(f127,plain,(
% 0.23/0.56    ( ! [X0] : (sK0 != X0 | ~v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(k4_relat_1(sK0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(k4_relat_1(sK0)) | k2_relat_1(X0) != k1_relat_1(k4_relat_1(sK0)) | k6_relat_1(k2_relat_1(k4_relat_1(sK0))) != k5_relat_1(X0,k4_relat_1(sK0))) )),
% 0.23/0.56    inference(superposition,[],[f61,f26])).
% 0.23/0.56  fof(f26,plain,(
% 0.23/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 0.23/0.56    inference(cnf_transformation,[],[f12])).
% 0.23/0.56  fof(f12,plain,(
% 0.23/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.23/0.56    inference(flattening,[],[f11])).
% 0.23/0.56  fof(f11,plain,(
% 0.23/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.23/0.56    inference(ennf_transformation,[],[f6])).
% 0.23/0.56  fof(f6,axiom,(
% 0.23/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.23/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 0.23/0.56  fof(f61,plain,(
% 0.23/0.56    sK0 != k2_funct_1(k4_relat_1(sK0))),
% 0.23/0.56    inference(backward_demodulation,[],[f25,f57])).
% 0.23/0.56  fof(f25,plain,(
% 0.23/0.56    sK0 != k2_funct_1(k2_funct_1(sK0))),
% 0.23/0.56    inference(cnf_transformation,[],[f10])).
% 0.23/0.56  % SZS output end Proof for theBenchmark
% 0.23/0.56  % (26623)------------------------------
% 0.23/0.56  % (26623)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.56  % (26623)Termination reason: Refutation
% 0.23/0.56  
% 0.23/0.56  % (26623)Memory used [KB]: 1663
% 0.23/0.56  % (26623)Time elapsed: 0.134 s
% 0.23/0.56  % (26623)------------------------------
% 0.23/0.56  % (26623)------------------------------
% 0.23/0.56  % (26597)Success in time 0.183 s
%------------------------------------------------------------------------------
