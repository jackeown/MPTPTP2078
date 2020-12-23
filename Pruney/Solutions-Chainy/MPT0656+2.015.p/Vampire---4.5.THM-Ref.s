%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 257 expanded)
%              Number of leaves         :   10 (  81 expanded)
%              Depth                    :   14
%              Number of atoms          :  213 (1842 expanded)
%              Number of equality atoms :   77 ( 705 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(subsumption_resolution,[],[f282,f33])).

fof(f33,plain,(
    k2_funct_1(sK0) != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_funct_1(sK0) != sK1
    & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
    & k2_relat_1(sK0) = k1_relat_1(sK1)
    & v2_funct_1(sK0)
    & v1_funct_1(sK1)
    & v1_relat_1(sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k2_funct_1(X0) != X1
            & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & k2_relat_1(X0) = k1_relat_1(X1)
            & v2_funct_1(X0)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k2_funct_1(sK0) != X1
          & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
          & k1_relat_1(X1) = k2_relat_1(sK0)
          & v2_funct_1(sK0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( k2_funct_1(sK0) != X1
        & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0))
        & k1_relat_1(X1) = k2_relat_1(sK0)
        & v2_funct_1(sK0)
        & v1_funct_1(X1)
        & v1_relat_1(X1) )
   => ( k2_funct_1(sK0) != sK1
      & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)
      & k2_relat_1(sK0) = k1_relat_1(sK1)
      & v2_funct_1(sK0)
      & v1_funct_1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
          & v2_funct_1(X0)
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k2_funct_1(X0) != X1
          & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
          & k2_relat_1(X0) = k1_relat_1(X1)
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
           => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
                & k2_relat_1(X0) = k1_relat_1(X1)
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
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f282,plain,(
    k2_funct_1(sK0) = sK1 ),
    inference(forward_demodulation,[],[f281,f95])).

fof(f95,plain,(
    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f281,plain,(
    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) ),
    inference(forward_demodulation,[],[f280,f173])).

fof(f173,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f161,f69])).

fof(f69,plain,(
    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) ),
    inference(subsumption_resolution,[],[f68,f27])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f53,f30])).

fof(f30,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f53,plain,
    ( k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f26,f41])).

fof(f41,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f161,plain,(
    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0)))) ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f64,plain,(
    v1_relat_1(k2_funct_1(sK0)) ),
    inference(backward_demodulation,[],[f58,f62])).

fof(f62,plain,(
    k2_funct_1(sK0) = k4_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f61,f27])).

fof(f61,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f51,f30])).

fof(f51,plain,
    ( k2_funct_1(sK0) = k4_relat_1(sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f26,f39])).

fof(f39,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f58,plain,(
    v1_relat_1(k4_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f57,f27])).

fof(f57,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f49,f30])).

fof(f49,plain,
    ( v1_relat_1(k4_relat_1(sK0))
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f26,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k4_relat_1(X0))
        & v1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).

fof(f280,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) ),
    inference(forward_demodulation,[],[f276,f74])).

fof(f74,plain,(
    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f73,f31])).

fof(f31,plain,(
    k2_relat_1(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) ),
    inference(subsumption_resolution,[],[f72,f27])).

fof(f72,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ v1_funct_1(sK0) ),
    inference(subsumption_resolution,[],[f55,f30])).

fof(f55,plain,
    ( k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)
    | ~ v2_funct_1(sK0)
    | ~ v1_funct_1(sK0) ),
    inference(resolution,[],[f26,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f276,plain,(
    k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1) ),
    inference(resolution,[],[f227,f64])).

% (3687)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f227,plain,(
    ! [X4] :
      ( ~ v1_relat_1(X4)
      | k5_relat_1(k5_relat_1(X4,sK0),sK1) = k5_relat_1(X4,k6_relat_1(k1_relat_1(sK0))) ) ),
    inference(forward_demodulation,[],[f225,f32])).

fof(f32,plain,(
    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f225,plain,(
    ! [X4] :
      ( k5_relat_1(k5_relat_1(X4,sK0),sK1) = k5_relat_1(X4,k5_relat_1(sK0,sK1))
      | ~ v1_relat_1(X4) ) ),
    inference(resolution,[],[f47,f28])).

fof(f47,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK0),X3) = k5_relat_1(X2,k5_relat_1(sK0,X3))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n003.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 15:12:57 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.46  % (3685)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  % (3694)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (3696)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (3684)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (3685)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f282,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k2_funct_1(sK0) != sK1),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f24,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X1] : (k2_funct_1(sK0) != X1 & k5_relat_1(sK0,X1) = k6_relat_1(k1_relat_1(sK0)) & k1_relat_1(X1) = k2_relat_1(sK0) & v2_funct_1(sK0) & v1_funct_1(X1) & v1_relat_1(X1)) => (k2_funct_1(sK0) != sK1 & k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1) & k2_relat_1(sK0) = k1_relat_1(sK1) & v2_funct_1(sK0) & v1_funct_1(sK1) & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (k2_funct_1(X0) != X1 & k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X1) & v1_relat_1(X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((k2_funct_1(X0) != X1 & (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0))) & (v1_funct_1(X1) & v1_relat_1(X1))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    k2_funct_1(sK0) = sK1),
% 0.20/0.47    inference(forward_demodulation,[],[f281,f95])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    sK1 = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.47    inference(resolution,[],[f28,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1)),
% 0.20/0.47    inference(forward_demodulation,[],[f280,f173])).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f161,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f68,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    v1_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f53,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v2_funct_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    k1_relat_1(sK0) = k2_relat_1(k2_funct_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(resolution,[],[f26,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    v1_relat_1(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k2_relat_1(k2_funct_1(sK0))))),
% 0.20/0.47    inference(resolution,[],[f64,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    v1_relat_1(k2_funct_1(sK0))),
% 0.20/0.47    inference(backward_demodulation,[],[f58,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k4_relat_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f27])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f51,f30])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    k2_funct_1(sK0) = k4_relat_1(sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(resolution,[],[f26,f39])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    v1_relat_1(k4_relat_1(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f57,f27])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    v1_relat_1(k4_relat_1(sK0)) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f49,f30])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    v1_relat_1(k4_relat_1(sK0)) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(resolution,[],[f26,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k4_relat_1(X0)) & v1_relat_1(k4_relat_1(X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_funct_1)).
% 0.20/0.47  fof(f280,plain,(
% 0.20/0.47    k5_relat_1(k6_relat_1(k1_relat_1(sK1)),sK1) = k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f276,f74])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    k5_relat_1(k2_funct_1(sK0),sK0) = k6_relat_1(k1_relat_1(sK1))),
% 0.20/0.47    inference(forward_demodulation,[],[f73,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    k2_relat_1(sK0) = k1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f72,f27])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f55,f30])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    k6_relat_1(k2_relat_1(sK0)) = k5_relat_1(k2_funct_1(sK0),sK0) | ~v2_funct_1(sK0) | ~v1_funct_1(sK0)),
% 0.20/0.47    inference(resolution,[],[f26,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    k5_relat_1(k2_funct_1(sK0),k6_relat_1(k1_relat_1(sK0))) = k5_relat_1(k5_relat_1(k2_funct_1(sK0),sK0),sK1)),
% 0.20/0.47    inference(resolution,[],[f227,f64])).
% 0.20/0.47  % (3687)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  fof(f227,plain,(
% 0.20/0.47    ( ! [X4] : (~v1_relat_1(X4) | k5_relat_1(k5_relat_1(X4,sK0),sK1) = k5_relat_1(X4,k6_relat_1(k1_relat_1(sK0)))) )),
% 0.20/0.47    inference(forward_demodulation,[],[f225,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    k6_relat_1(k1_relat_1(sK0)) = k5_relat_1(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    ( ! [X4] : (k5_relat_1(k5_relat_1(X4,sK0),sK1) = k5_relat_1(X4,k5_relat_1(sK0,sK1)) | ~v1_relat_1(X4)) )),
% 0.20/0.47    inference(resolution,[],[f47,f28])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK0),X3) = k5_relat_1(X2,k5_relat_1(sK0,X3)) | ~v1_relat_1(X2)) )),
% 0.20/0.47    inference(resolution,[],[f26,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (3685)------------------------------
% 0.20/0.47  % (3685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (3685)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (3685)Memory used [KB]: 1791
% 0.20/0.47  % (3685)Time elapsed: 0.061 s
% 0.20/0.47  % (3685)------------------------------
% 0.20/0.47  % (3685)------------------------------
% 0.20/0.48  % (3673)Success in time 0.13 s
%------------------------------------------------------------------------------
