%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:52 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 437 expanded)
%              Number of leaves         :    5 (  98 expanded)
%              Depth                    :   32
%              Number of atoms          :  208 (1805 expanded)
%              Number of equality atoms :  207 (1804 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f218,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f26,f25])).

fof(f25,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f13])).

% (12129)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f13,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : k2_zfmisc_1(k1_xboole_0,X1) = k3_zfmisc_1(X0,k1_xboole_0,X1) ),
    inference(superposition,[],[f20,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f199,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f15,f197])).

fof(f197,plain,(
    k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f190,f29])).

fof(f29,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_zfmisc_1(X3,X4,k1_xboole_0) ),
    inference(superposition,[],[f20,f24])).

fof(f190,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f15,f189])).

fof(f189,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f187,f85])).

fof(f85,plain,(
    k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f84,f15])).

fof(f84,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f83,f32])).

fof(f32,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X2,X3) ),
    inference(forward_demodulation,[],[f27,f25])).

fof(f27,plain,(
    ! [X2,X3] : k3_zfmisc_1(k1_xboole_0,X2,X3) = k2_zfmisc_1(k1_xboole_0,X3) ),
    inference(superposition,[],[f20,f25])).

fof(f83,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(k1_xboole_0,sK4,sK5)
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f14,f75])).

fof(f75,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f74,f15])).

fof(f74,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f73,f31])).

fof(f73,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5)
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f14,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(subsumption_resolution,[],[f67,f15])).

fof(f67,plain,
    ( k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(forward_demodulation,[],[f66,f29])).

fof(f66,plain,
    ( k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0)
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(superposition,[],[f14,f56])).

fof(f56,plain,
    ( k1_xboole_0 = sK5
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 != sK0 ),
    inference(equality_factoring,[],[f46])).

fof(f46,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK4
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = sK5
      | k1_xboole_0 = sK4
      | k1_xboole_0 = sK3
      | sK3 = X0 ) ),
    inference(superposition,[],[f21,f14])).

fof(f21,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( X2 = X5
        & X1 = X4
        & X0 = X3 )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).

fof(f14,plain,(
    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ( sK2 != sK5
      | sK1 != sK4
      | sK0 != sK3 )
    & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
    & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ( X2 != X5
          | X1 != X4
          | X0 != X3 )
        & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) )
   => ( ( sK2 != sK5
        | sK1 != sK4
        | sK0 != sK3 )
      & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)
      & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ( X2 != X5
        | X1 != X4
        | X0 != X3 )
      & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
       => ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)
     => ( ( X2 = X5
          & X1 = X4
          & X0 = X3 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).

fof(f187,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f183])).

fof(f183,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f169,f72])).

fof(f72,plain,
    ( sK0 = sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK2 ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK3 = X0 ) ),
    inference(superposition,[],[f21,f14])).

fof(f169,plain,(
    sK0 != sK3 ),
    inference(subsumption_resolution,[],[f162,f31])).

fof(f162,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,k1_xboole_0,sK2)
    | sK0 != sK3 ),
    inference(superposition,[],[f15,f135])).

fof(f135,plain,
    ( k1_xboole_0 = sK1
    | sK0 != sK3 ),
    inference(subsumption_resolution,[],[f128,f29])).

fof(f128,plain,
    ( k1_xboole_0 != k3_zfmisc_1(sK0,sK1,k1_xboole_0)
    | k1_xboole_0 = sK1
    | sK0 != sK3 ),
    inference(superposition,[],[f15,f113])).

fof(f113,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | sK0 != sK3 ),
    inference(subsumption_resolution,[],[f110,f90])).

fof(f90,plain,
    ( sK1 = sK4
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f89,f85])).

fof(f89,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK1 = sK4 ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK4 = X1 ) ),
    inference(superposition,[],[f22,f14])).

fof(f22,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X1 = X4 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f110,plain,
    ( sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( sK2 != sK2
    | sK1 != sK4
    | sK0 != sK3
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f16,f105])).

fof(f105,plain,
    ( sK2 = sK5
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f104,f85])).

fof(f104,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | sK2 = sK5 ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | sK5 = X2 ) ),
    inference(superposition,[],[f23,f14])).

fof(f23,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | X2 = X5 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f16,plain,
    ( sK2 != sK5
    | sK1 != sK4
    | sK0 != sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f15,plain,(
    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:50:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.20/0.52  % (12146)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.20/0.52  % (12138)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.20/0.52  % (12154)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.20/0.52  % (12141)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.20/0.52  % (12134)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.20/0.52  % (12135)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.20/0.53  % (12138)Refutation found. Thanks to Tanya!
% 1.20/0.53  % SZS status Theorem for theBenchmark
% 1.20/0.53  % (12131)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.20/0.53  % (12130)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.20/0.53  % (12151)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.53  % (12152)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f218,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(subsumption_resolution,[],[f199,f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k1_xboole_0 = k3_zfmisc_1(X0,k1_xboole_0,X1)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f26,f25])).
% 1.34/0.53  fof(f25,plain,(
% 1.34/0.53    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.34/0.53    inference(equality_resolution,[],[f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  % (12129)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.34/0.53    inference(flattening,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.34/0.53    inference(nnf_transformation,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k3_zfmisc_1(X0,k1_xboole_0,X1)) )),
% 1.34/0.53    inference(superposition,[],[f20,f24])).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(equality_resolution,[],[f19])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.34/0.53    inference(cnf_transformation,[],[f13])).
% 1.34/0.53  fof(f20,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.34/0.53  fof(f199,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,k1_xboole_0,sK2)),
% 1.34/0.53    inference(backward_demodulation,[],[f15,f197])).
% 1.34/0.53  fof(f197,plain,(
% 1.34/0.53    k1_xboole_0 = sK1),
% 1.34/0.53    inference(subsumption_resolution,[],[f190,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    ( ! [X4,X3] : (k1_xboole_0 = k3_zfmisc_1(X3,X4,k1_xboole_0)) )),
% 1.34/0.53    inference(superposition,[],[f20,f24])).
% 1.34/0.53  fof(f190,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,k1_xboole_0) | k1_xboole_0 = sK1),
% 1.34/0.53    inference(superposition,[],[f15,f189])).
% 1.34/0.53  fof(f189,plain,(
% 1.34/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.34/0.53    inference(subsumption_resolution,[],[f187,f85])).
% 1.34/0.53  fof(f85,plain,(
% 1.34/0.53    k1_xboole_0 != sK0),
% 1.34/0.53    inference(subsumption_resolution,[],[f84,f15])).
% 1.34/0.53  fof(f84,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 != sK0),
% 1.34/0.53    inference(forward_demodulation,[],[f83,f32])).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ( ! [X2,X3] : (k1_xboole_0 = k3_zfmisc_1(k1_xboole_0,X2,X3)) )),
% 1.34/0.53    inference(forward_demodulation,[],[f27,f25])).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X2,X3] : (k3_zfmisc_1(k1_xboole_0,X2,X3) = k2_zfmisc_1(k1_xboole_0,X3)) )),
% 1.34/0.53    inference(superposition,[],[f20,f25])).
% 1.34/0.53  fof(f83,plain,(
% 1.34/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(k1_xboole_0,sK4,sK5) | k1_xboole_0 != sK0),
% 1.34/0.53    inference(superposition,[],[f14,f75])).
% 1.34/0.53  fof(f75,plain,(
% 1.34/0.53    k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(subsumption_resolution,[],[f74,f15])).
% 1.34/0.53  fof(f74,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(forward_demodulation,[],[f73,f31])).
% 1.34/0.53  fof(f73,plain,(
% 1.34/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,k1_xboole_0,sK5) | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(superposition,[],[f14,f68])).
% 1.34/0.53  fof(f68,plain,(
% 1.34/0.53    k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(subsumption_resolution,[],[f67,f15])).
% 1.34/0.53  fof(f67,plain,(
% 1.34/0.53    k1_xboole_0 = k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(forward_demodulation,[],[f66,f29])).
% 1.34/0.53  fof(f66,plain,(
% 1.34/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,k1_xboole_0) | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(superposition,[],[f14,f56])).
% 1.34/0.53  fof(f56,plain,(
% 1.34/0.53    k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 != sK0),
% 1.34/0.53    inference(equality_factoring,[],[f46])).
% 1.34/0.53  fof(f46,plain,(
% 1.34/0.53    sK0 = sK3 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | k1_xboole_0 = sK5),
% 1.34/0.53    inference(equality_resolution,[],[f36])).
% 1.34/0.53  fof(f36,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = sK5 | k1_xboole_0 = sK4 | k1_xboole_0 = sK3 | sK3 = X0) )),
% 1.34/0.53    inference(superposition,[],[f21,f14])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X0 = X3) )),
% 1.34/0.53    inference(cnf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(flattening,[],[f8])).
% 1.34/0.53  fof(f8,plain,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) | k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_mcart_1)).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    (sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5)),
% 1.34/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f7,f10])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5)) => ((sK2 != sK5 | sK1 != sK4 | sK0 != sK3) & k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2) & k3_zfmisc_1(sK0,sK1,sK2) = k3_zfmisc_1(sK3,sK4,sK5))),
% 1.34/0.53    introduced(choice_axiom,[])).
% 1.34/0.53  fof(f7,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : ((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(flattening,[],[f6])).
% 1.34/0.53  fof(f6,plain,(
% 1.34/0.53    ? [X0,X1,X2,X3,X4,X5] : (((X2 != X5 | X1 != X4 | X0 != X3) & k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)) & k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5))),
% 1.34/0.53    inference(ennf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,negated_conjecture,(
% 1.34/0.53    ~! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.53    inference(negated_conjecture,[],[f4])).
% 1.34/0.53  fof(f4,conjecture,(
% 1.34/0.53    ! [X0,X1,X2,X3,X4,X5] : (k3_zfmisc_1(X0,X1,X2) = k3_zfmisc_1(X3,X4,X5) => ((X2 = X5 & X1 = X4 & X0 = X3) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)))),
% 1.34/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_mcart_1)).
% 1.34/0.53  fof(f187,plain,(
% 1.34/0.53    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f183])).
% 1.34/0.53  fof(f183,plain,(
% 1.34/0.53    sK0 != sK0 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(superposition,[],[f169,f72])).
% 1.34/0.53  fof(f72,plain,(
% 1.34/0.53    sK0 = sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(equality_resolution,[],[f39])).
% 1.34/0.53  fof(f39,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK3 = X0) )),
% 1.34/0.53    inference(superposition,[],[f21,f14])).
% 1.34/0.53  fof(f169,plain,(
% 1.34/0.53    sK0 != sK3),
% 1.34/0.53    inference(subsumption_resolution,[],[f162,f31])).
% 1.34/0.53  fof(f162,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,k1_xboole_0,sK2) | sK0 != sK3),
% 1.34/0.53    inference(superposition,[],[f15,f135])).
% 1.34/0.53  fof(f135,plain,(
% 1.34/0.53    k1_xboole_0 = sK1 | sK0 != sK3),
% 1.34/0.53    inference(subsumption_resolution,[],[f128,f29])).
% 1.34/0.53  fof(f128,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,k1_xboole_0) | k1_xboole_0 = sK1 | sK0 != sK3),
% 1.34/0.53    inference(superposition,[],[f15,f113])).
% 1.34/0.53  fof(f113,plain,(
% 1.34/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | sK0 != sK3),
% 1.34/0.53    inference(subsumption_resolution,[],[f110,f90])).
% 1.34/0.53  fof(f90,plain,(
% 1.34/0.53    sK1 = sK4 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(subsumption_resolution,[],[f89,f85])).
% 1.34/0.53  fof(f89,plain,(
% 1.34/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK1 = sK4),
% 1.34/0.53    inference(equality_resolution,[],[f50])).
% 1.34/0.53  fof(f50,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK4 = X1) )),
% 1.34/0.53    inference(superposition,[],[f22,f14])).
% 1.34/0.53  fof(f22,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X1 = X4) )),
% 1.34/0.53    inference(cnf_transformation,[],[f9])).
% 1.34/0.53  fof(f110,plain,(
% 1.34/0.53    sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f108])).
% 1.34/0.53  fof(f108,plain,(
% 1.34/0.53    sK2 != sK2 | sK1 != sK4 | sK0 != sK3 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(superposition,[],[f16,f105])).
% 1.34/0.53  fof(f105,plain,(
% 1.34/0.53    sK2 = sK5 | k1_xboole_0 = sK1 | k1_xboole_0 = sK2),
% 1.34/0.53    inference(subsumption_resolution,[],[f104,f85])).
% 1.34/0.53  fof(f104,plain,(
% 1.34/0.53    k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | sK2 = sK5),
% 1.34/0.53    inference(equality_resolution,[],[f60])).
% 1.34/0.53  fof(f60,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(sK0,sK1,sK2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | sK5 = X2) )),
% 1.34/0.53    inference(superposition,[],[f23,f14])).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k3_zfmisc_1(X0,X1,X2) != k3_zfmisc_1(X3,X4,X5) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0 | X2 = X5) )),
% 1.34/0.53    inference(cnf_transformation,[],[f9])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    sK2 != sK5 | sK1 != sK4 | sK0 != sK3),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    k1_xboole_0 != k3_zfmisc_1(sK0,sK1,sK2)),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (12138)------------------------------
% 1.34/0.53  % (12138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (12138)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (12138)Memory used [KB]: 1791
% 1.34/0.53  % (12138)Time elapsed: 0.112 s
% 1.34/0.53  % (12138)------------------------------
% 1.34/0.53  % (12138)------------------------------
% 1.34/0.54  % (12128)Success in time 0.172 s
%------------------------------------------------------------------------------
