%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:01 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 257 expanded)
%              Number of leaves         :   11 (  57 expanded)
%              Depth                    :   23
%              Number of atoms          :  181 ( 801 expanded)
%              Number of equality atoms :   60 ( 383 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f240,plain,(
    $false ),
    inference(global_subsumption,[],[f26,f27,f237])).

fof(f237,plain,
    ( ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f232,f28])).

fof(f28,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f232,plain,(
    ! [X1] :
      ( v5_funct_1(k1_xboole_0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f76,f77,f231])).

fof(f231,plain,(
    ! [X1] :
      ( v5_funct_1(k1_xboole_0,X1)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(forward_demodulation,[],[f230,f58])).

fof(f58,plain,(
    k1_xboole_0 = sK2(k1_xboole_0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK2(X0) ) ),
    inference(global_subsumption,[],[f41,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | ~ v1_relat_1(sK2(X0))
      | k1_xboole_0 = sK2(X0) ) ),
    inference(superposition,[],[f32,f43])).

fof(f43,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f41,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f230,plain,(
    ! [X1] :
      ( ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v5_funct_1(sK2(k1_xboole_0),X1) ) ),
    inference(forward_demodulation,[],[f229,f58])).

fof(f229,plain,(
    ! [X1] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK2(k1_xboole_0))
      | ~ v1_relat_1(X1)
      | v5_funct_1(sK2(k1_xboole_0),X1) ) ),
    inference(forward_demodulation,[],[f227,f58])).

fof(f227,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2(k1_xboole_0))
      | ~ v1_funct_1(sK2(k1_xboole_0))
      | ~ v1_relat_1(X1)
      | v5_funct_1(sK2(k1_xboole_0),X1) ) ),
    inference(resolution,[],[f220,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X1,sK2(X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2(X0))
      | ~ v1_funct_1(sK2(X0))
      | ~ v1_relat_1(X1)
      | v5_funct_1(sK2(X0),X1) ) ),
    inference(superposition,[],[f38,f43])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f220,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(global_subsumption,[],[f77,f219])).

fof(f219,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f218,f75])).

fof(f75,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f43,f58])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(trivial_inequality_removal,[],[f217])).

fof(f217,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f47,f210])).

fof(f210,plain,(
    ! [X0] : k1_xboole_0 = k11_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f104,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f114,f94])).

fof(f94,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f77,f91])).

fof(f91,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f89])).

fof(f89,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f35,f75])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f114,plain,(
    ! [X0] : k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f111,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X1) ),
    inference(forward_demodulation,[],[f81,f52])).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

fof(f81,plain,(
    ! [X1] : k7_relat_1(k1_xboole_0,X1) = k5_relat_1(k6_relat_1(X1),k1_xboole_0) ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f111,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f67,f58])).

fof(f67,plain,(
    ! [X4,X3] : k2_relat_1(k7_relat_1(sK2(X3),X4)) = k9_relat_1(sK2(X3),X4) ),
    inference(resolution,[],[f45,f41])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f104,plain,(
    ! [X0] : k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0)) ),
    inference(superposition,[],[f61,f58])).

fof(f61,plain,(
    ! [X4,X3] : k11_relat_1(sK2(X3),X4) = k9_relat_1(sK2(X3),k1_tarski(X4)) ),
    inference(resolution,[],[f36,f41])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X1,X0) != k1_xboole_0
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k11_relat_1(X1,X0) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f77,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f41,f58])).

fof(f76,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f42,f58])).

fof(f42,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f27,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:59:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (30739)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (30750)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.50  % (30742)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (30737)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (30759)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.51  % (30753)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  % (30741)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (30751)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (30744)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30745)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (30743)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.52  % (30745)Refutation not found, incomplete strategy% (30745)------------------------------
% 0.21/0.52  % (30745)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30745)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30745)Memory used [KB]: 10490
% 0.21/0.52  % (30745)Time elapsed: 0.105 s
% 0.21/0.52  % (30745)------------------------------
% 0.21/0.52  % (30745)------------------------------
% 0.21/0.52  % (30758)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (30738)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.52  % (30753)Refutation not found, incomplete strategy% (30753)------------------------------
% 0.21/0.52  % (30753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30749)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.52  % (30760)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.52  % (30753)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30753)Memory used [KB]: 1663
% 0.21/0.52  % (30753)Time elapsed: 0.105 s
% 0.21/0.52  % (30753)------------------------------
% 0.21/0.52  % (30753)------------------------------
% 0.21/0.52  % (30746)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.52  % (30752)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.32/0.52  % (30747)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.32/0.52  % (30760)Refutation not found, incomplete strategy% (30760)------------------------------
% 1.32/0.52  % (30760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.52  % (30760)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.52  
% 1.32/0.52  % (30760)Memory used [KB]: 10618
% 1.32/0.52  % (30760)Time elapsed: 0.110 s
% 1.32/0.52  % (30760)------------------------------
% 1.32/0.52  % (30760)------------------------------
% 1.32/0.53  % (30747)Refutation not found, incomplete strategy% (30747)------------------------------
% 1.32/0.53  % (30747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (30747)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.53  
% 1.32/0.53  % (30747)Memory used [KB]: 10618
% 1.32/0.53  % (30747)Time elapsed: 0.121 s
% 1.32/0.53  % (30747)------------------------------
% 1.32/0.53  % (30747)------------------------------
% 1.32/0.53  % (30749)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f240,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(global_subsumption,[],[f26,f27,f237])).
% 1.32/0.53  fof(f237,plain,(
% 1.32/0.53    ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 1.32/0.53    inference(resolution,[],[f232,f28])).
% 1.32/0.53  fof(f28,plain,(
% 1.32/0.53    ~v5_funct_1(k1_xboole_0,sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f14,plain,(
% 1.32/0.53    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.32/0.53    inference(flattening,[],[f13])).
% 1.32/0.53  fof(f13,plain,(
% 1.32/0.53    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f12])).
% 1.32/0.53  fof(f12,negated_conjecture,(
% 1.32/0.53    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.32/0.53    inference(negated_conjecture,[],[f11])).
% 1.32/0.53  fof(f11,conjecture,(
% 1.32/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 1.32/0.53  fof(f232,plain,(
% 1.32/0.53    ( ! [X1] : (v5_funct_1(k1_xboole_0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.53    inference(global_subsumption,[],[f76,f77,f231])).
% 1.32/0.53  fof(f231,plain,(
% 1.32/0.53    ( ! [X1] : (v5_funct_1(k1_xboole_0,X1) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f230,f58])).
% 1.32/0.53  fof(f58,plain,(
% 1.32/0.53    k1_xboole_0 = sK2(k1_xboole_0)),
% 1.32/0.53    inference(equality_resolution,[],[f55])).
% 1.32/0.53  fof(f55,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = sK2(X0)) )),
% 1.32/0.53    inference(global_subsumption,[],[f41,f54])).
% 1.32/0.53  fof(f54,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != X0 | ~v1_relat_1(sK2(X0)) | k1_xboole_0 = sK2(X0)) )),
% 1.32/0.53    inference(superposition,[],[f32,f43])).
% 1.32/0.53  fof(f43,plain,(
% 1.32/0.53    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f22,plain,(
% 1.32/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(flattening,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f230,plain,(
% 1.32/0.53    ( ! [X1] : (~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | v5_funct_1(sK2(k1_xboole_0),X1)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f229,f58])).
% 1.32/0.53  fof(f229,plain,(
% 1.32/0.53    ( ! [X1] : (~v1_relat_1(k1_xboole_0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2(k1_xboole_0)) | ~v1_relat_1(X1) | v5_funct_1(sK2(k1_xboole_0),X1)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f227,f58])).
% 1.32/0.53  fof(f227,plain,(
% 1.32/0.53    ( ! [X1] : (~v1_funct_1(X1) | ~v1_relat_1(sK2(k1_xboole_0)) | ~v1_funct_1(sK2(k1_xboole_0)) | ~v1_relat_1(X1) | v5_funct_1(sK2(k1_xboole_0),X1)) )),
% 1.32/0.53    inference(resolution,[],[f220,f79])).
% 1.32/0.53  fof(f79,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK1(X1,sK2(X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(sK2(X0)) | ~v1_funct_1(sK2(X0)) | ~v1_relat_1(X1) | v5_funct_1(sK2(X0),X1)) )),
% 1.32/0.53    inference(superposition,[],[f38,f43])).
% 1.32/0.53  fof(f38,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f21])).
% 1.32/0.53  fof(f21,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(flattening,[],[f20])).
% 1.32/0.53  fof(f20,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.53    inference(ennf_transformation,[],[f9])).
% 1.32/0.53  fof(f9,axiom,(
% 1.32/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 1.32/0.53  fof(f220,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(global_subsumption,[],[f77,f219])).
% 1.32/0.53  fof(f219,plain,(
% 1.32/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f218,f75])).
% 1.32/0.53  fof(f75,plain,(
% 1.32/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(superposition,[],[f43,f58])).
% 1.32/0.53  fof(f218,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f217])).
% 1.32/0.53  fof(f217,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) )),
% 1.32/0.53    inference(superposition,[],[f47,f210])).
% 1.32/0.53  fof(f210,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k11_relat_1(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f104,f115])).
% 1.32/0.53  fof(f115,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f114,f94])).
% 1.32/0.53  fof(f94,plain,(
% 1.32/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(global_subsumption,[],[f77,f91])).
% 1.32/0.53  fof(f91,plain,(
% 1.32/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(trivial_inequality_removal,[],[f89])).
% 1.32/0.53  fof(f89,plain,(
% 1.32/0.53    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(superposition,[],[f35,f75])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f18])).
% 1.32/0.53  fof(f18,plain,(
% 1.32/0.53    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.32/0.53  fof(f114,plain,(
% 1.32/0.53    ( ! [X0] : (k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f111,f85])).
% 1.32/0.53  fof(f85,plain,(
% 1.32/0.53    ( ! [X1] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X1)) )),
% 1.32/0.53    inference(forward_demodulation,[],[f81,f52])).
% 1.32/0.53  fof(f52,plain,(
% 1.32/0.53    ( ! [X0] : (k1_xboole_0 = k5_relat_1(k6_relat_1(X0),k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f31,f29])).
% 1.32/0.53  fof(f29,plain,(
% 1.32/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f2])).
% 1.32/0.53  fof(f2,axiom,(
% 1.32/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f15])).
% 1.32/0.53  fof(f15,plain,(
% 1.32/0.53    ! [X0] : ((k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k5_relat_1(X0,k1_xboole_0) & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).
% 1.32/0.53  fof(f81,plain,(
% 1.32/0.53    ( ! [X1] : (k7_relat_1(k1_xboole_0,X1) = k5_relat_1(k6_relat_1(X1),k1_xboole_0)) )),
% 1.32/0.53    inference(resolution,[],[f77,f44])).
% 1.32/0.53  fof(f44,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f23])).
% 1.32/0.53  fof(f23,plain,(
% 1.32/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f8])).
% 1.32/0.53  fof(f8,axiom,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.32/0.53  fof(f111,plain,(
% 1.32/0.53    ( ! [X0] : (k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0)) )),
% 1.32/0.53    inference(superposition,[],[f67,f58])).
% 1.32/0.53  fof(f67,plain,(
% 1.32/0.53    ( ! [X4,X3] : (k2_relat_1(k7_relat_1(sK2(X3),X4)) = k9_relat_1(sK2(X3),X4)) )),
% 1.32/0.53    inference(resolution,[],[f45,f41])).
% 1.32/0.53  fof(f45,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f24])).
% 1.32/0.53  fof(f24,plain,(
% 1.32/0.53    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f3])).
% 1.32/0.53  fof(f3,axiom,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.32/0.53  fof(f104,plain,(
% 1.32/0.53    ( ! [X0] : (k11_relat_1(k1_xboole_0,X0) = k9_relat_1(k1_xboole_0,k1_tarski(X0))) )),
% 1.32/0.53    inference(superposition,[],[f61,f58])).
% 1.32/0.53  fof(f61,plain,(
% 1.32/0.53    ( ! [X4,X3] : (k11_relat_1(sK2(X3),X4) = k9_relat_1(sK2(X3),k1_tarski(X4))) )),
% 1.32/0.53    inference(resolution,[],[f36,f41])).
% 1.32/0.53  fof(f36,plain,(
% 1.32/0.53    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f19])).
% 1.32/0.53  fof(f19,plain,(
% 1.32/0.53    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.32/0.53    inference(ennf_transformation,[],[f1])).
% 1.32/0.53  fof(f1,axiom,(
% 1.32/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.32/0.53  fof(f47,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k11_relat_1(X1,X0) != k1_xboole_0 | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f25])).
% 1.32/0.53  fof(f25,plain,(
% 1.32/0.53    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0) | ~v1_relat_1(X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f4])).
% 1.32/0.53  fof(f4,axiom,(
% 1.32/0.53    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k11_relat_1(X1,X0) != k1_xboole_0))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.32/0.53  fof(f77,plain,(
% 1.32/0.53    v1_relat_1(k1_xboole_0)),
% 1.32/0.53    inference(superposition,[],[f41,f58])).
% 1.32/0.53  fof(f76,plain,(
% 1.32/0.53    v1_funct_1(k1_xboole_0)),
% 1.32/0.53    inference(superposition,[],[f42,f58])).
% 1.32/0.53  fof(f42,plain,(
% 1.32/0.53    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 1.32/0.53    inference(cnf_transformation,[],[f22])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    v1_funct_1(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  fof(f26,plain,(
% 1.32/0.53    v1_relat_1(sK0)),
% 1.32/0.53    inference(cnf_transformation,[],[f14])).
% 1.32/0.53  % SZS output end Proof for theBenchmark
% 1.32/0.53  % (30749)------------------------------
% 1.32/0.53  % (30749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.53  % (30749)Termination reason: Refutation
% 1.32/0.53  
% 1.32/0.53  % (30749)Memory used [KB]: 10874
% 1.32/0.53  % (30749)Time elapsed: 0.117 s
% 1.32/0.53  % (30749)------------------------------
% 1.32/0.53  % (30749)------------------------------
% 1.32/0.53  % (30757)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 1.32/0.53  % (30736)Success in time 0.168 s
%------------------------------------------------------------------------------
