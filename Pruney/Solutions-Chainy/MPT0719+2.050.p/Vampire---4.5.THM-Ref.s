%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:02 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   58 (1304 expanded)
%              Number of leaves         :    7 ( 307 expanded)
%              Depth                    :   23
%              Number of atoms          :  156 (3823 expanded)
%              Number of equality atoms :   33 ( 954 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(subsumption_resolution,[],[f126,f112])).

fof(f112,plain,(
    ! [X0,X1] : ~ v5_funct_1(X1,X0) ),
    inference(superposition,[],[f71,f58])).

fof(f58,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f54,f54])).

fof(f54,plain,(
    ! [X0] : k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0 ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f16,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK0)
      | k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0 ) ),
    inference(subsumption_resolution,[],[f52,f17])).

fof(f17,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0)
      | k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0 ) ),
    inference(resolution,[],[f51,f18])).

fof(f18,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v5_funct_1(k1_xboole_0,X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_funct_1(k1_xboole_0,sK1(X0,k1_xboole_0)) = X1 ) ),
    inference(forward_demodulation,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = sK2(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK2(X0,X1) ) ),
    inference(subsumption_resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = sK2(X0,X1) ) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0)
      | k1_funct_1(sK2(k1_xboole_0,X1),sK1(X0,k1_xboole_0)) = X1 ) ),
    inference(resolution,[],[f47,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK2(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f47,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f46,f33])).

fof(f33,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f23,f19])).

fof(f19,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f23,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f44,f34])).

fof(f34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f22,f19])).

fof(f22,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f27,f20])).

fof(f20,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f71,plain,(
    ! [X0] : ~ v5_funct_1(X0,sK0) ),
    inference(superposition,[],[f18,f58])).

fof(f126,plain,(
    ! [X0,X1] : v5_funct_1(X1,X0) ),
    inference(subsumption_resolution,[],[f125,f73])).

fof(f73,plain,(
    ! [X0] : v1_relat_1(X0) ),
    inference(superposition,[],[f34,f58])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f124,f72])).

fof(f72,plain,(
    ! [X0] : v1_funct_1(X0) ),
    inference(superposition,[],[f33,f58])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f123,f73])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(subsumption_resolution,[],[f116,f72])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(resolution,[],[f28,f114])).

fof(f114,plain,(
    ! [X0,X1] : r2_hidden(X1,X0) ),
    inference(superposition,[],[f111,f58])).

fof(f111,plain,(
    ! [X1] : r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f110,f78])).

fof(f78,plain,(
    ! [X0] : ~ v5_funct_1(k1_xboole_0,X0) ),
    inference(superposition,[],[f18,f58])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f109,f73])).

fof(f109,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f82,f72])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_xboole_0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v5_funct_1(k1_xboole_0,X0) ) ),
    inference(superposition,[],[f47,f58])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v5_funct_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (25388)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (25389)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (25390)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (25384)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (25401)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.50  % (25404)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.50  % (25405)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (25401)Refutation not found, incomplete strategy% (25401)------------------------------
% 0.21/0.51  % (25401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25401)Memory used [KB]: 1663
% 0.21/0.51  % (25401)Time elapsed: 0.098 s
% 0.21/0.51  % (25401)------------------------------
% 0.21/0.51  % (25401)------------------------------
% 0.21/0.51  % (25385)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 1.25/0.51  % (25402)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 1.25/0.51  % (25392)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.25/0.51  % (25394)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 1.25/0.51  % (25397)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 1.25/0.51  % (25392)Refutation not found, incomplete strategy% (25392)------------------------------
% 1.25/0.51  % (25392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.51  % (25392)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.51  
% 1.25/0.51  % (25392)Memory used [KB]: 10490
% 1.25/0.51  % (25392)Time elapsed: 0.109 s
% 1.25/0.51  % (25392)------------------------------
% 1.25/0.51  % (25392)------------------------------
% 1.25/0.51  % (25393)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.25/0.51  % (25394)Refutation not found, incomplete strategy% (25394)------------------------------
% 1.25/0.51  % (25394)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.51  % (25394)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.51  
% 1.25/0.51  % (25394)Memory used [KB]: 10618
% 1.25/0.51  % (25394)Time elapsed: 0.108 s
% 1.25/0.51  % (25394)------------------------------
% 1.25/0.51  % (25394)------------------------------
% 1.25/0.51  % (25397)Refutation found. Thanks to Tanya!
% 1.25/0.51  % SZS status Theorem for theBenchmark
% 1.25/0.51  % (25398)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.25/0.52  % (25407)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 1.25/0.52  % (25399)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 1.25/0.52  % (25396)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.25/0.52  % (25400)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.25/0.52  % (25407)Refutation not found, incomplete strategy% (25407)------------------------------
% 1.25/0.52  % (25407)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (25407)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (25407)Memory used [KB]: 10618
% 1.25/0.52  % (25407)Time elapsed: 0.108 s
% 1.25/0.52  % (25407)------------------------------
% 1.25/0.52  % (25407)------------------------------
% 1.25/0.52  % (25391)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.25/0.52  % (25400)Refutation not found, incomplete strategy% (25400)------------------------------
% 1.25/0.52  % (25400)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (25400)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (25400)Memory used [KB]: 1663
% 1.25/0.52  % (25400)Time elapsed: 0.113 s
% 1.25/0.52  % (25400)------------------------------
% 1.25/0.52  % (25400)------------------------------
% 1.25/0.52  % (25391)Refutation not found, incomplete strategy% (25391)------------------------------
% 1.25/0.52  % (25391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (25391)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (25391)Memory used [KB]: 6012
% 1.25/0.52  % (25391)Time elapsed: 0.083 s
% 1.25/0.52  % (25391)------------------------------
% 1.25/0.52  % (25391)------------------------------
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f127,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(subsumption_resolution,[],[f126,f112])).
% 1.25/0.52  fof(f112,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(superposition,[],[f71,f58])).
% 1.25/0.52  fof(f58,plain,(
% 1.25/0.52    ( ! [X0,X1] : (X0 = X1) )),
% 1.25/0.52    inference(superposition,[],[f54,f54])).
% 1.25/0.52  fof(f54,plain,(
% 1.25/0.52    ( ! [X0] : (k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f53,f16])).
% 1.25/0.52  fof(f16,plain,(
% 1.25/0.52    v1_relat_1(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f10])).
% 1.25/0.52  fof(f10,plain,(
% 1.25/0.52    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f9])).
% 1.25/0.52  fof(f9,plain,(
% 1.25/0.52    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f8])).
% 1.25/0.52  fof(f8,negated_conjecture,(
% 1.25/0.52    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.25/0.52    inference(negated_conjecture,[],[f7])).
% 1.25/0.52  fof(f7,conjecture,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 1.25/0.52  fof(f53,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_relat_1(sK0) | k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f52,f17])).
% 1.25/0.52  fof(f17,plain,(
% 1.25/0.52    v1_funct_1(sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f10])).
% 1.25/0.52  fof(f52,plain,(
% 1.25/0.52    ( ! [X0] : (~v1_funct_1(sK0) | ~v1_relat_1(sK0) | k1_funct_1(k1_xboole_0,sK1(sK0,k1_xboole_0)) = X0) )),
% 1.25/0.52    inference(resolution,[],[f51,f18])).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    ~v5_funct_1(k1_xboole_0,sK0)),
% 1.25/0.52    inference(cnf_transformation,[],[f10])).
% 1.25/0.52  fof(f51,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v5_funct_1(k1_xboole_0,X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(k1_xboole_0,sK1(X0,k1_xboole_0)) = X1) )),
% 1.25/0.52    inference(forward_demodulation,[],[f50,f38])).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    ( ! [X0] : (k1_xboole_0 = sK2(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(equality_resolution,[],[f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK2(X0,X1)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f36,f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,plain,(
% 1.25/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,axiom,(
% 1.25/0.52    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.25/0.52  fof(f36,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = sK2(X0,X1)) )),
% 1.25/0.52    inference(superposition,[],[f24,f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f24,plain,(
% 1.25/0.52    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.25/0.52    inference(cnf_transformation,[],[f12])).
% 1.25/0.52  fof(f12,plain,(
% 1.25/0.52    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f11])).
% 1.25/0.52  fof(f11,plain,(
% 1.25/0.52    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0) | k1_funct_1(sK2(k1_xboole_0,X1),sK1(X0,k1_xboole_0)) = X1) )),
% 1.25/0.52    inference(resolution,[],[f47,f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK2(X0,X1),X3) = X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f47,plain,(
% 1.25/0.52    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f46,f33])).
% 1.25/0.52  fof(f33,plain,(
% 1.25/0.52    v1_funct_1(k1_xboole_0)),
% 1.25/0.52    inference(superposition,[],[f23,f19])).
% 1.25/0.52  fof(f19,plain,(
% 1.25/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.25/0.52    inference(cnf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f5])).
% 1.25/0.52  fof(f5,axiom,(
% 1.25/0.52    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 1.25/0.52  fof(f46,plain,(
% 1.25/0.52    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f44,f34])).
% 1.25/0.52  fof(f34,plain,(
% 1.25/0.52    v1_relat_1(k1_xboole_0)),
% 1.25/0.52    inference(superposition,[],[f22,f19])).
% 1.25/0.52  fof(f22,plain,(
% 1.25/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.25/0.52    inference(cnf_transformation,[],[f5])).
% 1.25/0.52  fof(f44,plain,(
% 1.25/0.52    ( ! [X0] : (r2_hidden(sK1(X0,k1_xboole_0),k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(superposition,[],[f27,f20])).
% 1.25/0.52  fof(f20,plain,(
% 1.25/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/0.52    inference(cnf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f14])).
% 1.25/0.52  fof(f14,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.25/0.52    inference(flattening,[],[f13])).
% 1.25/0.52  fof(f13,plain,(
% 1.25/0.52    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.25/0.52    inference(ennf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 1.25/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 1.25/0.52  fof(f71,plain,(
% 1.25/0.52    ( ! [X0] : (~v5_funct_1(X0,sK0)) )),
% 1.25/0.52    inference(superposition,[],[f18,f58])).
% 1.25/0.52  fof(f126,plain,(
% 1.25/0.52    ( ! [X0,X1] : (v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f125,f73])).
% 1.25/0.52  fof(f73,plain,(
% 1.25/0.52    ( ! [X0] : (v1_relat_1(X0)) )),
% 1.25/0.52    inference(superposition,[],[f34,f58])).
% 1.25/0.52  fof(f125,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f124,f72])).
% 1.25/0.52  fof(f72,plain,(
% 1.25/0.52    ( ! [X0] : (v1_funct_1(X0)) )),
% 1.25/0.52    inference(superposition,[],[f33,f58])).
% 1.25/0.52  fof(f124,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f123,f73])).
% 1.25/0.52  fof(f123,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f116,f72])).
% 1.25/0.52  fof(f116,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(resolution,[],[f28,f114])).
% 1.25/0.52  fof(f114,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0)) )),
% 1.25/0.52    inference(superposition,[],[f111,f58])).
% 1.25/0.52  fof(f111,plain,(
% 1.25/0.52    ( ! [X1] : (r2_hidden(X1,k1_xboole_0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f110,f78])).
% 1.25/0.52  fof(f78,plain,(
% 1.25/0.52    ( ! [X0] : (~v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(superposition,[],[f18,f58])).
% 1.25/0.52  fof(f110,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r2_hidden(X1,k1_xboole_0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f109,f73])).
% 1.25/0.52  fof(f109,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r2_hidden(X1,k1_xboole_0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(subsumption_resolution,[],[f82,f72])).
% 1.25/0.52  fof(f82,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r2_hidden(X1,k1_xboole_0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v5_funct_1(k1_xboole_0,X0)) )),
% 1.25/0.52    inference(superposition,[],[f47,f58])).
% 1.25/0.52  fof(f28,plain,(
% 1.25/0.52    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v5_funct_1(X1,X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f14])).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (25397)------------------------------
% 1.25/0.52  % (25397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (25397)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (25397)Memory used [KB]: 6140
% 1.25/0.52  % (25397)Time elapsed: 0.108 s
% 1.25/0.52  % (25397)------------------------------
% 1.25/0.52  % (25397)------------------------------
% 1.25/0.52  % (25381)Success in time 0.164 s
%------------------------------------------------------------------------------
