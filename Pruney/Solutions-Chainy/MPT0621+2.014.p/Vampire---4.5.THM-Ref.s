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
% DateTime   : Thu Dec  3 12:51:56 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 149 expanded)
%              Number of leaves         :    6 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  130 ( 515 expanded)
%              Number of equality atoms :   64 ( 222 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f737,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f599])).

fof(f599,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f598,f598])).

fof(f598,plain,(
    ! [X0] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0 ),
    inference(subsumption_resolution,[],[f597,f16])).

% (28154)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f597,plain,(
    ! [X0] :
      ( k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f227,f132])).

fof(f132,plain,(
    ! [X0] : sK1(sK0) = sK5(sK0,X0) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X4
      | sK0 != X2
      | sK5(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f127,f28])).

fof(f28,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f127,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | sK0 != X4
      | ~ v1_relat_1(sK5(X2,X3))
      | sK5(X2,X3) = sK1(X4) ) ),
    inference(subsumption_resolution,[],[f124,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f124,plain,(
    ! [X4,X2,X3] :
      ( sK0 != X2
      | ~ v1_funct_1(sK5(X2,X3))
      | sK0 != X4
      | ~ v1_relat_1(sK5(X2,X3))
      | sK5(X2,X3) = sK1(X4) ) ),
    inference(superposition,[],[f120,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f120,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) != sK0
      | ~ v1_funct_1(X1)
      | sK0 != X0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f119,f21])).

fof(f21,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f119,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f117,f20])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f117,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK1(X0))
      | ~ v1_funct_1(sK1(X0))
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | sK1(X0) = X1 ) ),
    inference(superposition,[],[f15,f22])).

fof(f22,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | k1_relat_1(X2) != X0
              | k1_relat_1(X1) != X0
              | ~ v1_funct_1(X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( ( v1_funct_1(X1)
              & v1_relat_1(X1) )
           => ! [X2] :
                ( ( v1_funct_1(X2)
                  & v1_relat_1(X2) )
               => ( ( k1_relat_1(X2) = X0
                    & k1_relat_1(X1) = X0 )
                 => X1 = X2 ) ) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ( ( k1_relat_1(X2) = X0
                  & k1_relat_1(X1) = X0 )
               => X1 = X2 ) ) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(f227,plain,(
    ! [X6,X5] :
      ( k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6
      | k1_xboole_0 = X5 ) ),
    inference(backward_demodulation,[],[f177,f179])).

fof(f179,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f157,f46])).

fof(f46,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f18,f17])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f157,plain,(
    ! [X12] :
      ( r2_hidden(sK2(k1_xboole_0,X12),X12)
      | k1_relat_1(k1_xboole_0) = X12 ) ),
    inference(resolution,[],[f25,f46])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f177,plain,(
    ! [X6,X5] :
      ( k1_relat_1(k1_xboole_0) = X5
      | k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6 ) ),
    inference(resolution,[],[f157,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK5(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f16,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:05:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (28148)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (28140)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.47  % (28148)Refutation not found, incomplete strategy% (28148)------------------------------
% 0.22/0.47  % (28148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (28148)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (28148)Memory used [KB]: 6012
% 0.22/0.47  % (28148)Time elapsed: 0.053 s
% 0.22/0.47  % (28148)------------------------------
% 0.22/0.47  % (28148)------------------------------
% 0.22/0.47  % (28140)Refutation not found, incomplete strategy% (28140)------------------------------
% 0.22/0.47  % (28140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (28140)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (28140)Memory used [KB]: 6140
% 0.22/0.47  % (28140)Time elapsed: 0.053 s
% 0.22/0.47  % (28140)------------------------------
% 0.22/0.47  % (28140)------------------------------
% 0.22/0.49  % (28156)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.49  % (28141)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (28141)Refutation not found, incomplete strategy% (28141)------------------------------
% 0.22/0.49  % (28141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (28141)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (28141)Memory used [KB]: 10618
% 0.22/0.49  % (28141)Time elapsed: 0.075 s
% 0.22/0.49  % (28141)------------------------------
% 0.22/0.49  % (28141)------------------------------
% 0.22/0.49  % (28151)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.50  % (28149)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (28150)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (28137)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.50  % (28157)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.51  % (28143)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (28142)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.51  % (28145)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (28147)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (28158)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (28138)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (28135)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.52  % (28135)Refutation not found, incomplete strategy% (28135)------------------------------
% 0.22/0.52  % (28135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28135)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28135)Memory used [KB]: 10490
% 0.22/0.52  % (28135)Time elapsed: 0.117 s
% 0.22/0.52  % (28135)------------------------------
% 0.22/0.52  % (28135)------------------------------
% 0.22/0.52  % (28136)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (28159)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.53  % (28136)Refutation not found, incomplete strategy% (28136)------------------------------
% 0.22/0.53  % (28136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28136)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28136)Memory used [KB]: 10618
% 0.22/0.53  % (28136)Time elapsed: 0.118 s
% 0.22/0.53  % (28136)------------------------------
% 0.22/0.53  % (28136)------------------------------
% 0.22/0.53  % (28139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (28157)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f737,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f16,f599])).
% 0.22/0.53  fof(f599,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1) )),
% 0.22/0.53    inference(superposition,[],[f598,f598])).
% 0.22/0.53  fof(f598,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f597,f16])).
% 0.22/0.53  % (28154)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  fof(f597,plain,(
% 0.22/0.53    ( ! [X0] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X0 | k1_xboole_0 = sK0) )),
% 0.22/0.53    inference(superposition,[],[f227,f132])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ( ! [X0] : (sK1(sK0) = sK5(sK0,X0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f131])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(sK0)) )),
% 0.22/0.53    inference(equality_resolution,[],[f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (sK0 != X4 | sK0 != X2 | sK5(X2,X3) = sK1(X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f127,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (sK0 != X2 | sK0 != X4 | ~v1_relat_1(sK5(X2,X3)) | sK5(X2,X3) = sK1(X4)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f124,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X4,X2,X3] : (sK0 != X2 | ~v1_funct_1(sK5(X2,X3)) | sK0 != X4 | ~v1_relat_1(sK5(X2,X3)) | sK5(X2,X3) = sK1(X4)) )),
% 0.22/0.53    inference(superposition,[],[f120,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_relat_1(X1) != sK0 | ~v1_funct_1(X1) | sK0 != X0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f119,f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_funct_1(sK1(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f117,f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sK0 != X0 | ~v1_funct_1(X1) | ~v1_relat_1(sK1(X0)) | ~v1_funct_1(sK1(X0)) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | sK1(X0) = X1) )),
% 0.22/0.53    inference(superposition,[],[f15,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    ( ! [X6,X5] : (k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6 | k1_xboole_0 = X5) )),
% 0.22/0.53    inference(backward_demodulation,[],[f177,f179])).
% 0.22/0.53  fof(f179,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f157,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.53    inference(resolution,[],[f18,f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    ( ! [X12] : (r2_hidden(sK2(k1_xboole_0,X12),X12) | k1_relat_1(k1_xboole_0) = X12) )),
% 0.22/0.53    inference(resolution,[],[f25,f46])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    ( ! [X6,X5] : (k1_relat_1(k1_xboole_0) = X5 | k1_funct_1(sK5(X5,X6),sK2(k1_xboole_0,X5)) = X6) )),
% 0.22/0.53    inference(resolution,[],[f157,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK5(X0,X1),X3) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    k1_xboole_0 != sK0),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (28157)------------------------------
% 0.22/0.53  % (28157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28157)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (28157)Memory used [KB]: 11129
% 0.22/0.53  % (28157)Time elapsed: 0.109 s
% 0.22/0.53  % (28157)------------------------------
% 0.22/0.53  % (28157)------------------------------
% 0.22/0.53  % (28134)Success in time 0.169 s
%------------------------------------------------------------------------------
