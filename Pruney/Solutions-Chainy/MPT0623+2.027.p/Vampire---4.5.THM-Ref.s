%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:06 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 185 expanded)
%              Number of leaves         :   11 (  44 expanded)
%              Depth                    :   20
%              Number of atoms          :  200 ( 654 expanded)
%              Number of equality atoms :   96 ( 315 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f443,plain,(
    $false ),
    inference(equality_resolution,[],[f435])).

fof(f435,plain,(
    ! [X18] : sK1 != X18 ),
    inference(global_subsumption,[],[f27,f120,f427])).

fof(f427,plain,(
    ! [X18] :
      ( k1_xboole_0 = sK0
      | sK1 != X18 ) ),
    inference(resolution,[],[f404,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK0)
      | sK1 != X0 ) ),
    inference(subsumption_resolution,[],[f177,f119])).

fof(f119,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f118,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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

fof(f118,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f117,plain,(
    ! [X1] :
      ( sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f40,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f116,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(subsumption_resolution,[],[f113,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f113,plain,(
    ! [X1] :
      ( ~ r1_tarski(k1_xboole_0,sK0)
      | ~ v1_funct_1(sK3(X1))
      | sK1 != k1_relat_1(sK3(X1))
      | ~ v1_relat_1(sK3(X1))
      | k1_xboole_0 != X1 ) ),
    inference(superposition,[],[f26,f105])).

fof(f105,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != X0 ) ),
    inference(forward_demodulation,[],[f102,f41])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(sK3(X0))
      | k1_xboole_0 != k1_relat_1(sK3(X0)) ) ),
    inference(resolution,[],[f33,f39])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f26,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f177,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | ~ r2_hidden(X1,sK0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f170,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f170,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f168,f111])).

fof(f111,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f110,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f108,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f108,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | ~ v1_funct_1(sK2(X2,X3))
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f26,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f168,plain,(
    ! [X0] :
      ( r1_tarski(k1_tarski(X0),sK0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(superposition,[],[f48,f166])).

fof(f166,plain,(
    ! [X0] : sK5(k1_tarski(X0),sK0) = X0 ),
    inference(equality_resolution,[],[f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1 ) ),
    inference(subsumption_resolution,[],[f164,f119])).

fof(f164,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK5(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f144,f36])).

fof(f144,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK5(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f70,f111])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK5(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f404,plain,(
    ! [X7] :
      ( r2_hidden(sK7(k1_xboole_0,X7),X7)
      | k1_xboole_0 = X7 ) ),
    inference(forward_demodulation,[],[f379,f28])).

fof(f28,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f379,plain,(
    ! [X7] :
      ( r2_hidden(sK7(k1_xboole_0,X7),X7)
      | k1_relat_1(k1_xboole_0) = X7 ) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f87,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f42,f31])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f46,f30])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK9(X0,X1)),X0)
      | r2_hidden(sK7(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f120,plain,(
    k1_xboole_0 != sK1 ),
    inference(equality_resolution,[],[f119])).

fof(f27,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:44:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.55  % (1748)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.57  % (1765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.57  % (1756)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.62/0.58  % (1762)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.62/0.58  % (1748)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.59  % (1750)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.62/0.59  % (1753)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.62/0.59  % (1770)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.62/0.60  % (1745)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.60  % (1747)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.62/0.60  % (1746)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.62/0.60  % SZS output start Proof for theBenchmark
% 1.62/0.60  fof(f443,plain,(
% 1.62/0.60    $false),
% 1.62/0.60    inference(equality_resolution,[],[f435])).
% 1.62/0.60  fof(f435,plain,(
% 1.62/0.60    ( ! [X18] : (sK1 != X18) )),
% 1.62/0.60    inference(global_subsumption,[],[f27,f120,f427])).
% 1.62/0.60  fof(f427,plain,(
% 1.62/0.60    ( ! [X18] : (k1_xboole_0 = sK0 | sK1 != X18) )),
% 1.62/0.60    inference(resolution,[],[f404,f178])).
% 1.62/0.60  fof(f178,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X1,sK0) | sK1 != X0) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f177,f119])).
% 1.62/0.60  fof(f119,plain,(
% 1.62/0.60    ( ! [X0] : (sK1 != X0 | k1_xboole_0 != X0) )),
% 1.62/0.60    inference(superposition,[],[f118,f41])).
% 1.62/0.60  fof(f41,plain,(
% 1.62/0.60    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f20])).
% 1.62/0.60  fof(f20,plain,(
% 1.62/0.60    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.62/0.60    inference(ennf_transformation,[],[f10])).
% 1.62/0.60  fof(f10,axiom,(
% 1.62/0.60    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.62/0.60  fof(f118,plain,(
% 1.62/0.60    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f117,f39])).
% 1.62/0.60  fof(f39,plain,(
% 1.62/0.60    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f20])).
% 1.62/0.60  fof(f117,plain,(
% 1.62/0.60    ( ! [X1] : (sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f116,f40])).
% 1.62/0.60  fof(f40,plain,(
% 1.62/0.60    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.62/0.60    inference(cnf_transformation,[],[f20])).
% 1.62/0.60  fof(f116,plain,(
% 1.62/0.60    ( ! [X1] : (~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f113,f30])).
% 1.62/0.60  fof(f30,plain,(
% 1.62/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f3])).
% 1.62/0.60  fof(f3,axiom,(
% 1.62/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.60  fof(f113,plain,(
% 1.62/0.60    ( ! [X1] : (~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(sK3(X1)) | sK1 != k1_relat_1(sK3(X1)) | ~v1_relat_1(sK3(X1)) | k1_xboole_0 != X1) )),
% 1.62/0.60    inference(superposition,[],[f26,f105])).
% 1.62/0.60  fof(f105,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != X0) )),
% 1.62/0.60    inference(forward_demodulation,[],[f102,f41])).
% 1.62/0.60  fof(f102,plain,(
% 1.62/0.60    ( ! [X0] : (k1_xboole_0 = k2_relat_1(sK3(X0)) | k1_xboole_0 != k1_relat_1(sK3(X0))) )),
% 1.62/0.60    inference(resolution,[],[f33,f39])).
% 1.62/0.60  fof(f33,plain,(
% 1.62/0.60    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f18])).
% 1.62/0.60  fof(f18,plain,(
% 1.62/0.60    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f8])).
% 1.62/0.60  fof(f8,axiom,(
% 1.62/0.60    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.62/0.60  fof(f26,plain,(
% 1.62/0.60    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f17])).
% 1.62/0.60  fof(f17,plain,(
% 1.62/0.60    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.62/0.60    inference(flattening,[],[f16])).
% 1.62/0.60  fof(f16,plain,(
% 1.62/0.60    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.62/0.60    inference(ennf_transformation,[],[f14])).
% 1.62/0.60  fof(f14,negated_conjecture,(
% 1.62/0.60    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.62/0.60    inference(negated_conjecture,[],[f13])).
% 1.62/0.60  fof(f13,conjecture,(
% 1.62/0.60    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.62/0.60  fof(f177,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f176])).
% 1.62/0.60  fof(f176,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != X0 | ~r2_hidden(X1,sK0) | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(superposition,[],[f170,f36])).
% 1.62/0.60  fof(f36,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f19])).
% 1.62/0.60  fof(f19,plain,(
% 1.62/0.60    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.62/0.60    inference(ennf_transformation,[],[f12])).
% 1.62/0.60  fof(f12,axiom,(
% 1.62/0.60    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.62/0.60  fof(f170,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | ~r2_hidden(X0,sK0) | k1_xboole_0 = X1) )),
% 1.62/0.60    inference(resolution,[],[f168,f111])).
% 1.62/0.60  fof(f111,plain,(
% 1.62/0.60    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f110,f34])).
% 1.62/0.60  fof(f34,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f19])).
% 1.62/0.60  fof(f110,plain,(
% 1.62/0.60    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f108,f35])).
% 1.62/0.60  fof(f35,plain,(
% 1.62/0.60    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f19])).
% 1.62/0.60  fof(f108,plain,(
% 1.62/0.60    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | ~v1_funct_1(sK2(X2,X3)) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.62/0.60    inference(superposition,[],[f26,f37])).
% 1.62/0.60  fof(f37,plain,(
% 1.62/0.60    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(cnf_transformation,[],[f19])).
% 1.62/0.60  fof(f168,plain,(
% 1.62/0.60    ( ! [X0] : (r1_tarski(k1_tarski(X0),sK0) | ~r2_hidden(X0,sK0)) )),
% 1.62/0.60    inference(superposition,[],[f48,f166])).
% 1.62/0.60  fof(f166,plain,(
% 1.62/0.60    ( ! [X0] : (sK5(k1_tarski(X0),sK0) = X0) )),
% 1.62/0.60    inference(equality_resolution,[],[f165])).
% 1.62/0.60  fof(f165,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f164,f119])).
% 1.62/0.60  fof(f164,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(duplicate_literal_removal,[],[f163])).
% 1.62/0.60  fof(f163,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != X0 | sK5(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.62/0.60    inference(superposition,[],[f144,f36])).
% 1.62/0.60  fof(f144,plain,(
% 1.62/0.60    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK5(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 1.62/0.60    inference(resolution,[],[f70,f111])).
% 1.62/0.60  fof(f70,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK5(k1_tarski(X0),X1) = X0) )),
% 1.62/0.60    inference(resolution,[],[f47,f61])).
% 1.62/0.60  fof(f61,plain,(
% 1.62/0.60    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.62/0.60    inference(equality_resolution,[],[f50])).
% 1.62/0.60  fof(f50,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.62/0.60    inference(cnf_transformation,[],[f5])).
% 1.62/0.60  fof(f5,axiom,(
% 1.62/0.60    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.62/0.60  fof(f47,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f24])).
% 1.62/0.60  fof(f24,plain,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.62/0.60    inference(ennf_transformation,[],[f1])).
% 1.62/0.60  fof(f1,axiom,(
% 1.62/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.62/0.60  fof(f48,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f24])).
% 1.62/0.60  fof(f404,plain,(
% 1.62/0.60    ( ! [X7] : (r2_hidden(sK7(k1_xboole_0,X7),X7) | k1_xboole_0 = X7) )),
% 1.62/0.60    inference(forward_demodulation,[],[f379,f28])).
% 1.62/0.60  fof(f28,plain,(
% 1.62/0.60    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.60    inference(cnf_transformation,[],[f7])).
% 1.62/0.60  fof(f7,axiom,(
% 1.62/0.60    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.62/0.60  fof(f379,plain,(
% 1.62/0.60    ( ! [X7] : (r2_hidden(sK7(k1_xboole_0,X7),X7) | k1_relat_1(k1_xboole_0) = X7) )),
% 1.62/0.60    inference(resolution,[],[f55,f89])).
% 1.62/0.60  fof(f89,plain,(
% 1.62/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(subsumption_resolution,[],[f87,f77])).
% 1.62/0.60  fof(f77,plain,(
% 1.62/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) )),
% 1.62/0.60    inference(resolution,[],[f42,f31])).
% 1.62/0.60  fof(f31,plain,(
% 1.62/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f4])).
% 1.62/0.60  fof(f4,axiom,(
% 1.62/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.62/0.60  fof(f42,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f21])).
% 1.62/0.60  fof(f21,plain,(
% 1.62/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.62/0.60    inference(ennf_transformation,[],[f15])).
% 1.62/0.60  fof(f15,plain,(
% 1.62/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.60    inference(rectify,[],[f2])).
% 1.62/0.60  fof(f2,axiom,(
% 1.62/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.62/0.60  fof(f87,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.62/0.60    inference(resolution,[],[f46,f30])).
% 1.62/0.60  fof(f46,plain,(
% 1.62/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.62/0.60    inference(cnf_transformation,[],[f24])).
% 1.62/0.60  fof(f55,plain,(
% 1.62/0.60    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK9(X0,X1)),X0) | r2_hidden(sK7(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.62/0.60    inference(cnf_transformation,[],[f6])).
% 1.62/0.60  fof(f6,axiom,(
% 1.62/0.60    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.62/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 1.62/0.60  fof(f120,plain,(
% 1.62/0.60    k1_xboole_0 != sK1),
% 1.62/0.60    inference(equality_resolution,[],[f119])).
% 1.62/0.60  fof(f27,plain,(
% 1.62/0.60    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.62/0.60    inference(cnf_transformation,[],[f17])).
% 1.62/0.60  % SZS output end Proof for theBenchmark
% 1.62/0.60  % (1748)------------------------------
% 1.62/0.60  % (1748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.60  % (1748)Termination reason: Refutation
% 1.62/0.60  
% 1.62/0.60  % (1748)Memory used [KB]: 6908
% 1.62/0.60  % (1748)Time elapsed: 0.149 s
% 1.62/0.60  % (1748)------------------------------
% 1.62/0.60  % (1748)------------------------------
% 1.62/0.61  % (1741)Success in time 0.238 s
%------------------------------------------------------------------------------
