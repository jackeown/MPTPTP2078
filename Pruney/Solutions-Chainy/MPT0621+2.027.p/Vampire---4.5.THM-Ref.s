%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:58 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   57 (  97 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   16
%              Number of atoms          :  177 ( 374 expanded)
%              Number of equality atoms :   94 ( 185 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (23876)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f1627,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1419,f1542,f1625])).

fof(f1625,plain,(
    ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f1621])).

fof(f1621,plain,
    ( $false
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f15,f1546])).

fof(f1546,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl6_22 ),
    inference(superposition,[],[f1418,f1418])).

fof(f1418,plain,
    ( ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f1417])).

fof(f1417,plain,
    ( spl6_22
  <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f15,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f1542,plain,(
    ~ spl6_21 ),
    inference(avatar_contradiction_clause,[],[f1533])).

fof(f1533,plain,
    ( $false
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f15,f1458])).

fof(f1458,plain,
    ( ! [X0,X1] : X0 = X1
    | ~ spl6_21 ),
    inference(superposition,[],[f1415,f1415])).

fof(f1415,plain,
    ( ! [X3] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f1414])).

fof(f1414,plain,
    ( spl6_21
  <=> ! [X3] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f1419,plain,
    ( spl6_21
    | spl6_22 ),
    inference(avatar_split_clause,[],[f1412,f1417,f1414])).

fof(f1412,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2
      | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3 ) ),
    inference(subsumption_resolution,[],[f1339,f15])).

fof(f1339,plain,(
    ! [X2,X3] :
      ( k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2
      | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f193,f83])).

fof(f83,plain,(
    ! [X0] : sK1(sK0) = sK5(sK0,X0) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( sK0 != X0
      | sK5(X0,X1) = sK1(sK0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( sK0 != X5
      | sK0 != X3
      | sK5(X3,X4) = sK1(X5) ) ),
    inference(subsumption_resolution,[],[f78,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f78,plain,(
    ! [X4,X5,X3] :
      ( sK0 != X3
      | sK0 != X5
      | ~ v1_relat_1(sK5(X3,X4))
      | sK5(X3,X4) = sK1(X5) ) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f30,plain,(
    ! [X0,X1] : v1_funct_1(sK5(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X4,X5,X3] :
      ( sK0 != X3
      | ~ v1_funct_1(sK5(X3,X4))
      | sK0 != X5
      | ~ v1_relat_1(sK5(X3,X4))
      | sK5(X3,X4) = sK1(X5) ) ),
    inference(superposition,[],[f70,f31])).

fof(f31,plain,(
    ! [X0,X1] : k1_relat_1(sK5(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X2)
      | sK0 != X1
      | ~ v1_relat_1(X2)
      | sK1(X1) = X2 ) ),
    inference(subsumption_resolution,[],[f69,f22])).

fof(f22,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_funct_1(X1,X2) = np__1
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_funct_1(X1,X2) = np__1 )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(f69,plain,(
    ! [X2,X1] :
      ( sK0 != X1
      | ~ v1_funct_1(X2)
      | ~ v1_funct_1(sK1(X1))
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(X2)
      | sK1(X1) = X2 ) ),
    inference(subsumption_resolution,[],[f67,f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X1] :
      ( sK0 != X1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK1(X1))
      | ~ v1_funct_1(sK1(X1))
      | k1_relat_1(X2) != sK0
      | ~ v1_relat_1(X2)
      | sK1(X1) = X2 ) ),
    inference(superposition,[],[f14,f23])).

fof(f23,plain,(
    ! [X0] : k1_relat_1(sK1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f14,plain,(
    ! [X2,X1] :
      ( k1_relat_1(X2) != sK0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X1) != sK0
      | ~ v1_relat_1(X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f193,plain,(
    ! [X12,X13,X11] :
      ( k1_funct_1(sK5(X11,X13),sK2(k1_xboole_0,X11)) = X13
      | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X11)) = X12
      | k1_xboole_0 = X11 ) ),
    inference(resolution,[],[f156,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK5(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f156,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(k1_xboole_0,X8),X8)
      | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X8)) = X9
      | k1_xboole_0 = X8 ) ),
    inference(forward_demodulation,[],[f137,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = sK5(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = sK5(X1,X2) ) ),
    inference(subsumption_resolution,[],[f36,f29])).

fof(f36,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != X1
      | ~ v1_relat_1(sK5(X1,X2))
      | k1_xboole_0 = sK5(X1,X2) ) ),
    inference(superposition,[],[f18,f31])).

fof(f18,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f137,plain,(
    ! [X8,X9] :
      ( r2_hidden(sK2(k1_xboole_0,X8),X8)
      | k1_xboole_0 = X8
      | k1_funct_1(sK5(k1_xboole_0,X9),sK2(k1_xboole_0,X8)) = X9 ) ),
    inference(resolution,[],[f127,f28])).

fof(f127,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0)
      | r2_hidden(sK2(k1_xboole_0,X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f96,f16])).

fof(f16,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(resolution,[],[f26,f33])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:10:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (23874)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.48  % (23874)Refutation not found, incomplete strategy% (23874)------------------------------
% 0.22/0.48  % (23874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23889)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.48  % (23874)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23874)Memory used [KB]: 1663
% 0.22/0.48  % (23874)Time elapsed: 0.063 s
% 0.22/0.48  % (23874)------------------------------
% 0.22/0.48  % (23874)------------------------------
% 0.22/0.50  % (23870)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.50  % (23867)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (23891)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.51  % (23875)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (23867)Refutation not found, incomplete strategy% (23867)------------------------------
% 0.22/0.51  % (23867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23867)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23867)Memory used [KB]: 10490
% 0.22/0.51  % (23867)Time elapsed: 0.082 s
% 0.22/0.51  % (23867)------------------------------
% 0.22/0.51  % (23867)------------------------------
% 0.22/0.52  % (23883)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (23880)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (23868)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (23872)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (23879)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (23872)Refutation not found, incomplete strategy% (23872)------------------------------
% 0.22/0.53  % (23872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (23872)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (23872)Memory used [KB]: 6140
% 0.22/0.53  % (23872)Time elapsed: 0.119 s
% 0.22/0.53  % (23872)------------------------------
% 0.22/0.53  % (23872)------------------------------
% 0.22/0.53  % (23877)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.54  % (23885)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (23890)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (23888)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (23887)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.42/0.54  % (23868)Refutation not found, incomplete strategy% (23868)------------------------------
% 1.42/0.54  % (23868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.54  % (23868)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.54  
% 1.42/0.54  % (23868)Memory used [KB]: 10618
% 1.42/0.54  % (23868)Time elapsed: 0.119 s
% 1.42/0.54  % (23868)------------------------------
% 1.42/0.54  % (23868)------------------------------
% 1.42/0.54  % (23869)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.42/0.54  % (23871)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.42/0.55  % (23881)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.42/0.55  % (23878)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.42/0.55  % (23880)Refutation not found, incomplete strategy% (23880)------------------------------
% 1.42/0.55  % (23880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23880)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23880)Memory used [KB]: 6012
% 1.42/0.55  % (23880)Time elapsed: 0.143 s
% 1.42/0.55  % (23880)------------------------------
% 1.42/0.55  % (23880)------------------------------
% 1.42/0.55  % (23878)Refutation not found, incomplete strategy% (23878)------------------------------
% 1.42/0.55  % (23878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23878)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23878)Memory used [KB]: 10490
% 1.42/0.55  % (23878)Time elapsed: 0.133 s
% 1.42/0.55  % (23878)------------------------------
% 1.42/0.55  % (23878)------------------------------
% 1.42/0.55  % (23882)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.42/0.55  % (23873)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.42/0.55  % (23892)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.42/0.55  % (23873)Refutation not found, incomplete strategy% (23873)------------------------------
% 1.42/0.55  % (23873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (23873)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (23873)Memory used [KB]: 10618
% 1.42/0.55  % (23873)Time elapsed: 0.129 s
% 1.42/0.55  % (23873)------------------------------
% 1.42/0.55  % (23873)------------------------------
% 1.42/0.56  % (23884)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.57/0.56  % (23889)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  % (23876)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.57/0.56  fof(f1627,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f1419,f1542,f1625])).
% 1.57/0.56  fof(f1625,plain,(
% 1.57/0.56    ~spl6_22),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f1621])).
% 1.57/0.56  fof(f1621,plain,(
% 1.57/0.56    $false | ~spl6_22),
% 1.57/0.56    inference(subsumption_resolution,[],[f15,f1546])).
% 1.57/0.56  fof(f1546,plain,(
% 1.57/0.56    ( ! [X0,X1] : (X0 = X1) ) | ~spl6_22),
% 1.57/0.56    inference(superposition,[],[f1418,f1418])).
% 1.57/0.56  fof(f1418,plain,(
% 1.57/0.56    ( ! [X2] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2) ) | ~spl6_22),
% 1.57/0.56    inference(avatar_component_clause,[],[f1417])).
% 1.57/0.56  fof(f1417,plain,(
% 1.57/0.56    spl6_22 <=> ! [X2] : k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.57/0.56  fof(f15,plain,(
% 1.57/0.56    k1_xboole_0 != sK0),
% 1.57/0.56    inference(cnf_transformation,[],[f9])).
% 1.57/0.56  fof(f9,plain,(
% 1.57/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : (X1 = X2 | k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.57/0.56    inference(flattening,[],[f8])).
% 1.57/0.56  fof(f8,plain,(
% 1.57/0.56    ? [X0] : (k1_xboole_0 != X0 & ! [X1] : (! [X2] : ((X1 = X2 | (k1_relat_1(X2) != X0 | k1_relat_1(X1) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))))),
% 1.57/0.56    inference(ennf_transformation,[],[f7])).
% 1.57/0.56  fof(f7,negated_conjecture,(
% 1.57/0.56    ~! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.57/0.56    inference(negated_conjecture,[],[f6])).
% 1.57/0.56  fof(f6,conjecture,(
% 1.57/0.56    ! [X0] : (! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((k1_relat_1(X2) = X0 & k1_relat_1(X1) = X0) => X1 = X2))) => k1_xboole_0 = X0)),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).
% 1.57/0.56  fof(f1542,plain,(
% 1.57/0.56    ~spl6_21),
% 1.57/0.56    inference(avatar_contradiction_clause,[],[f1533])).
% 1.57/0.56  fof(f1533,plain,(
% 1.57/0.56    $false | ~spl6_21),
% 1.57/0.56    inference(subsumption_resolution,[],[f15,f1458])).
% 1.57/0.56  fof(f1458,plain,(
% 1.57/0.56    ( ! [X0,X1] : (X0 = X1) ) | ~spl6_21),
% 1.57/0.56    inference(superposition,[],[f1415,f1415])).
% 1.57/0.56  fof(f1415,plain,(
% 1.57/0.56    ( ! [X3] : (k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3) ) | ~spl6_21),
% 1.57/0.56    inference(avatar_component_clause,[],[f1414])).
% 1.57/0.56  fof(f1414,plain,(
% 1.57/0.56    spl6_21 <=> ! [X3] : k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.57/0.56  fof(f1419,plain,(
% 1.57/0.56    spl6_21 | spl6_22),
% 1.57/0.56    inference(avatar_split_clause,[],[f1412,f1417,f1414])).
% 1.57/0.56  fof(f1412,plain,(
% 1.57/0.56    ( ! [X2,X3] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f1339,f15])).
% 1.57/0.56  fof(f1339,plain,(
% 1.57/0.56    ( ! [X2,X3] : (k1_funct_1(sK1(sK0),sK2(k1_xboole_0,sK0)) = X2 | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,sK0)) = X3 | k1_xboole_0 = sK0) )),
% 1.57/0.56    inference(superposition,[],[f193,f83])).
% 1.57/0.56  fof(f83,plain,(
% 1.57/0.56    ( ! [X0] : (sK1(sK0) = sK5(sK0,X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f82])).
% 1.57/0.56  fof(f82,plain,(
% 1.57/0.56    ( ! [X0,X1] : (sK0 != X0 | sK5(X0,X1) = sK1(sK0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f79])).
% 1.57/0.56  fof(f79,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (sK0 != X5 | sK0 != X3 | sK5(X3,X4) = sK1(X5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f78,f29])).
% 1.57/0.56  fof(f29,plain,(
% 1.57/0.56    ( ! [X0,X1] : (v1_relat_1(sK5(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f13,plain,(
% 1.57/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.57/0.56    inference(ennf_transformation,[],[f4])).
% 1.57/0.56  fof(f4,axiom,(
% 1.57/0.56    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.57/0.56  fof(f78,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (sK0 != X3 | sK0 != X5 | ~v1_relat_1(sK5(X3,X4)) | sK5(X3,X4) = sK1(X5)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f75,f30])).
% 1.57/0.56  fof(f30,plain,(
% 1.57/0.56    ( ! [X0,X1] : (v1_funct_1(sK5(X0,X1))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f75,plain,(
% 1.57/0.56    ( ! [X4,X5,X3] : (sK0 != X3 | ~v1_funct_1(sK5(X3,X4)) | sK0 != X5 | ~v1_relat_1(sK5(X3,X4)) | sK5(X3,X4) = sK1(X5)) )),
% 1.57/0.56    inference(superposition,[],[f70,f31])).
% 1.57/0.56  fof(f31,plain,(
% 1.57/0.56    ( ! [X0,X1] : (k1_relat_1(sK5(X0,X1)) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f70,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X2) | sK0 != X1 | ~v1_relat_1(X2) | sK1(X1) = X2) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f69,f22])).
% 1.57/0.56  fof(f22,plain,(
% 1.57/0.56    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f12,plain,(
% 1.57/0.56    ! [X0] : ? [X1] : (! [X2] : (k1_funct_1(X1,X2) = np__1 | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.57/0.56    inference(ennf_transformation,[],[f5])).
% 1.57/0.56  fof(f5,axiom,(
% 1.57/0.56    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_funct_1(X1,X2) = np__1) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).
% 1.57/0.56  fof(f69,plain,(
% 1.57/0.56    ( ! [X2,X1] : (sK0 != X1 | ~v1_funct_1(X2) | ~v1_funct_1(sK1(X1)) | k1_relat_1(X2) != sK0 | ~v1_relat_1(X2) | sK1(X1) = X2) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f67,f21])).
% 1.57/0.56  fof(f21,plain,(
% 1.57/0.56    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f67,plain,(
% 1.57/0.56    ( ! [X2,X1] : (sK0 != X1 | ~v1_funct_1(X2) | ~v1_relat_1(sK1(X1)) | ~v1_funct_1(sK1(X1)) | k1_relat_1(X2) != sK0 | ~v1_relat_1(X2) | sK1(X1) = X2) )),
% 1.57/0.56    inference(superposition,[],[f14,f23])).
% 1.57/0.56  fof(f23,plain,(
% 1.57/0.56    ( ! [X0] : (k1_relat_1(sK1(X0)) = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f12])).
% 1.57/0.56  fof(f14,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k1_relat_1(X2) != sK0 | ~v1_funct_1(X1) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X1) != sK0 | ~v1_relat_1(X1) | X1 = X2) )),
% 1.57/0.56    inference(cnf_transformation,[],[f9])).
% 1.57/0.56  fof(f193,plain,(
% 1.57/0.56    ( ! [X12,X13,X11] : (k1_funct_1(sK5(X11,X13),sK2(k1_xboole_0,X11)) = X13 | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X11)) = X12 | k1_xboole_0 = X11) )),
% 1.57/0.56    inference(resolution,[],[f156,f28])).
% 1.57/0.56  fof(f28,plain,(
% 1.57/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK5(X0,X1),X3) = X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f13])).
% 1.57/0.56  fof(f156,plain,(
% 1.57/0.56    ( ! [X8,X9] : (r2_hidden(sK2(k1_xboole_0,X8),X8) | k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X8)) = X9 | k1_xboole_0 = X8) )),
% 1.57/0.56    inference(forward_demodulation,[],[f137,f43])).
% 1.57/0.56  fof(f43,plain,(
% 1.57/0.56    ( ! [X0] : (k1_xboole_0 = sK5(k1_xboole_0,X0)) )),
% 1.57/0.56    inference(equality_resolution,[],[f38])).
% 1.57/0.56  fof(f38,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = sK5(X1,X2)) )),
% 1.57/0.56    inference(subsumption_resolution,[],[f36,f29])).
% 1.57/0.56  fof(f36,plain,(
% 1.57/0.56    ( ! [X2,X1] : (k1_xboole_0 != X1 | ~v1_relat_1(sK5(X1,X2)) | k1_xboole_0 = sK5(X1,X2)) )),
% 1.57/0.56    inference(superposition,[],[f18,f31])).
% 1.57/0.56  fof(f18,plain,(
% 1.57/0.56    ( ! [X0] : (k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.57/0.56    inference(cnf_transformation,[],[f11])).
% 1.57/0.56  fof(f11,plain,(
% 1.57/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(flattening,[],[f10])).
% 1.57/0.56  fof(f10,plain,(
% 1.57/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 1.57/0.56    inference(ennf_transformation,[],[f3])).
% 1.57/0.56  fof(f3,axiom,(
% 1.57/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.57/0.56  fof(f137,plain,(
% 1.57/0.56    ( ! [X8,X9] : (r2_hidden(sK2(k1_xboole_0,X8),X8) | k1_xboole_0 = X8 | k1_funct_1(sK5(k1_xboole_0,X9),sK2(k1_xboole_0,X8)) = X9) )),
% 1.57/0.56    inference(resolution,[],[f127,f28])).
% 1.57/0.56  fof(f127,plain,(
% 1.57/0.56    ( ! [X0] : (r2_hidden(sK2(k1_xboole_0,X0),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),X0) | k1_xboole_0 = X0) )),
% 1.57/0.56    inference(superposition,[],[f96,f16])).
% 1.57/0.56  fof(f16,plain,(
% 1.57/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.57/0.56    inference(cnf_transformation,[],[f2])).
% 1.57/0.56  fof(f2,axiom,(
% 1.57/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.57/0.56  fof(f96,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.57/0.56    inference(resolution,[],[f26,f33])).
% 1.57/0.56  fof(f33,plain,(
% 1.57/0.56    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,k1_relat_1(X0))) )),
% 1.57/0.56    inference(equality_resolution,[],[f24])).
% 1.57/0.56  fof(f24,plain,(
% 1.57/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f1])).
% 1.57/0.56  fof(f1,axiom,(
% 1.57/0.56    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.57/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.57/0.56  fof(f26,plain,(
% 1.57/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 1.57/0.56    inference(cnf_transformation,[],[f1])).
% 1.57/0.56  % SZS output end Proof for theBenchmark
% 1.57/0.56  % (23889)------------------------------
% 1.57/0.56  % (23889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.56  % (23889)Termination reason: Refutation
% 1.57/0.56  
% 1.57/0.56  % (23889)Memory used [KB]: 11769
% 1.57/0.56  % (23889)Time elapsed: 0.146 s
% 1.57/0.56  % (23889)------------------------------
% 1.57/0.56  % (23889)------------------------------
% 1.57/0.56  % (23866)Success in time 0.197 s
%------------------------------------------------------------------------------
