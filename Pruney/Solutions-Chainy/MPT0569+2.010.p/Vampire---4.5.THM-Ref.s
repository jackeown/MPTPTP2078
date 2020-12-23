%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:27 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 207 expanded)
%              Number of leaves         :   10 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 579 expanded)
%              Number of equality atoms :   27 (  82 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f900,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f177,f220,f899])).

fof(f899,plain,
    ( ~ spl12_1
    | spl12_2 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | ~ spl12_1
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f26,f888,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f888,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl12_1
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f882,f882,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f882,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl12_1
    | spl12_2 ),
    inference(forward_demodulation,[],[f858,f72])).

fof(f72,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl12_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f858,plain,
    ( r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f223,f222,f352])).

fof(f352,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK5(sK1,X5),k10_relat_1(sK1,X6))
      | ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X5,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f66,f50])).

fof(f50,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f66,plain,(
    ! [X17,X15,X16] :
      ( ~ r2_hidden(k4_tarski(X15,X16),sK1)
      | ~ r2_hidden(X16,X17)
      | r2_hidden(X15,k10_relat_1(sK1,X17)) ) ),
    inference(resolution,[],[f23,f55])).

fof(f55,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f222,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f221,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f221,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k3_xboole_0(k2_relat_1(sK1),sK0))
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f75,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl12_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f223,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl12_2 ),
    inference(unit_resulting_resolution,[],[f221,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f220,plain,
    ( spl12_1
    | ~ spl12_2 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f26,f182,f24])).

fof(f182,plain,
    ( r2_hidden(sK8(k1_xboole_0,k10_relat_1(sK1,sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f178,f178,f52])).

fof(f178,plain,
    ( r2_hidden(sK8(k1_xboole_0,k10_relat_1(sK1,sK0)),k1_xboole_0)
    | spl12_1
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f106,f71,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK8(X0,X1),X1)
      | r2_hidden(sK8(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f71,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl12_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f106,plain,
    ( ! [X0] : ~ r2_hidden(X0,k10_relat_1(sK1,sK0))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f78,f105])).

fof(f105,plain,
    ( k10_relat_1(sK1,sK0) = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f95,f58])).

fof(f58,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f23,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).

fof(f95,plain,
    ( k3_xboole_0(k2_relat_1(sK1),sK0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f23,f78,f78,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK11(X0,X1,X2),X1)
      | r2_hidden(sK9(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f78,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl12_2 ),
    inference(unit_resulting_resolution,[],[f76,f24])).

fof(f76,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f177,plain,
    ( ~ spl12_1
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f22,f74,f70])).

fof(f22,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f77,plain,
    ( spl12_1
    | spl12_2 ),
    inference(avatar_split_clause,[],[f21,f74,f70])).

fof(f21,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (32691)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (32719)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (32699)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (32695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (32693)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (32701)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (32692)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (32717)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (32718)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (32697)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (32694)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (32714)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (32706)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (32712)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (32715)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (32709)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (32710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (32698)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (32703)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (32707)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (32708)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (32705)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (32700)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (32702)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (32701)Refutation not found, incomplete strategy% (32701)------------------------------
% 0.21/0.56  % (32701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (32716)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (32720)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (32711)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (32701)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (32701)Memory used [KB]: 10746
% 0.21/0.56  % (32701)Time elapsed: 0.141 s
% 0.21/0.56  % (32701)------------------------------
% 0.21/0.56  % (32701)------------------------------
% 0.21/0.56  % (32696)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (32702)Refutation not found, incomplete strategy% (32702)------------------------------
% 0.21/0.57  % (32702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (32702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (32702)Memory used [KB]: 10618
% 0.21/0.57  % (32702)Time elapsed: 0.158 s
% 0.21/0.57  % (32702)------------------------------
% 0.21/0.57  % (32702)------------------------------
% 1.64/0.59  % (32704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.64/0.59  % (32713)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.79/0.60  % (32713)Refutation not found, incomplete strategy% (32713)------------------------------
% 1.79/0.60  % (32713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (32695)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f900,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(avatar_sat_refutation,[],[f77,f177,f220,f899])).
% 1.79/0.60  fof(f899,plain,(
% 1.79/0.60    ~spl12_1 | spl12_2),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f894])).
% 1.79/0.60  fof(f894,plain,(
% 1.79/0.60    $false | (~spl12_1 | spl12_2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f26,f888,f24])).
% 1.79/0.60  fof(f24,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f16])).
% 1.79/0.60  fof(f16,plain,(
% 1.79/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.79/0.60    inference(ennf_transformation,[],[f14])).
% 1.79/0.60  fof(f14,plain,(
% 1.79/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.60    inference(rectify,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.79/0.60  fof(f888,plain,(
% 1.79/0.60    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl12_1 | spl12_2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f882,f882,f52])).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f41])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.79/0.60  fof(f882,plain,(
% 1.79/0.60    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl12_1 | spl12_2)),
% 1.79/0.60    inference(forward_demodulation,[],[f858,f72])).
% 1.79/0.60  fof(f72,plain,(
% 1.79/0.60    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl12_1),
% 1.79/0.60    inference(avatar_component_clause,[],[f70])).
% 1.79/0.60  fof(f70,plain,(
% 1.79/0.60    spl12_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.79/0.60  fof(f858,plain,(
% 1.79/0.60    r2_hidden(sK5(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f223,f222,f352])).
% 1.79/0.60  fof(f352,plain,(
% 1.79/0.60    ( ! [X6,X5] : (r2_hidden(sK5(sK1,X5),k10_relat_1(sK1,X6)) | ~r2_hidden(X5,X6) | ~r2_hidden(X5,k2_relat_1(sK1))) )),
% 1.79/0.60    inference(resolution,[],[f66,f50])).
% 1.79/0.60  fof(f50,plain,(
% 1.79/0.60    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.79/0.60    inference(equality_resolution,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f9])).
% 1.79/0.60  fof(f9,axiom,(
% 1.79/0.60    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.79/0.60  fof(f66,plain,(
% 1.79/0.60    ( ! [X17,X15,X16] : (~r2_hidden(k4_tarski(X15,X16),sK1) | ~r2_hidden(X16,X17) | r2_hidden(X15,k10_relat_1(sK1,X17))) )),
% 1.79/0.60    inference(resolution,[],[f23,f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.79/0.60    inference(equality_resolution,[],[f49])).
% 1.79/0.60  fof(f49,plain,(
% 1.79/0.60    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.79/0.60    inference(ennf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    v1_relat_1(sK1)),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,plain,(
% 1.79/0.60    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,negated_conjecture,(
% 1.79/0.60    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.79/0.60    inference(negated_conjecture,[],[f12])).
% 1.79/0.60  fof(f12,conjecture,(
% 1.79/0.60    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 1.79/0.60  fof(f222,plain,(
% 1.79/0.60    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f221,f54])).
% 1.79/0.60  fof(f54,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(equality_resolution,[],[f39])).
% 1.79/0.60  fof(f39,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f221,plain,(
% 1.79/0.60    r2_hidden(sK2(k2_relat_1(sK1),sK0),k3_xboole_0(k2_relat_1(sK1),sK0)) | spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f75,f25])).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f16])).
% 1.79/0.60  fof(f75,plain,(
% 1.79/0.60    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl12_2),
% 1.79/0.60    inference(avatar_component_clause,[],[f74])).
% 1.79/0.60  fof(f74,plain,(
% 1.79/0.60    spl12_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.79/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.79/0.60  fof(f223,plain,(
% 1.79/0.60    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f221,f53])).
% 1.79/0.60  fof(f53,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.79/0.60    inference(equality_resolution,[],[f40])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f26,plain,(
% 1.79/0.60    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f4])).
% 1.79/0.60  fof(f4,axiom,(
% 1.79/0.60    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.79/0.60  fof(f220,plain,(
% 1.79/0.60    spl12_1 | ~spl12_2),
% 1.79/0.60    inference(avatar_contradiction_clause,[],[f215])).
% 1.79/0.60  fof(f215,plain,(
% 1.79/0.60    $false | (spl12_1 | ~spl12_2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f26,f182,f24])).
% 1.79/0.60  fof(f182,plain,(
% 1.79/0.60    r2_hidden(sK8(k1_xboole_0,k10_relat_1(sK1,sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | (spl12_1 | ~spl12_2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f178,f178,f52])).
% 1.79/0.60  fof(f178,plain,(
% 1.79/0.60    r2_hidden(sK8(k1_xboole_0,k10_relat_1(sK1,sK0)),k1_xboole_0) | (spl12_1 | ~spl12_2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f106,f71,f42])).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(sK8(X0,X1),X1) | r2_hidden(sK8(X0,X1),X0) | X0 = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f19,plain,(
% 1.79/0.60    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.79/0.60    inference(ennf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.79/0.60  fof(f71,plain,(
% 1.79/0.60    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl12_1),
% 1.79/0.60    inference(avatar_component_clause,[],[f70])).
% 1.79/0.60  fof(f106,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k10_relat_1(sK1,sK0))) ) | ~spl12_2),
% 1.79/0.60    inference(backward_demodulation,[],[f78,f105])).
% 1.79/0.60  fof(f105,plain,(
% 1.79/0.60    k10_relat_1(sK1,sK0) = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl12_2),
% 1.79/0.60    inference(forward_demodulation,[],[f95,f58])).
% 1.79/0.60  fof(f58,plain,(
% 1.79/0.60    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f23,f35])).
% 1.79/0.60  fof(f35,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f11])).
% 1.79/0.60  fof(f11,axiom,(
% 1.79/0.60    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.79/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t168_relat_1)).
% 1.79/0.60  fof(f95,plain,(
% 1.79/0.60    k3_xboole_0(k2_relat_1(sK1),sK0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),sK0)) | ~spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f23,f78,f78,f46])).
% 1.79/0.60  fof(f46,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK11(X0,X1,X2),X1) | r2_hidden(sK9(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f20])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k2_relat_1(sK1),sK0))) ) | ~spl12_2),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f76,f24])).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl12_2),
% 1.79/0.60    inference(avatar_component_clause,[],[f74])).
% 1.79/0.60  fof(f177,plain,(
% 1.79/0.60    ~spl12_1 | ~spl12_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f22,f74,f70])).
% 1.79/0.60  fof(f22,plain,(
% 1.79/0.60    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  fof(f77,plain,(
% 1.79/0.60    spl12_1 | spl12_2),
% 1.79/0.60    inference(avatar_split_clause,[],[f21,f74,f70])).
% 1.79/0.60  fof(f21,plain,(
% 1.79/0.60    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f15])).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (32695)------------------------------
% 1.79/0.60  % (32695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (32695)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (32695)Memory used [KB]: 6908
% 1.79/0.60  % (32695)Time elapsed: 0.189 s
% 1.79/0.60  % (32695)------------------------------
% 1.79/0.60  % (32695)------------------------------
% 1.79/0.60  % (32690)Success in time 0.242 s
%------------------------------------------------------------------------------
