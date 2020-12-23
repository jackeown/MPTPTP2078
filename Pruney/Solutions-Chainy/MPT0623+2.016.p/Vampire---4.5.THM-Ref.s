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
% DateTime   : Thu Dec  3 12:52:04 EST 2020

% Result     : Theorem 1.87s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 563 expanded)
%              Number of leaves         :    9 ( 122 expanded)
%              Depth                    :   26
%              Number of atoms          :  197 (1931 expanded)
%              Number of equality atoms :  114 (1047 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f299,plain,(
    $false ),
    inference(resolution,[],[f191,f45])).

fof(f45,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f191,plain,(
    ! [X0] : ~ r1_tarski(X0,sK0) ),
    inference(superposition,[],[f127,f147])).

fof(f147,plain,(
    ! [X0,X1] : X0 = X1 ),
    inference(superposition,[],[f141,f141])).

fof(f141,plain,(
    ! [X7] : k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK0)) = X7 ),
    inference(forward_demodulation,[],[f138,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK6(X0,X1) ) ),
    inference(subsumption_resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ v1_relat_1(sK6(X0,X1))
      | k1_xboole_0 = sK6(X0,X1) ) ),
    inference(superposition,[],[f22,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f138,plain,(
    ! [X7] : k1_funct_1(sK6(k1_xboole_0,X7),sK4(k1_xboole_0,sK0)) = X7 ),
    inference(resolution,[],[f91,f127])).

fof(f91,plain,(
    ! [X6,X4,X5] :
      ( r1_tarski(X4,X6)
      | k1_funct_1(sK6(X4,X5),sK4(X4,X6)) = X5 ) ),
    inference(resolution,[],[f41,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | k1_funct_1(sK6(X0,X1),X3) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(backward_demodulation,[],[f79,f121])).

fof(f121,plain,(
    k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(equality_resolution,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( sK1 != X0
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f106,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => ! [X1] :
        ? [X2] :
          ( k2_relat_1(X2) = k1_tarski(X1)
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).

fof(f106,plain,(
    ! [X0] :
      ( sK1 != k1_relat_1(sK2(X0,sK3(sK0)))
      | k1_xboole_0 = sK1
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f105,f87])).

fof(f87,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f86,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f83,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_tarski(X3),sK0)
      | ~ v1_funct_1(sK2(X2,X3))
      | sK1 != k1_relat_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f20,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X2] :
      ( ~ r1_tarski(k2_relat_1(X2),sK0)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != sK1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ! [X2] :
          ( ~ r1_tarski(k2_relat_1(X2),X0)
          | k1_relat_1(X2) != X1
          | ~ v1_funct_1(X2)
          | ~ v1_relat_1(X2) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 != X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ~ ( ! [X2] :
              ( ( v1_funct_1(X2)
                & v1_relat_1(X2) )
             => ~ ( r1_tarski(k2_relat_1(X2),X0)
                  & k1_relat_1(X2) = X1 ) )
          & ~ ( k1_xboole_0 != X1
              & k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).

fof(f105,plain,
    ( r1_tarski(k1_tarski(sK3(sK0)),sK0)
    | k1_xboole_0 = sK1 ),
    inference(subsumption_resolution,[],[f103,f21])).

fof(f21,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f12])).

% (31118)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f103,plain,
    ( r1_tarski(k1_tarski(sK3(sK0)),sK0)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f101,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r1_tarski(k1_tarski(X0),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f36,f100])).

fof(f100,plain,(
    ! [X0] :
      ( sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0 ) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( sK1 != X0
      | sK4(k1_tarski(X1),sK0) = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f92,f28])).

fof(f92,plain,(
    ! [X0,X1] :
      ( sK1 != k1_relat_1(sK2(X1,X0))
      | sK4(k1_tarski(X0),sK0) = X0
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f53,f87])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | sK4(k1_tarski(X0),X1) = X0 ) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f79,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(forward_demodulation,[],[f78,f59])).

fof(f59,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f44,f58])).

fof(f78,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | sK1 != k1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f42,f58])).

fof(f77,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | sK1 != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f74,f60])).

fof(f60,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f43,f58])).

fof(f43,plain,(
    ! [X0,X1] : v1_funct_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | sK1 != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f20,f72])).

% (31120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (31117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (31118)Refutation not found, incomplete strategy% (31118)------------------------------
% (31118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f72,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f70,f59])).

fof(f70,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f25,f61])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:18:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.56  % (31097)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.23/0.57  % (31114)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.23/0.57  % (31106)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.23/0.58  % (31106)Refutation not found, incomplete strategy% (31106)------------------------------
% 0.23/0.58  % (31106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.58  % (31098)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.58  % (31102)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.23/0.58  % (31107)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.23/0.58  % (31106)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.58  
% 0.23/0.58  % (31106)Memory used [KB]: 10618
% 0.23/0.58  % (31106)Time elapsed: 0.139 s
% 0.23/0.58  % (31106)------------------------------
% 0.23/0.58  % (31106)------------------------------
% 0.23/0.58  % (31123)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.65/0.58  % (31101)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.65/0.59  % (31113)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.65/0.59  % (31113)Refutation not found, incomplete strategy% (31113)------------------------------
% 1.65/0.59  % (31113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (31113)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (31113)Memory used [KB]: 10618
% 1.65/0.59  % (31113)Time elapsed: 0.149 s
% 1.65/0.59  % (31113)------------------------------
% 1.65/0.59  % (31113)------------------------------
% 1.65/0.59  % (31119)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.65/0.59  % (31105)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.65/0.59  % (31108)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.65/0.59  % (31098)Refutation not found, incomplete strategy% (31098)------------------------------
% 1.65/0.59  % (31098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.59  % (31098)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.59  
% 1.65/0.59  % (31098)Memory used [KB]: 10746
% 1.65/0.59  % (31098)Time elapsed: 0.121 s
% 1.65/0.59  % (31098)------------------------------
% 1.65/0.59  % (31098)------------------------------
% 1.65/0.60  % (31096)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.65/0.60  % (31096)Refutation not found, incomplete strategy% (31096)------------------------------
% 1.65/0.60  % (31096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.60  % (31096)Termination reason: Refutation not found, incomplete strategy
% 1.65/0.60  
% 1.65/0.60  % (31096)Memory used [KB]: 1663
% 1.65/0.60  % (31096)Time elapsed: 0.162 s
% 1.65/0.60  % (31096)------------------------------
% 1.65/0.60  % (31096)------------------------------
% 1.65/0.60  % (31111)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.65/0.60  % (31099)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.65/0.60  % (31112)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.65/0.60  % (31121)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.87/0.60  % (31100)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.87/0.61  % (31102)Refutation found. Thanks to Tanya!
% 1.87/0.61  % SZS status Theorem for theBenchmark
% 1.87/0.61  % SZS output start Proof for theBenchmark
% 1.87/0.61  fof(f299,plain,(
% 1.87/0.61    $false),
% 1.87/0.61    inference(resolution,[],[f191,f45])).
% 1.87/0.61  fof(f45,plain,(
% 1.87/0.61    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.87/0.61    inference(equality_resolution,[],[f32])).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.87/0.61    inference(cnf_transformation,[],[f3])).
% 1.87/0.61  fof(f3,axiom,(
% 1.87/0.61    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.87/0.61  fof(f191,plain,(
% 1.87/0.61    ( ! [X0] : (~r1_tarski(X0,sK0)) )),
% 1.87/0.61    inference(superposition,[],[f127,f147])).
% 1.87/0.61  fof(f147,plain,(
% 1.87/0.61    ( ! [X0,X1] : (X0 = X1) )),
% 1.87/0.61    inference(superposition,[],[f141,f141])).
% 1.87/0.61  fof(f141,plain,(
% 1.87/0.61    ( ! [X7] : (k1_funct_1(k1_xboole_0,sK4(k1_xboole_0,sK0)) = X7) )),
% 1.87/0.61    inference(forward_demodulation,[],[f138,f58])).
% 1.87/0.61  fof(f58,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.87/0.61    inference(equality_resolution,[],[f57])).
% 1.87/0.61  fof(f57,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = sK6(X0,X1)) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f56,f42])).
% 1.87/0.61  fof(f42,plain,(
% 1.87/0.61    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f19,plain,(
% 1.87/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.87/0.61    inference(ennf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.87/0.61  fof(f56,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~v1_relat_1(sK6(X0,X1)) | k1_xboole_0 = sK6(X0,X1)) )),
% 1.87/0.61    inference(superposition,[],[f22,f44])).
% 1.87/0.61  fof(f44,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f22,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f14])).
% 1.87/0.61  fof(f14,plain,(
% 1.87/0.61    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(flattening,[],[f13])).
% 1.87/0.61  fof(f13,plain,(
% 1.87/0.61    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f5])).
% 1.87/0.61  fof(f5,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 1.87/0.61  fof(f138,plain,(
% 1.87/0.61    ( ! [X7] : (k1_funct_1(sK6(k1_xboole_0,X7),sK4(k1_xboole_0,sK0)) = X7) )),
% 1.87/0.61    inference(resolution,[],[f91,f127])).
% 1.87/0.61  fof(f91,plain,(
% 1.87/0.61    ( ! [X6,X4,X5] : (r1_tarski(X4,X6) | k1_funct_1(sK6(X4,X5),sK4(X4,X6)) = X5) )),
% 1.87/0.61    inference(resolution,[],[f41,f35])).
% 1.87/0.61  fof(f35,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,plain,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f1])).
% 1.87/0.61  fof(f1,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.87/0.61  fof(f41,plain,(
% 1.87/0.61    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | k1_funct_1(sK6(X0,X1),X3) = X1) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f127,plain,(
% 1.87/0.61    ~r1_tarski(k1_xboole_0,sK0)),
% 1.87/0.61    inference(trivial_inequality_removal,[],[f123])).
% 1.87/0.61  fof(f123,plain,(
% 1.87/0.61    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(k1_xboole_0,sK0)),
% 1.87/0.61    inference(backward_demodulation,[],[f79,f121])).
% 1.87/0.61  fof(f121,plain,(
% 1.87/0.61    k1_xboole_0 = sK1),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f120])).
% 1.87/0.61  fof(f120,plain,(
% 1.87/0.61    k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.87/0.61    inference(equality_resolution,[],[f119])).
% 1.87/0.61  fof(f119,plain,(
% 1.87/0.61    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = sK1 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f118])).
% 1.87/0.61  fof(f118,plain,(
% 1.87/0.61    ( ! [X0] : (sK1 != X0 | k1_xboole_0 = sK1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(superposition,[],[f106,f28])).
% 1.87/0.61  fof(f28,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f16,plain,(
% 1.87/0.61    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.87/0.61    inference(ennf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_funct_1)).
% 1.87/0.61  fof(f106,plain,(
% 1.87/0.61    ( ! [X0] : (sK1 != k1_relat_1(sK2(X0,sK3(sK0))) | k1_xboole_0 = sK1 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(resolution,[],[f105,f87])).
% 1.87/0.61  fof(f87,plain,(
% 1.87/0.61    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f86,f26])).
% 1.87/0.61  fof(f26,plain,(
% 1.87/0.61    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f86,plain,(
% 1.87/0.61    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.87/0.61    inference(subsumption_resolution,[],[f83,f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f83,plain,(
% 1.87/0.61    ( ! [X2,X3] : (~r1_tarski(k1_tarski(X3),sK0) | ~v1_funct_1(sK2(X2,X3)) | sK1 != k1_relat_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | k1_xboole_0 = X2) )),
% 1.87/0.61    inference(superposition,[],[f20,f29])).
% 1.87/0.61  fof(f29,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f16])).
% 1.87/0.61  fof(f20,plain,(
% 1.87/0.61    ( ! [X2] : (~r1_tarski(k2_relat_1(X2),sK0) | ~v1_funct_1(X2) | k1_relat_1(X2) != sK1 | ~v1_relat_1(X2)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,plain,(
% 1.87/0.61    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.87/0.61    inference(flattening,[],[f11])).
% 1.87/0.61  fof(f11,plain,(
% 1.87/0.61    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f10])).
% 1.87/0.61  fof(f10,negated_conjecture,(
% 1.87/0.61    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.87/0.61    inference(negated_conjecture,[],[f9])).
% 1.87/0.61  fof(f9,conjecture,(
% 1.87/0.61    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_1)).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    r1_tarski(k1_tarski(sK3(sK0)),sK0) | k1_xboole_0 = sK1),
% 1.87/0.61    inference(subsumption_resolution,[],[f103,f21])).
% 1.87/0.61  fof(f21,plain,(
% 1.87/0.61    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.87/0.61    inference(cnf_transformation,[],[f12])).
% 1.87/0.61  % (31118)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.87/0.61  fof(f103,plain,(
% 1.87/0.61    r1_tarski(k1_tarski(sK3(sK0)),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.87/0.61    inference(resolution,[],[f101,f30])).
% 1.87/0.61  fof(f30,plain,(
% 1.87/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f17])).
% 1.87/0.61  fof(f17,plain,(
% 1.87/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.87/0.61    inference(ennf_transformation,[],[f2])).
% 1.87/0.61  fof(f2,axiom,(
% 1.87/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.87/0.61  fof(f101,plain,(
% 1.87/0.61    ( ! [X0] : (~r2_hidden(X0,sK0) | r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) )),
% 1.87/0.61    inference(superposition,[],[f36,f100])).
% 1.87/0.61  fof(f100,plain,(
% 1.87/0.61    ( ! [X0] : (sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = sK1) )),
% 1.87/0.61    inference(equality_resolution,[],[f99])).
% 1.87/0.61  fof(f99,plain,(
% 1.87/0.61    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(duplicate_literal_removal,[],[f98])).
% 1.87/0.61  fof(f98,plain,(
% 1.87/0.61    ( ! [X0,X1] : (sK1 != X0 | sK4(k1_tarski(X1),sK0) = X1 | k1_xboole_0 = X0 | k1_xboole_0 = X0) )),
% 1.87/0.61    inference(superposition,[],[f92,f28])).
% 1.87/0.61  fof(f92,plain,(
% 1.87/0.61    ( ! [X0,X1] : (sK1 != k1_relat_1(sK2(X1,X0)) | sK4(k1_tarski(X0),sK0) = X0 | k1_xboole_0 = X1) )),
% 1.87/0.61    inference(resolution,[],[f53,f87])).
% 1.87/0.61  fof(f53,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | sK4(k1_tarski(X0),X1) = X0) )),
% 1.87/0.61    inference(resolution,[],[f35,f47])).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.87/0.61    inference(equality_resolution,[],[f38])).
% 1.87/0.61  fof(f38,plain,(
% 1.87/0.61    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.87/0.61    inference(cnf_transformation,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.87/0.61  fof(f36,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f18])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    ~r1_tarski(k1_xboole_0,sK0) | k1_xboole_0 != sK1),
% 1.87/0.61    inference(forward_demodulation,[],[f78,f59])).
% 1.87/0.61  fof(f59,plain,(
% 1.87/0.61    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f44,f58])).
% 1.87/0.61  fof(f78,plain,(
% 1.87/0.61    ~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f77,f61])).
% 1.87/0.61  fof(f61,plain,(
% 1.87/0.61    v1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f42,f58])).
% 1.87/0.61  fof(f77,plain,(
% 1.87/0.61    ~r1_tarski(k1_xboole_0,sK0) | sK1 != k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f74,f60])).
% 1.87/0.61  fof(f60,plain,(
% 1.87/0.61    v1_funct_1(k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f43,f58])).
% 1.87/0.61  fof(f43,plain,(
% 1.87/0.61    ( ! [X0,X1] : (v1_funct_1(sK6(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f19])).
% 1.87/0.61  fof(f74,plain,(
% 1.87/0.61    ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | sK1 != k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(superposition,[],[f20,f72])).
% 1.87/0.61  % (31120)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.61  % (31117)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.87/0.61  % (31118)Refutation not found, incomplete strategy% (31118)------------------------------
% 1.87/0.61  % (31118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  fof(f72,plain,(
% 1.87/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f70,f59])).
% 1.87/0.61  fof(f70,plain,(
% 1.87/0.61    k1_xboole_0 = k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.87/0.61    inference(resolution,[],[f25,f61])).
% 1.87/0.61  fof(f25,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f15])).
% 1.87/0.61  fof(f15,plain,(
% 1.87/0.61    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (31102)------------------------------
% 1.87/0.61  % (31102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (31102)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (31102)Memory used [KB]: 6268
% 1.87/0.61  % (31102)Time elapsed: 0.181 s
% 1.87/0.61  % (31102)------------------------------
% 1.87/0.61  % (31102)------------------------------
% 1.87/0.61  % (31095)Success in time 0.241 s
%------------------------------------------------------------------------------
