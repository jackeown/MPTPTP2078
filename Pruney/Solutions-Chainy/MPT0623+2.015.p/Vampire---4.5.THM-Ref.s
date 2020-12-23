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

% Result     : Theorem 1.35s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 241 expanded)
%              Number of leaves         :    9 (  60 expanded)
%              Depth                    :   14
%              Number of atoms          :  192 ( 785 expanded)
%              Number of equality atoms :   85 ( 329 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f674,plain,(
    $false ),
    inference(global_subsumption,[],[f20,f668,f672])).

fof(f672,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f635,f272])).

fof(f272,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK0)
      | k1_xboole_0 = sK1
      | sK0 = X0 ) ),
    inference(resolution,[],[f268,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f268,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f265,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f265,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f242,f160])).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(duplicate_literal_removal,[],[f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f111,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k2_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).

fof(f111,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0)
      | k1_xboole_0 = sK1 ) ),
    inference(equality_resolution,[],[f110])).

fof(f110,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | k1_xboole_0 = X2 ) ),
    inference(global_subsumption,[],[f26,f25,f109])).

fof(f109,plain,(
    ! [X2,X3] :
      ( sK1 != X2
      | ~ v1_funct_1(sK2(X2,X3))
      | ~ v1_relat_1(sK2(X2,X3))
      | ~ r1_tarski(k2_relat_1(sK2(X2,X3)),sK0)
      | k1_xboole_0 = X2 ) ),
    inference(superposition,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK2(X0,X1)) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f19,plain,(
    ! [X2] :
      ( k1_relat_1(X2) != sK1
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(k2_relat_1(X2),sK0) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK2(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f242,plain,(
    ! [X4,X5] :
      ( r1_tarski(k1_tarski(X4),X5)
      | ~ r2_hidden(X4,X5) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | r1_tarski(k1_tarski(X4),X5)
      | r1_tarski(k1_tarski(X4),X5) ) ),
    inference(superposition,[],[f38,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( sK4(k1_tarski(X0),X1) = X0
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f635,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f47,f569,f153])).

fof(f153,plain,(
    ! [X4,X2,X3] :
      ( r2_hidden(sK4(X2,X3),X4)
      | ~ r1_tarski(X2,X4)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f36,f37])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f569,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f47,f568])).

fof(f568,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r1_tarski(X1,sK0) ) ),
    inference(duplicate_literal_removal,[],[f565])).

fof(f565,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK0)
      | ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f390,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k1_xboole_0,X1) = X0
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(superposition,[],[f43,f80])).

fof(f80,plain,(
    ! [X0] : k1_xboole_0 = sK6(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f44,f46,f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f46,plain,(
    ! [X0,X1] : k1_relat_1(sK6(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(sK6(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k1_funct_1(sK6(X0,X1),X3) = X1
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f390,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_funct_1(k1_xboole_0,X0),sK0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f145,f169])).

fof(f145,plain,(
    ~ r1_tarski(k1_tarski(sK4(k2_relat_1(sK3(sK1)),sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f75,f51,f36])).

fof(f51,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ~ r2_hidden(sK4(k2_relat_1(sK3(sK1)),sK0),sK0) ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f52,plain,(
    ~ r1_tarski(k2_relat_1(sK3(sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f30,f32,f19])).

fof(f32,plain,(
    ! [X0] : k1_relat_1(sK3(X0)) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f30,plain,(
    ! [X0] : v1_relat_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ! [X0] : v1_funct_1(sK3(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f668,plain,(
    k1_xboole_0 != sK1 ),
    inference(unit_resulting_resolution,[],[f88,f87,f635,f55])).

fof(f55,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,sK0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f53,f22])).

fof(f22,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f53,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),sK0) ),
    inference(superposition,[],[f19,f21])).

fof(f21,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f87,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f31,f79])).

fof(f79,plain,(
    k1_xboole_0 = sK3(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f30,f32,f23])).

fof(f88,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f30,f79])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:19:51 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.53  % (5193)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.53  % (5185)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.53  % (5191)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.53  % (5177)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.53  % (5177)Refutation not found, incomplete strategy% (5177)------------------------------
% 0.22/0.53  % (5177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5175)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (5177)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5177)Memory used [KB]: 10746
% 0.22/0.53  % (5177)Time elapsed: 0.108 s
% 0.22/0.53  % (5177)------------------------------
% 0.22/0.53  % (5177)------------------------------
% 0.22/0.54  % (5178)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (5194)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (5186)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (5169)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.35/0.55  % (5183)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.35/0.55  % (5173)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.35/0.55  % (5178)Refutation not found, incomplete strategy% (5178)------------------------------
% 1.35/0.55  % (5178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (5191)Refutation not found, incomplete strategy% (5191)------------------------------
% 1.35/0.55  % (5191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (5191)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (5191)Memory used [KB]: 10746
% 1.35/0.55  % (5191)Time elapsed: 0.134 s
% 1.35/0.55  % (5191)------------------------------
% 1.35/0.55  % (5191)------------------------------
% 1.35/0.55  % (5186)Refutation not found, incomplete strategy% (5186)------------------------------
% 1.35/0.55  % (5186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (5186)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (5186)Memory used [KB]: 10618
% 1.35/0.55  % (5186)Time elapsed: 0.138 s
% 1.35/0.55  % (5186)------------------------------
% 1.35/0.55  % (5186)------------------------------
% 1.35/0.55  % (5192)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.55  % (5178)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.55  
% 1.35/0.55  % (5178)Memory used [KB]: 10618
% 1.35/0.55  % (5178)Time elapsed: 0.138 s
% 1.35/0.55  % (5178)------------------------------
% 1.35/0.55  % (5178)------------------------------
% 1.35/0.56  % (5180)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.56  % (5176)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.56  % (5195)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.56  % (5193)Refutation found. Thanks to Tanya!
% 1.35/0.56  % SZS status Theorem for theBenchmark
% 1.35/0.56  % (5189)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.35/0.56  % (5188)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.56  % (5171)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.35/0.56  % (5179)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.35/0.56  % (5171)Refutation not found, incomplete strategy% (5171)------------------------------
% 1.35/0.56  % (5171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (5171)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (5171)Memory used [KB]: 10746
% 1.35/0.56  % (5171)Time elapsed: 0.138 s
% 1.35/0.56  % (5171)------------------------------
% 1.35/0.56  % (5171)------------------------------
% 1.35/0.56  % (5179)Refutation not found, incomplete strategy% (5179)------------------------------
% 1.35/0.56  % (5179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.56  % (5179)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.56  
% 1.35/0.56  % (5179)Memory used [KB]: 10618
% 1.35/0.56  % (5179)Time elapsed: 0.146 s
% 1.35/0.56  % (5179)------------------------------
% 1.35/0.56  % (5179)------------------------------
% 1.35/0.57  % (5174)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.57  % (5197)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.58/0.57  % (5187)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.57  % (5182)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.58/0.57  % (5169)Refutation not found, incomplete strategy% (5169)------------------------------
% 1.58/0.57  % (5169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (5169)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (5169)Memory used [KB]: 1663
% 1.58/0.57  % (5169)Time elapsed: 0.141 s
% 1.58/0.57  % (5169)------------------------------
% 1.58/0.57  % (5169)------------------------------
% 1.58/0.57  % (5196)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.57  % (5170)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.57  % (5181)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.57  % (5184)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.57  % (5172)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.57  % SZS output start Proof for theBenchmark
% 1.58/0.57  fof(f674,plain,(
% 1.58/0.57    $false),
% 1.58/0.57    inference(global_subsumption,[],[f20,f668,f672])).
% 1.58/0.57  fof(f672,plain,(
% 1.58/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.58/0.57    inference(resolution,[],[f635,f272])).
% 1.58/0.57  fof(f272,plain,(
% 1.58/0.57    ( ! [X0] : (~r1_tarski(X0,sK0) | k1_xboole_0 = sK1 | sK0 = X0) )),
% 1.58/0.57    inference(resolution,[],[f268,f35])).
% 1.58/0.57  fof(f35,plain,(
% 1.58/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.58/0.57    inference(cnf_transformation,[],[f2])).
% 1.58/0.58  fof(f2,axiom,(
% 1.58/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.58  fof(f268,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(sK0,X0) | k1_xboole_0 = sK1) )),
% 1.58/0.58    inference(resolution,[],[f265,f37])).
% 1.58/0.58  fof(f37,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f17])).
% 1.58/0.58  fof(f17,plain,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.58/0.58    inference(ennf_transformation,[],[f1])).
% 1.58/0.58  fof(f1,axiom,(
% 1.58/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.58/0.58  fof(f265,plain,(
% 1.58/0.58    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK1) )),
% 1.58/0.58    inference(resolution,[],[f242,f160])).
% 1.58/0.58  fof(f160,plain,(
% 1.58/0.58    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f158])).
% 1.58/0.58  fof(f158,plain,(
% 1.58/0.58    ( ! [X0] : (~r1_tarski(k1_tarski(X0),sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK1) )),
% 1.58/0.58    inference(superposition,[],[f111,f28])).
% 1.58/0.58  fof(f28,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_tarski(X1) = k2_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f15,plain,(
% 1.58/0.58    ! [X0] : (! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) | k1_xboole_0 = X0)),
% 1.58/0.58    inference(ennf_transformation,[],[f8])).
% 1.58/0.58  fof(f8,axiom,(
% 1.58/0.58    ! [X0] : (k1_xboole_0 != X0 => ! [X1] : ? [X2] : (k2_relat_1(X2) = k1_tarski(X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_funct_1)).
% 1.58/0.58  fof(f111,plain,(
% 1.58/0.58    ( ! [X0] : (~r1_tarski(k2_relat_1(sK2(sK1,X0)),sK0) | k1_xboole_0 = sK1) )),
% 1.58/0.58    inference(equality_resolution,[],[f110])).
% 1.58/0.58  fof(f110,plain,(
% 1.58/0.58    ( ! [X2,X3] : (sK1 != X2 | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | k1_xboole_0 = X2) )),
% 1.58/0.58    inference(global_subsumption,[],[f26,f25,f109])).
% 1.58/0.58  fof(f109,plain,(
% 1.58/0.58    ( ! [X2,X3] : (sK1 != X2 | ~v1_funct_1(sK2(X2,X3)) | ~v1_relat_1(sK2(X2,X3)) | ~r1_tarski(k2_relat_1(sK2(X2,X3)),sK0) | k1_xboole_0 = X2) )),
% 1.58/0.58    inference(superposition,[],[f19,f27])).
% 1.58/0.58  fof(f27,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0 | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f19,plain,(
% 1.58/0.58    ( ! [X2] : (k1_relat_1(X2) != sK1 | ~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r1_tarski(k2_relat_1(X2),sK0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f12])).
% 1.58/0.58  fof(f12,plain,(
% 1.58/0.58    ? [X0,X1] : (! [X2] : (~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.58/0.58    inference(flattening,[],[f11])).
% 1.58/0.58  fof(f11,plain,(
% 1.58/0.58    ? [X0,X1] : (! [X2] : ((~r1_tarski(k2_relat_1(X2),X0) | k1_relat_1(X2) != X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2))) & (k1_xboole_0 = X1 | k1_xboole_0 != X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f10])).
% 1.58/0.58  fof(f10,negated_conjecture,(
% 1.58/0.58    ~! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.58/0.58    inference(negated_conjecture,[],[f9])).
% 1.58/0.58  fof(f9,conjecture,(
% 1.58/0.58    ! [X0,X1] : ~(! [X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ~(r1_tarski(k2_relat_1(X2),X0) & k1_relat_1(X2) = X1)) & ~(k1_xboole_0 != X1 & k1_xboole_0 = X0))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).
% 1.58/0.58  fof(f25,plain,(
% 1.58/0.58    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f26,plain,(
% 1.58/0.58    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1)) | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f15])).
% 1.58/0.58  fof(f242,plain,(
% 1.58/0.58    ( ! [X4,X5] : (r1_tarski(k1_tarski(X4),X5) | ~r2_hidden(X4,X5)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f239])).
% 1.58/0.58  fof(f239,plain,(
% 1.58/0.58    ( ! [X4,X5] : (~r2_hidden(X4,X5) | r1_tarski(k1_tarski(X4),X5) | r1_tarski(k1_tarski(X4),X5)) )),
% 1.58/0.58    inference(superposition,[],[f38,f74])).
% 1.58/0.58  fof(f74,plain,(
% 1.58/0.58    ( ! [X0,X1] : (sK4(k1_tarski(X0),X1) = X0 | r1_tarski(k1_tarski(X0),X1)) )),
% 1.58/0.58    inference(resolution,[],[f37,f49])).
% 1.58/0.58  fof(f49,plain,(
% 1.58/0.58    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 1.58/0.58    inference(equality_resolution,[],[f40])).
% 1.58/0.58  fof(f40,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f3])).
% 1.58/0.58  fof(f3,axiom,(
% 1.58/0.58    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 1.58/0.58  fof(f38,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f17])).
% 1.58/0.58  fof(f635,plain,(
% 1.58/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f47,f569,f153])).
% 1.58/0.58  fof(f153,plain,(
% 1.58/0.58    ( ! [X4,X2,X3] : (r2_hidden(sK4(X2,X3),X4) | ~r1_tarski(X2,X4) | r1_tarski(X2,X3)) )),
% 1.58/0.58    inference(resolution,[],[f36,f37])).
% 1.58/0.58  fof(f36,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f17])).
% 1.58/0.58  fof(f569,plain,(
% 1.58/0.58    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f47,f568])).
% 1.58/0.58  fof(f568,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r1_tarski(X1,sK0)) )),
% 1.58/0.58    inference(duplicate_literal_removal,[],[f565])).
% 1.58/0.58  fof(f565,plain,(
% 1.58/0.58    ( ! [X0,X1] : (~r1_tarski(X1,sK0) | ~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.58/0.58    inference(superposition,[],[f390,f169])).
% 1.58/0.58  fof(f169,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_funct_1(k1_xboole_0,X1) = X0 | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.58/0.58    inference(superposition,[],[f43,f80])).
% 1.58/0.58  fof(f80,plain,(
% 1.58/0.58    ( ! [X0] : (k1_xboole_0 = sK6(k1_xboole_0,X0)) )),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f44,f46,f23])).
% 1.58/0.58  fof(f23,plain,(
% 1.58/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f14])).
% 1.58/0.58  fof(f14,plain,(
% 1.58/0.58    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.58/0.58    inference(flattening,[],[f13])).
% 1.58/0.58  fof(f13,plain,(
% 1.58/0.58    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.58/0.58    inference(ennf_transformation,[],[f5])).
% 1.58/0.58  fof(f5,axiom,(
% 1.58/0.58    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.58/0.58  fof(f46,plain,(
% 1.58/0.58    ( ! [X0,X1] : (k1_relat_1(sK6(X0,X1)) = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f18])).
% 1.58/0.58  fof(f18,plain,(
% 1.58/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.58/0.58    inference(ennf_transformation,[],[f6])).
% 1.58/0.58  fof(f6,axiom,(
% 1.58/0.58    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 1.58/0.58  fof(f44,plain,(
% 1.58/0.58    ( ! [X0,X1] : (v1_relat_1(sK6(X0,X1))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f18])).
% 1.58/0.58  fof(f43,plain,(
% 1.58/0.58    ( ! [X0,X3,X1] : (k1_funct_1(sK6(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f18])).
% 1.58/0.58  fof(f390,plain,(
% 1.58/0.58    ( ! [X0] : (~r1_tarski(k1_funct_1(k1_xboole_0,X0),sK0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.58/0.58    inference(superposition,[],[f145,f169])).
% 1.58/0.58  fof(f145,plain,(
% 1.58/0.58    ~r1_tarski(k1_tarski(sK4(k2_relat_1(sK3(sK1)),sK0)),sK0)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f75,f51,f36])).
% 1.58/0.58  fof(f51,plain,(
% 1.58/0.58    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 1.58/0.58    inference(equality_resolution,[],[f50])).
% 1.58/0.58  fof(f50,plain,(
% 1.58/0.58    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 1.58/0.58    inference(equality_resolution,[],[f39])).
% 1.58/0.58  fof(f39,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f3])).
% 1.58/0.58  fof(f75,plain,(
% 1.58/0.58    ~r2_hidden(sK4(k2_relat_1(sK3(sK1)),sK0),sK0)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f52,f38])).
% 1.58/0.58  fof(f52,plain,(
% 1.58/0.58    ~r1_tarski(k2_relat_1(sK3(sK1)),sK0)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f31,f30,f32,f19])).
% 1.58/0.58  fof(f32,plain,(
% 1.58/0.58    ( ! [X0] : (k1_relat_1(sK3(X0)) = X0) )),
% 1.58/0.58    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f16,plain,(
% 1.58/0.58    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.58/0.58    inference(ennf_transformation,[],[f7])).
% 1.58/0.58  fof(f7,axiom,(
% 1.58/0.58    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).
% 1.58/0.58  fof(f30,plain,(
% 1.58/0.58    ( ! [X0] : (v1_relat_1(sK3(X0))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f31,plain,(
% 1.58/0.58    ( ! [X0] : (v1_funct_1(sK3(X0))) )),
% 1.58/0.58    inference(cnf_transformation,[],[f16])).
% 1.58/0.58  fof(f47,plain,(
% 1.58/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.58    inference(equality_resolution,[],[f34])).
% 1.58/0.58  fof(f34,plain,(
% 1.58/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.58    inference(cnf_transformation,[],[f2])).
% 1.58/0.58  fof(f668,plain,(
% 1.58/0.58    k1_xboole_0 != sK1),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f88,f87,f635,f55])).
% 1.58/0.58  fof(f55,plain,(
% 1.58/0.58    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,sK0) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 1.58/0.58    inference(forward_demodulation,[],[f53,f22])).
% 1.58/0.58  fof(f22,plain,(
% 1.58/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.58/0.58    inference(cnf_transformation,[],[f4])).
% 1.58/0.58  fof(f4,axiom,(
% 1.58/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.58/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 1.58/0.58  fof(f53,plain,(
% 1.58/0.58    k1_xboole_0 != sK1 | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),sK0)),
% 1.58/0.58    inference(superposition,[],[f19,f21])).
% 1.58/0.58  fof(f21,plain,(
% 1.58/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.58/0.58    inference(cnf_transformation,[],[f4])).
% 1.58/0.58  fof(f87,plain,(
% 1.58/0.58    v1_funct_1(k1_xboole_0)),
% 1.58/0.58    inference(superposition,[],[f31,f79])).
% 1.58/0.58  fof(f79,plain,(
% 1.58/0.58    k1_xboole_0 = sK3(k1_xboole_0)),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f30,f32,f23])).
% 1.58/0.58  fof(f88,plain,(
% 1.58/0.58    v1_relat_1(k1_xboole_0)),
% 1.58/0.58    inference(superposition,[],[f30,f79])).
% 1.58/0.58  fof(f20,plain,(
% 1.58/0.58    k1_xboole_0 != sK0 | k1_xboole_0 = sK1),
% 1.58/0.58    inference(cnf_transformation,[],[f12])).
% 1.58/0.58  % SZS output end Proof for theBenchmark
% 1.58/0.58  % (5193)------------------------------
% 1.58/0.58  % (5193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (5193)Termination reason: Refutation
% 1.58/0.58  
% 1.58/0.58  % (5193)Memory used [KB]: 6780
% 1.58/0.58  % (5193)Time elapsed: 0.130 s
% 1.58/0.58  % (5193)------------------------------
% 1.58/0.58  % (5193)------------------------------
% 1.58/0.58  % (5168)Success in time 0.198 s
%------------------------------------------------------------------------------
