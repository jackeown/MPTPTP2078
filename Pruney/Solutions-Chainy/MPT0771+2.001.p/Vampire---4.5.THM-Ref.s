%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:53 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 128 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  158 ( 315 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f1111,f1308])).

fof(f1308,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f1307])).

fof(f1307,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f59,f1306])).

fof(f1306,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0) ),
    inference(forward_demodulation,[],[f1251,f239])).

fof(f239,plain,(
    ! [X0] : k3_relat_1(k2_wellord1(sK1,X0)) = k2_xboole_0(k1_relat_1(k2_wellord1(sK1,X0)),k2_relat_1(k2_wellord1(sK1,X0))) ),
    inference(unit_resulting_resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f67,plain,(
    ! [X0] : v1_relat_1(k2_wellord1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).

fof(f35,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
      | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f32])).

fof(f32,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ( ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        | ~ r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
          & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0)
        & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).

fof(f1251,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_relat_1(k2_wellord1(sK1,X0)),k2_relat_1(k2_wellord1(sK1,X0))),X0) ),
    inference(unit_resulting_resolution,[],[f1136,f1248,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f1248,plain,(
    ! [X1] : r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1) ),
    inference(global_subsumption,[],[f63,f1246])).

fof(f1246,plain,(
    ! [X1] :
      ( r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1)
      | ~ v1_relat_1(k8_relat_1(X1,sK1)) ) ),
    inference(superposition,[],[f46,f752])).

fof(f752,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0) ),
    inference(unit_resulting_resolution,[],[f35,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f1136,plain,(
    ! [X1] : r1_tarski(k2_relat_1(k2_wellord1(sK1,X1)),X1) ),
    inference(global_subsumption,[],[f61,f1134])).

fof(f1134,plain,(
    ! [X1] :
      ( r1_tarski(k2_relat_1(k2_wellord1(sK1,X1)),X1)
      | ~ v1_relat_1(k7_relat_1(sK1,X1)) ) ),
    inference(superposition,[],[f45,f567])).

fof(f567,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).

fof(f61,plain,(
    ! [X0] : v1_relat_1(k7_relat_1(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f59,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_2
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f1111,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f1110])).

fof(f1110,plain,
    ( $false
    | spl2_1 ),
    inference(subsumption_resolution,[],[f55,f1106])).

fof(f1106,plain,(
    ! [X11] : r1_tarski(k3_relat_1(k2_wellord1(sK1,X11)),k3_relat_1(sK1)) ),
    inference(superposition,[],[f985,f432])).

fof(f432,plain,(
    ! [X0] : k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

fof(f985,plain,(
    ! [X0] : r1_tarski(k3_relat_1(k3_xboole_0(sK1,X0)),k3_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f35,f120,f41,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f120,plain,(
    ! [X0] : v1_relat_1(k3_xboole_0(sK1,X0)) ),
    inference(unit_resulting_resolution,[],[f35,f102,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f102,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f55,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f60,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f36,f57,f53])).

fof(f36,plain,
    ( ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)
    | ~ r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:03:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (3684)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (3674)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (3677)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (3674)Refutation not found, incomplete strategy% (3674)------------------------------
% 0.21/0.49  % (3674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3674)Memory used [KB]: 10490
% 0.21/0.49  % (3674)Time elapsed: 0.083 s
% 0.21/0.49  % (3674)------------------------------
% 0.21/0.49  % (3674)------------------------------
% 0.21/0.49  % (3666)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.49  % (3668)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (3676)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.49  % (3680)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (3685)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.50  % (3667)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (3665)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.50  % (3667)Refutation not found, incomplete strategy% (3667)------------------------------
% 0.21/0.50  % (3667)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3667)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3667)Memory used [KB]: 10618
% 0.21/0.50  % (3667)Time elapsed: 0.095 s
% 0.21/0.50  % (3667)------------------------------
% 0.21/0.50  % (3667)------------------------------
% 0.21/0.50  % (3669)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (3686)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (3678)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (3679)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (3675)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (3670)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.51  % (3664)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.51  % (3671)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (3681)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (3671)Refutation not found, incomplete strategy% (3671)------------------------------
% 0.21/0.51  % (3671)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3671)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (3671)Memory used [KB]: 6012
% 0.21/0.51  % (3671)Time elapsed: 0.108 s
% 0.21/0.51  % (3671)------------------------------
% 0.21/0.51  % (3671)------------------------------
% 0.21/0.51  % (3672)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.52  % (3682)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.52  % (3683)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.53  % (3687)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.53  % (3687)Refutation not found, incomplete strategy% (3687)------------------------------
% 0.21/0.53  % (3687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (3687)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (3687)Memory used [KB]: 10618
% 0.21/0.53  % (3687)Time elapsed: 0.107 s
% 0.21/0.53  % (3687)------------------------------
% 0.21/0.53  % (3687)------------------------------
% 0.21/0.54  % (3673)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 1.63/0.56  % (3678)Refutation found. Thanks to Tanya!
% 1.63/0.56  % SZS status Theorem for theBenchmark
% 1.63/0.56  % SZS output start Proof for theBenchmark
% 1.63/0.56  fof(f1309,plain,(
% 1.63/0.56    $false),
% 1.63/0.56    inference(avatar_sat_refutation,[],[f60,f1111,f1308])).
% 1.63/0.56  fof(f1308,plain,(
% 1.63/0.56    spl2_2),
% 1.63/0.56    inference(avatar_contradiction_clause,[],[f1307])).
% 1.63/0.56  fof(f1307,plain,(
% 1.63/0.56    $false | spl2_2),
% 1.63/0.56    inference(subsumption_resolution,[],[f59,f1306])).
% 1.63/0.56  fof(f1306,plain,(
% 1.63/0.56    ( ! [X0] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X0)),X0)) )),
% 1.63/0.56    inference(forward_demodulation,[],[f1251,f239])).
% 1.63/0.56  fof(f239,plain,(
% 1.63/0.56    ( ! [X0] : (k3_relat_1(k2_wellord1(sK1,X0)) = k2_xboole_0(k1_relat_1(k2_wellord1(sK1,X0)),k2_relat_1(k2_wellord1(sK1,X0)))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f67,f37])).
% 1.63/0.56  fof(f37,plain,(
% 1.63/0.56    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 1.63/0.56    inference(cnf_transformation,[],[f18])).
% 1.63/0.56  fof(f18,plain,(
% 1.63/0.56    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f5])).
% 1.63/0.56  fof(f5,axiom,(
% 1.63/0.56    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 1.63/0.56  fof(f67,plain,(
% 1.63/0.56    ( ! [X0] : (v1_relat_1(k2_wellord1(sK1,X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f44])).
% 1.63/0.56  fof(f44,plain,(
% 1.63/0.56    ( ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f25])).
% 1.63/0.56  fof(f25,plain,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(k2_wellord1(X0,X1)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f12])).
% 1.63/0.56  fof(f12,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k2_wellord1(X0,X1)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_wellord1)).
% 1.63/0.56  fof(f35,plain,(
% 1.63/0.56    v1_relat_1(sK1)),
% 1.63/0.56    inference(cnf_transformation,[],[f33])).
% 1.63/0.56  fof(f33,plain,(
% 1.63/0.56    (~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))) & v1_relat_1(sK1)),
% 1.63/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f32])).
% 1.63/0.56  fof(f32,plain,(
% 1.63/0.56    ? [X0,X1] : ((~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) & v1_relat_1(X1)) => ((~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 1.63/0.56    introduced(choice_axiom,[])).
% 1.63/0.56  fof(f17,plain,(
% 1.63/0.56    ? [X0,X1] : ((~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) | ~r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))) & v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f16])).
% 1.63/0.56  fof(f16,negated_conjecture,(
% 1.63/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.63/0.56    inference(negated_conjecture,[],[f15])).
% 1.63/0.56  fof(f15,conjecture,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),X0) & r1_tarski(k3_relat_1(k2_wellord1(X1,X0)),k3_relat_1(X1))))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_wellord1)).
% 1.63/0.56  fof(f1251,plain,(
% 1.63/0.56    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_relat_1(k2_wellord1(sK1,X0)),k2_relat_1(k2_wellord1(sK1,X0))),X0)) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f1136,f1248,f51])).
% 1.63/0.56  fof(f51,plain,(
% 1.63/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f31])).
% 1.63/0.56  fof(f31,plain,(
% 1.63/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.63/0.56    inference(flattening,[],[f30])).
% 1.63/0.56  fof(f30,plain,(
% 1.63/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.63/0.56    inference(ennf_transformation,[],[f2])).
% 1.63/0.56  fof(f2,axiom,(
% 1.63/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.63/0.56  fof(f1248,plain,(
% 1.63/0.56    ( ! [X1] : (r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1)) )),
% 1.63/0.56    inference(global_subsumption,[],[f63,f1246])).
% 1.63/0.56  fof(f1246,plain,(
% 1.63/0.56    ( ! [X1] : (r1_tarski(k1_relat_1(k2_wellord1(sK1,X1)),X1) | ~v1_relat_1(k8_relat_1(X1,sK1))) )),
% 1.63/0.56    inference(superposition,[],[f46,f752])).
% 1.63/0.56  fof(f752,plain,(
% 1.63/0.56    ( ! [X0] : (k2_wellord1(sK1,X0) = k7_relat_1(k8_relat_1(X0,sK1),X0)) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f48])).
% 1.63/0.56  fof(f48,plain,(
% 1.63/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f29])).
% 1.63/0.56  fof(f29,plain,(
% 1.63/0.56    ! [X0,X1] : (k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0) | ~v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f13])).
% 1.63/0.56  fof(f13,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k7_relat_1(k8_relat_1(X0,X1),X0))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_wellord1)).
% 1.63/0.56  fof(f46,plain,(
% 1.63/0.56    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f27])).
% 1.63/0.56  fof(f27,plain,(
% 1.63/0.56    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f10])).
% 1.63/0.56  fof(f10,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.63/0.56  fof(f63,plain,(
% 1.63/0.56    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK1))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f43])).
% 1.63/0.56  fof(f43,plain,(
% 1.63/0.56    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f24])).
% 1.63/0.56  fof(f24,plain,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f7])).
% 1.63/0.56  fof(f7,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 1.63/0.56  fof(f1136,plain,(
% 1.63/0.56    ( ! [X1] : (r1_tarski(k2_relat_1(k2_wellord1(sK1,X1)),X1)) )),
% 1.63/0.56    inference(global_subsumption,[],[f61,f1134])).
% 1.63/0.56  fof(f1134,plain,(
% 1.63/0.56    ( ! [X1] : (r1_tarski(k2_relat_1(k2_wellord1(sK1,X1)),X1) | ~v1_relat_1(k7_relat_1(sK1,X1))) )),
% 1.63/0.56    inference(superposition,[],[f45,f567])).
% 1.63/0.56  fof(f567,plain,(
% 1.63/0.56    ( ! [X0] : (k2_wellord1(sK1,X0) = k8_relat_1(X0,k7_relat_1(sK1,X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f47])).
% 1.63/0.56  fof(f47,plain,(
% 1.63/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0))) )),
% 1.63/0.56    inference(cnf_transformation,[],[f28])).
% 1.63/0.56  fof(f28,plain,(
% 1.63/0.56    ! [X0,X1] : (k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f14])).
% 1.63/0.56  fof(f14,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => k2_wellord1(X1,X0) = k8_relat_1(X0,k7_relat_1(X1,X0)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_wellord1)).
% 1.63/0.56  fof(f45,plain,(
% 1.63/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f26])).
% 1.63/0.56  fof(f26,plain,(
% 1.63/0.56    ! [X0,X1] : (r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0) | ~v1_relat_1(X1))),
% 1.63/0.56    inference(ennf_transformation,[],[f8])).
% 1.63/0.56  fof(f8,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),X0))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_relat_1)).
% 1.63/0.56  fof(f61,plain,(
% 1.63/0.56    ( ! [X0] : (v1_relat_1(k7_relat_1(sK1,X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f42])).
% 1.63/0.56  fof(f42,plain,(
% 1.63/0.56    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f23])).
% 1.63/0.56  fof(f23,plain,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f6])).
% 1.63/0.56  fof(f6,axiom,(
% 1.63/0.56    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.63/0.56  fof(f59,plain,(
% 1.63/0.56    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | spl2_2),
% 1.63/0.56    inference(avatar_component_clause,[],[f57])).
% 1.63/0.56  fof(f57,plain,(
% 1.63/0.56    spl2_2 <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0)),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.63/0.56  fof(f1111,plain,(
% 1.63/0.56    spl2_1),
% 1.63/0.56    inference(avatar_contradiction_clause,[],[f1110])).
% 1.63/0.56  fof(f1110,plain,(
% 1.63/0.56    $false | spl2_1),
% 1.63/0.56    inference(subsumption_resolution,[],[f55,f1106])).
% 1.63/0.56  fof(f1106,plain,(
% 1.63/0.56    ( ! [X11] : (r1_tarski(k3_relat_1(k2_wellord1(sK1,X11)),k3_relat_1(sK1))) )),
% 1.63/0.56    inference(superposition,[],[f985,f432])).
% 1.63/0.56  fof(f432,plain,(
% 1.63/0.56    ( ! [X0] : (k2_wellord1(sK1,X0) = k3_xboole_0(sK1,k2_zfmisc_1(X0,X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f38])).
% 1.63/0.56  fof(f38,plain,(
% 1.63/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1))) )),
% 1.63/0.56    inference(cnf_transformation,[],[f19])).
% 1.63/0.56  fof(f19,plain,(
% 1.63/0.56    ! [X0] : (! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f11])).
% 1.63/0.56  fof(f11,axiom,(
% 1.63/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : k2_wellord1(X0,X1) = k3_xboole_0(X0,k2_zfmisc_1(X1,X1)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).
% 1.63/0.56  fof(f985,plain,(
% 1.63/0.56    ( ! [X0] : (r1_tarski(k3_relat_1(k3_xboole_0(sK1,X0)),k3_relat_1(sK1))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f120,f41,f39])).
% 1.63/0.56  fof(f39,plain,(
% 1.63/0.56    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f21])).
% 1.63/0.56  fof(f21,plain,(
% 1.63/0.56    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(flattening,[],[f20])).
% 1.63/0.56  fof(f20,plain,(
% 1.63/0.56    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f9])).
% 1.63/0.56  fof(f9,axiom,(
% 1.63/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 1.63/0.56  fof(f41,plain,(
% 1.63/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f1])).
% 1.63/0.56  fof(f1,axiom,(
% 1.63/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.63/0.56  fof(f120,plain,(
% 1.63/0.56    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK1,X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f35,f102,f40])).
% 1.63/0.56  fof(f40,plain,(
% 1.63/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f22])).
% 1.63/0.56  fof(f22,plain,(
% 1.63/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.63/0.56    inference(ennf_transformation,[],[f4])).
% 1.63/0.56  fof(f4,axiom,(
% 1.63/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.63/0.56  fof(f102,plain,(
% 1.63/0.56    ( ! [X0,X1] : (m1_subset_1(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 1.63/0.56    inference(unit_resulting_resolution,[],[f41,f50])).
% 1.63/0.56  fof(f50,plain,(
% 1.63/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.63/0.56    inference(cnf_transformation,[],[f34])).
% 1.63/0.56  fof(f34,plain,(
% 1.63/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.63/0.56    inference(nnf_transformation,[],[f3])).
% 1.63/0.56  fof(f3,axiom,(
% 1.63/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.63/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.63/0.56  fof(f55,plain,(
% 1.63/0.56    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1)) | spl2_1),
% 1.63/0.56    inference(avatar_component_clause,[],[f53])).
% 1.63/0.56  fof(f53,plain,(
% 1.63/0.56    spl2_1 <=> r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 1.63/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.63/0.56  fof(f60,plain,(
% 1.63/0.56    ~spl2_1 | ~spl2_2),
% 1.63/0.56    inference(avatar_split_clause,[],[f36,f57,f53])).
% 1.63/0.56  fof(f36,plain,(
% 1.63/0.56    ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),sK0) | ~r1_tarski(k3_relat_1(k2_wellord1(sK1,sK0)),k3_relat_1(sK1))),
% 1.63/0.56    inference(cnf_transformation,[],[f33])).
% 1.63/0.56  % SZS output end Proof for theBenchmark
% 1.63/0.56  % (3678)------------------------------
% 1.63/0.56  % (3678)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.56  % (3678)Termination reason: Refutation
% 1.63/0.56  
% 1.63/0.56  % (3678)Memory used [KB]: 12537
% 1.63/0.56  % (3678)Time elapsed: 0.138 s
% 1.63/0.56  % (3678)------------------------------
% 1.63/0.56  % (3678)------------------------------
% 1.63/0.57  % (3660)Success in time 0.213 s
%------------------------------------------------------------------------------
