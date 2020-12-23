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
% DateTime   : Thu Dec  3 13:20:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 264 expanded)
%              Number of leaves         :   17 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  170 ( 945 expanded)
%              Number of equality atoms :   73 ( 163 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f336,plain,(
    $false ),
    inference(subsumption_resolution,[],[f335,f85])).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f335,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(backward_demodulation,[],[f63,f328])).

fof(f328,plain,(
    k1_xboole_0 = k3_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f315,f64])).

fof(f64,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ~ r1_tarski(sK0,sK1)
    & ~ v1_xboole_0(k3_xboole_0(sK0,sK1))
    & v1_zfmisc_1(sK0)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(X0,X1)
            & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
        & v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(sK0,X1)
          & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
      & v1_zfmisc_1(sK0)
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X1] :
        ( ~ r1_tarski(sK0,X1)
        & ~ v1_xboole_0(k3_xboole_0(sK0,X1)) )
   => ( ~ r1_tarski(sK0,sK1)
      & ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(X0,X1)
          & ~ v1_xboole_0(k3_xboole_0(X0,X1)) )
      & v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_zfmisc_1(X0)
          & ~ v1_xboole_0(X0) )
       => ! [X1] :
            ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
           => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( ~ v1_xboole_0(k3_xboole_0(X0,X1))
         => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

fof(f315,plain,(
    ! [X0] :
      ( r1_tarski(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(trivial_inequality_removal,[],[f311])).

fof(f311,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(backward_demodulation,[],[f202,f308])).

fof(f308,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f307,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f307,plain,(
    k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0) ),
    inference(subsumption_resolution,[],[f306,f126])).

fof(f126,plain,(
    k1_xboole_0 != sK0 ),
    inference(superposition,[],[f115,f95])).

fof(f95,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 != k2_xboole_0(sK0,X0) ),
    inference(superposition,[],[f94,f111])).

fof(f111,plain,(
    sK0 = k1_tarski(sK3(sK0)) ),
    inference(forward_demodulation,[],[f110,f105])).

fof(f105,plain,(
    sK0 = k6_domain_1(sK0,sK3(sK0)) ),
    inference(subsumption_resolution,[],[f103,f61])).

fof(f61,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,
    ( sK0 = k6_domain_1(sK0,sK3(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f62,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK3(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ( k6_domain_1(X0,sK3(X0)) = X0
            & m1_subset_1(sK3(X0),X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k6_domain_1(X0,X2) = X0
          & m1_subset_1(X2,X0) )
     => ( k6_domain_1(X0,sK3(X0)) = X0
        & m1_subset_1(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X2] :
              ( k6_domain_1(X0,X2) = X0
              & m1_subset_1(X2,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( v1_zfmisc_1(X0)
          | ! [X1] :
              ( k6_domain_1(X0,X1) != X0
              | ~ m1_subset_1(X1,X0) ) )
        & ( ? [X1] :
              ( k6_domain_1(X0,X1) = X0
              & m1_subset_1(X1,X0) )
          | ~ v1_zfmisc_1(X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f62,plain,(
    v1_zfmisc_1(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f110,plain,(
    k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f109,f61])).

fof(f109,plain,
    ( k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k1_tarski(X1) = k6_domain_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f104,plain,(
    m1_subset_1(sK3(sK0),sK0) ),
    inference(subsumption_resolution,[],[f102,f61])).

fof(f102,plain,
    ( m1_subset_1(sK3(sK0),sK0)
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | m1_subset_1(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f306,plain,
    ( k1_xboole_0 = sK0
    | k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0) ),
    inference(forward_demodulation,[],[f301,f77])).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f301,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK0)
    | k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0) ),
    inference(superposition,[],[f200,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

% (7743)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
fof(f200,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,X1))
      | k3_xboole_0(sK0,X1) = k5_xboole_0(sK0,sK0) ) ),
    inference(superposition,[],[f149,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f149,plain,(
    ! [X1] :
      ( k4_xboole_0(sK0,X1) = k5_xboole_0(sK0,sK0)
      | k1_xboole_0 = k3_xboole_0(sK0,X1) ) ),
    inference(superposition,[],[f93,f140])).

fof(f140,plain,(
    ! [X0] :
      ( sK0 = k3_xboole_0(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f118,f74])).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f118,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK0)
      | k1_xboole_0 = X2
      | sK0 = X2 ) ),
    inference(superposition,[],[f68,f111])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f202,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
      | r1_tarski(sK0,X0)
      | k1_xboole_0 = k3_xboole_0(sK0,X0) ) ),
    inference(superposition,[],[f66,f149])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f63,plain,(
    ~ v1_xboole_0(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:33:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.57  % (7750)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=2.0:amm=sco:anc=none:gs=on:gsem=off:lma=on:lwlo=on:nm=4:nwc=10:stl=30:sd=3:ss=axioms:sos=all:sac=on_49 on theBenchmark
% 0.21/0.57  % (7739)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (7741)dis+1010_2:3_afr=on:afp=40000:afq=1.4:amm=off:anc=none:lma=on:nm=16:nwc=1:sp=occurrence:updr=off:uhcvi=on_34 on theBenchmark
% 0.21/0.57  % (7742)dis+10_5:4_add=off:afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sd=3:ss=axioms:st=3.0:sos=all:sp=occurrence:urr=on:updr=off_15 on theBenchmark
% 0.21/0.57  % (7749)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_6 on theBenchmark
% 0.21/0.58  % (7734)dis+4_8:1_add=large:afp=100000:afq=1.4:ep=RST:fde=unused:gsp=input_only:lcm=predicate:nwc=1:sos=all:sp=occurrence:updr=off:uhcvi=on_33 on theBenchmark
% 0.21/0.59  % (7730)lrs-11_3_av=off:bs=unit_only:bsr=on:cond=on:gsp=input_only:gs=on:gsem=on:lma=on:nm=2:nwc=1:stl=30:sd=3:ss=axioms:st=1.2:sos=all:sp=reverse_arity:urr=on:updr=off_11 on theBenchmark
% 0.21/0.59  % (7757)ott+11_8:1_av=off:bs=on:bce=on:fde=none:gsp=input_only:gs=on:gsem=on:irw=on:lcm=predicate:nm=6:nwc=1.5:sd=2:ss=axioms:st=1.2:sos=theory:urr=on:updr=off_49 on theBenchmark
% 0.21/0.59  % (7736)dis+1004_1_aac=none:acc=on:afp=40000:afq=1.2:anc=none:cond=on:fde=unused:gs=on:gsem=off:irw=on:nm=32:nwc=2:sd=1:ss=axioms:sos=theory:sp=reverse_arity:urr=ec_only_17 on theBenchmark
% 0.21/0.59  % (7738)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_11 on theBenchmark
% 0.21/0.59  % (7749)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % (7738)Refutation not found, incomplete strategy% (7738)------------------------------
% 0.21/0.59  % (7738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (7738)Memory used [KB]: 6140
% 0.21/0.59  % (7738)Time elapsed: 0.159 s
% 0.21/0.59  % (7738)------------------------------
% 0.21/0.59  % (7738)------------------------------
% 0.21/0.59  % (7736)Refutation not found, incomplete strategy% (7736)------------------------------
% 0.21/0.59  % (7736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (7735)lrs+11_4_av=off:gsp=input_only:irw=on:lma=on:nm=0:nwc=1.2:stl=30:sd=2:ss=axioms:sp=reverse_arity:urr=on:updr=off_8 on theBenchmark
% 0.21/0.59  % (7758)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_4 on theBenchmark
% 0.21/0.59  % (7747)lrs-2_3:2_av=off:bce=on:cond=on:gsp=input_only:gs=on:gsem=on:lcm=predicate:lma=on:newcnf=on:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off:uhcvi=on_62 on theBenchmark
% 0.21/0.59  % (7736)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (7736)Memory used [KB]: 10746
% 0.21/0.59  % (7736)Time elapsed: 0.154 s
% 0.21/0.59  % (7736)------------------------------
% 0.21/0.59  % (7736)------------------------------
% 0.21/0.59  % (7745)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.59  % (7733)lrs+2_5:4_av=off:bce=on:cond=fast:ep=R:fde=none:gs=on:lcm=reverse:lwlo=on:nwc=1:stl=30:sd=1:ss=axioms:sos=all:sp=occurrence_8 on theBenchmark
% 0.21/0.60  % (7751)ott+11_4:1_awrs=converge:awrsf=16:acc=model:add=large:afr=on:afp=4000:afq=1.4:amm=off:br=off:cond=fast:fde=none:gsp=input_only:nm=64:nwc=2:nicw=on:sd=3:ss=axioms:s2a=on:sac=on:sp=frequency:urr=on:updr=off_70 on theBenchmark
% 0.21/0.60  % (7753)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.60  % (7733)Refutation not found, incomplete strategy% (7733)------------------------------
% 0.21/0.60  % (7733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (7733)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (7733)Memory used [KB]: 6140
% 0.21/0.60  % (7733)Time elapsed: 0.002 s
% 0.21/0.60  % (7733)------------------------------
% 0.21/0.60  % (7733)------------------------------
% 0.21/0.60  % (7737)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_6 on theBenchmark
% 0.21/0.60  % (7731)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.60  % (7732)lrs+1002_8:1_av=off:cond=on:gsp=input_only:gs=on:irw=on:lma=on:nm=0:nwc=1.7:stl=30:sd=2:ss=axioms:sos=on:sp=occurrence:urr=on_41 on theBenchmark
% 1.87/0.60  % SZS output start Proof for theBenchmark
% 1.87/0.60  fof(f336,plain,(
% 1.87/0.60    $false),
% 1.87/0.60    inference(subsumption_resolution,[],[f335,f85])).
% 1.87/0.60  fof(f85,plain,(
% 1.87/0.60    v1_xboole_0(k1_xboole_0)),
% 1.87/0.60    inference(cnf_transformation,[],[f3])).
% 1.87/0.60  fof(f3,axiom,(
% 1.87/0.60    v1_xboole_0(k1_xboole_0)),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.87/0.60  fof(f335,plain,(
% 1.87/0.60    ~v1_xboole_0(k1_xboole_0)),
% 1.87/0.60    inference(backward_demodulation,[],[f63,f328])).
% 1.87/0.60  fof(f328,plain,(
% 1.87/0.60    k1_xboole_0 = k3_xboole_0(sK0,sK1)),
% 1.87/0.60    inference(resolution,[],[f315,f64])).
% 1.87/0.60  fof(f64,plain,(
% 1.87/0.60    ~r1_tarski(sK0,sK1)),
% 1.87/0.60    inference(cnf_transformation,[],[f38])).
% 1.87/0.60  fof(f38,plain,(
% 1.87/0.60    (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0)),
% 1.87/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f37,f36])).
% 1.87/0.60  fof(f36,plain,(
% 1.87/0.60    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => (? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) & v1_zfmisc_1(sK0) & ~v1_xboole_0(sK0))),
% 1.87/0.60    introduced(choice_axiom,[])).
% 1.87/0.60  fof(f37,plain,(
% 1.87/0.60    ? [X1] : (~r1_tarski(sK0,X1) & ~v1_xboole_0(k3_xboole_0(sK0,X1))) => (~r1_tarski(sK0,sK1) & ~v1_xboole_0(k3_xboole_0(sK0,sK1)))),
% 1.87/0.60    introduced(choice_axiom,[])).
% 1.87/0.60  fof(f29,plain,(
% 1.87/0.60    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & v1_zfmisc_1(X0) & ~v1_xboole_0(X0))),
% 1.87/0.60    inference(flattening,[],[f28])).
% 1.87/0.60  fof(f28,plain,(
% 1.87/0.60    ? [X0] : (? [X1] : (~r1_tarski(X0,X1) & ~v1_xboole_0(k3_xboole_0(X0,X1))) & (v1_zfmisc_1(X0) & ~v1_xboole_0(X0)))),
% 1.87/0.60    inference(ennf_transformation,[],[f26])).
% 1.87/0.60  fof(f26,negated_conjecture,(
% 1.87/0.60    ~! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.87/0.60    inference(negated_conjecture,[],[f25])).
% 1.87/0.60  fof(f25,conjecture,(
% 1.87/0.60    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (~v1_xboole_0(k3_xboole_0(X0,X1)) => r1_tarski(X0,X1)))),
% 1.87/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).
% 1.87/0.60  fof(f315,plain,(
% 1.87/0.60    ( ! [X0] : (r1_tarski(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 1.87/0.60    inference(trivial_inequality_removal,[],[f311])).
% 1.87/0.61  fof(f311,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 1.87/0.61    inference(backward_demodulation,[],[f202,f308])).
% 1.87/0.61  fof(f308,plain,(
% 1.87/0.61    k1_xboole_0 = k5_xboole_0(sK0,sK0)),
% 1.87/0.61    inference(forward_demodulation,[],[f307,f78])).
% 1.87/0.61  fof(f78,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f10])).
% 1.87/0.61  fof(f10,axiom,(
% 1.87/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.87/0.61  fof(f307,plain,(
% 1.87/0.61    k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f306,f126])).
% 1.87/0.61  fof(f126,plain,(
% 1.87/0.61    k1_xboole_0 != sK0),
% 1.87/0.61    inference(superposition,[],[f115,f95])).
% 1.87/0.61  fof(f95,plain,(
% 1.87/0.61    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f9])).
% 1.87/0.61  fof(f9,axiom,(
% 1.87/0.61    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.87/0.61  fof(f115,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(sK0,X0)) )),
% 1.87/0.61    inference(superposition,[],[f94,f111])).
% 1.87/0.61  fof(f111,plain,(
% 1.87/0.61    sK0 = k1_tarski(sK3(sK0))),
% 1.87/0.61    inference(forward_demodulation,[],[f110,f105])).
% 1.87/0.61  fof(f105,plain,(
% 1.87/0.61    sK0 = k6_domain_1(sK0,sK3(sK0))),
% 1.87/0.61    inference(subsumption_resolution,[],[f103,f61])).
% 1.87/0.61  fof(f61,plain,(
% 1.87/0.61    ~v1_xboole_0(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f38])).
% 1.87/0.61  fof(f103,plain,(
% 1.87/0.61    sK0 = k6_domain_1(sK0,sK3(sK0)) | v1_xboole_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f62,f80])).
% 1.87/0.61  fof(f80,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK3(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f49])).
% 1.87/0.61  fof(f49,plain,(
% 1.87/0.61    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & ((k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.87/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 1.87/0.61  fof(f48,plain,(
% 1.87/0.61    ! [X0] : (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) => (k6_domain_1(X0,sK3(X0)) = X0 & m1_subset_1(sK3(X0),X0)))),
% 1.87/0.61    introduced(choice_axiom,[])).
% 1.87/0.61  fof(f47,plain,(
% 1.87/0.61    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X2] : (k6_domain_1(X0,X2) = X0 & m1_subset_1(X2,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.87/0.61    inference(rectify,[],[f46])).
% 1.87/0.61  fof(f46,plain,(
% 1.87/0.61    ! [X0] : (((v1_zfmisc_1(X0) | ! [X1] : (k6_domain_1(X0,X1) != X0 | ~m1_subset_1(X1,X0))) & (? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0)) | ~v1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 1.87/0.61    inference(nnf_transformation,[],[f32])).
% 1.87/0.61  fof(f32,plain,(
% 1.87/0.61    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.87/0.61    inference(ennf_transformation,[],[f24])).
% 1.87/0.61  fof(f24,axiom,(
% 1.87/0.61    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.87/0.61  fof(f62,plain,(
% 1.87/0.61    v1_zfmisc_1(sK0)),
% 1.87/0.61    inference(cnf_transformation,[],[f38])).
% 1.87/0.61  fof(f110,plain,(
% 1.87/0.61    k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0))),
% 1.87/0.61    inference(subsumption_resolution,[],[f109,f61])).
% 1.87/0.61  fof(f109,plain,(
% 1.87/0.61    k6_domain_1(sK0,sK3(sK0)) = k1_tarski(sK3(sK0)) | v1_xboole_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f104,f82])).
% 1.87/0.61  fof(f82,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k1_tarski(X1) = k6_domain_1(X0,X1) | v1_xboole_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f34])).
% 1.87/0.61  fof(f34,plain,(
% 1.87/0.61    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.87/0.61    inference(flattening,[],[f33])).
% 1.87/0.61  fof(f33,plain,(
% 1.87/0.61    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.87/0.61    inference(ennf_transformation,[],[f23])).
% 1.87/0.61  fof(f23,axiom,(
% 1.87/0.61    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.87/0.61  fof(f104,plain,(
% 1.87/0.61    m1_subset_1(sK3(sK0),sK0)),
% 1.87/0.61    inference(subsumption_resolution,[],[f102,f61])).
% 1.87/0.61  fof(f102,plain,(
% 1.87/0.61    m1_subset_1(sK3(sK0),sK0) | v1_xboole_0(sK0)),
% 1.87/0.61    inference(resolution,[],[f62,f79])).
% 1.87/0.61  fof(f79,plain,(
% 1.87/0.61    ( ! [X0] : (~v1_zfmisc_1(X0) | m1_subset_1(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f49])).
% 1.87/0.61  fof(f94,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f20])).
% 1.87/0.61  fof(f20,axiom,(
% 1.87/0.61    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.87/0.61  fof(f306,plain,(
% 1.87/0.61    k1_xboole_0 = sK0 | k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0)),
% 1.87/0.61    inference(forward_demodulation,[],[f301,f77])).
% 1.87/0.61  fof(f77,plain,(
% 1.87/0.61    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f27])).
% 1.87/0.61  fof(f27,plain,(
% 1.87/0.61    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.87/0.61    inference(rectify,[],[f4])).
% 1.87/0.61  fof(f4,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.87/0.61  fof(f301,plain,(
% 1.87/0.61    k1_xboole_0 = k3_xboole_0(sK0,sK0) | k3_xboole_0(sK0,k1_xboole_0) = k5_xboole_0(sK0,sK0)),
% 1.87/0.61    inference(superposition,[],[f200,f92])).
% 1.87/0.61  fof(f92,plain,(
% 1.87/0.61    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f12])).
% 1.87/0.61  fof(f12,axiom,(
% 1.87/0.61    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.87/0.61  % (7743)dis+4_2_av=off:bs=on:fsr=off:gsp=input_only:newcnf=on:nwc=1:sd=3:ss=axioms:st=3.0:sos=all:sp=reverse_arity:urr=ec_only:updr=off_127 on theBenchmark
% 1.87/0.61  fof(f200,plain,(
% 1.87/0.61    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK0,k4_xboole_0(sK0,X1)) | k3_xboole_0(sK0,X1) = k5_xboole_0(sK0,sK0)) )),
% 1.87/0.61    inference(superposition,[],[f149,f76])).
% 1.87/0.61  fof(f76,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f13])).
% 1.87/0.61  fof(f13,axiom,(
% 1.87/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.87/0.61  fof(f149,plain,(
% 1.87/0.61    ( ! [X1] : (k4_xboole_0(sK0,X1) = k5_xboole_0(sK0,sK0) | k1_xboole_0 = k3_xboole_0(sK0,X1)) )),
% 1.87/0.61    inference(superposition,[],[f93,f140])).
% 1.87/0.61  fof(f140,plain,(
% 1.87/0.61    ( ! [X0] : (sK0 = k3_xboole_0(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 1.87/0.61    inference(resolution,[],[f118,f74])).
% 1.87/0.61  fof(f74,plain,(
% 1.87/0.61    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f8])).
% 1.87/0.61  fof(f8,axiom,(
% 1.87/0.61    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.87/0.61  fof(f118,plain,(
% 1.87/0.61    ( ! [X2] : (~r1_tarski(X2,sK0) | k1_xboole_0 = X2 | sK0 = X2) )),
% 1.87/0.61    inference(superposition,[],[f68,f111])).
% 1.87/0.61  fof(f68,plain,(
% 1.87/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.87/0.61    inference(cnf_transformation,[],[f41])).
% 1.87/0.61  fof(f41,plain,(
% 1.87/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.87/0.61    inference(flattening,[],[f40])).
% 1.87/0.61  fof(f40,plain,(
% 1.87/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.87/0.61    inference(nnf_transformation,[],[f18])).
% 1.87/0.61  fof(f18,axiom,(
% 1.87/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.87/0.61  fof(f93,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.87/0.61    inference(cnf_transformation,[],[f7])).
% 1.87/0.61  fof(f7,axiom,(
% 1.87/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.87/0.61  fof(f202,plain,(
% 1.87/0.61    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(sK0,sK0) | r1_tarski(sK0,X0) | k1_xboole_0 = k3_xboole_0(sK0,X0)) )),
% 1.87/0.61    inference(superposition,[],[f66,f149])).
% 1.87/0.61  fof(f66,plain,(
% 1.87/0.61    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.87/0.61    inference(cnf_transformation,[],[f39])).
% 1.87/0.61  fof(f39,plain,(
% 1.87/0.61    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.87/0.61    inference(nnf_transformation,[],[f6])).
% 1.87/0.61  fof(f6,axiom,(
% 1.87/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.87/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.87/0.61  fof(f63,plain,(
% 1.87/0.61    ~v1_xboole_0(k3_xboole_0(sK0,sK1))),
% 1.87/0.61    inference(cnf_transformation,[],[f38])).
% 1.87/0.61  % SZS output end Proof for theBenchmark
% 1.87/0.61  % (7749)------------------------------
% 1.87/0.61  % (7749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (7749)Termination reason: Refutation
% 1.87/0.61  
% 1.87/0.61  % (7749)Memory used [KB]: 1791
% 1.87/0.61  % (7749)Time elapsed: 0.145 s
% 1.87/0.61  % (7749)------------------------------
% 1.87/0.61  % (7749)------------------------------
% 1.87/0.61  % (7729)Success in time 0.241 s
%------------------------------------------------------------------------------
