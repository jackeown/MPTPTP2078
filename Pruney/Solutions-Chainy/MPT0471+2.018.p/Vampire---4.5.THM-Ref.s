%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 133 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   22
%              Number of atoms          :  191 ( 374 expanded)
%              Number of equality atoms :  120 ( 202 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f143,plain,(
    $false ),
    inference(subsumption_resolution,[],[f31,f131])).

fof(f131,plain,(
    ! [X5] : k1_xboole_0 = X5 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X5 ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X5
      | k1_xboole_0 != k1_xboole_0 ) ),
    inference(superposition,[],[f88,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k3_xboole_0(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f66,f86])).

fof(f86,plain,(
    k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f85,f31])).

fof(f85,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(forward_demodulation,[],[f84,f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f84,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(forward_demodulation,[],[f83,f32])).

fof(f32,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f83,plain,
    ( k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(forward_demodulation,[],[f81,f33])).

fof(f33,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f81,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f80,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f80,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    inference(resolution,[],[f79,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4))))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

fof(f79,plain,(
    ! [X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f77,f35])).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f77,plain,(
    ! [X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ) ),
    inference(duplicate_literal_removal,[],[f76])).

fof(f76,plain,(
    ! [X1] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0) ) ),
    inference(superposition,[],[f39,f74])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))
      | k1_xboole_0 = k1_tarski(k1_xboole_0) ) ),
    inference(resolution,[],[f63,f35])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | k1_xboole_0 = k1_tarski(X0)
      | sK1(X1,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

% (2234)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK1(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f66,plain,(
    ! [X4,X2,X3] :
      ( k1_tarski(X4) != X2
      | k1_tarski(X4) = k3_xboole_0(X2,X3)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f57,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = X0
        & k1_tarski(X1) = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(definition_folding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f88,plain,(
    ! [X0] :
      ( k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0))
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f41,f86])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

fof(f31,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f13])).

fof(f13,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:14:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (2229)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (2232)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (2231)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (2238)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (2236)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (2237)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (2229)Refutation not found, incomplete strategy% (2229)------------------------------
% 0.21/0.51  % (2229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2229)Memory used [KB]: 10618
% 0.21/0.51  % (2229)Time elapsed: 0.094 s
% 0.21/0.51  % (2229)------------------------------
% 0.21/0.51  % (2229)------------------------------
% 0.21/0.51  % (2230)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (2254)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (2230)Refutation not found, incomplete strategy% (2230)------------------------------
% 0.21/0.51  % (2230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (2245)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (2246)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (2251)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (2230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (2230)Memory used [KB]: 10618
% 0.21/0.51  % (2230)Time elapsed: 0.091 s
% 0.21/0.51  % (2230)------------------------------
% 0.21/0.51  % (2230)------------------------------
% 0.21/0.51  % (2243)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (2232)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(subsumption_resolution,[],[f31,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X5] : (k1_xboole_0 = X5) )),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X5) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X5 | k1_xboole_0 != k1_xboole_0) )),
% 0.21/0.52    inference(superposition,[],[f88,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,X1) | k1_xboole_0 != X0) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(superposition,[],[f66,f86])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(subsumption_resolution,[],[f85,f31])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0) | k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f84,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f83,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k1_xboole_0) | k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(forward_demodulation,[],[f81,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f11])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    k1_xboole_0 = k1_tarski(k1_xboole_0) | k3_relat_1(k1_xboole_0) = k2_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0))),
% 0.21/0.52    inference(resolution,[],[f80,f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    v1_relat_1(k1_xboole_0) | k1_xboole_0 = k1_tarski(k1_xboole_0)),
% 0.21/0.52    inference(resolution,[],[f79,f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_tarski(k4_tarski(X1,X2),k4_tarski(X3,X4)))) | v1_relat_1(X0)) )),
% 0.21/0.52    inference(resolution,[],[f52,f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(k1_xboole_0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f77,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(k1_xboole_0) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f76])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    ( ! [X1] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(k1_xboole_0) | ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) | k1_xboole_0 = k1_tarski(k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f39,f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = sK1(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0)) | k1_xboole_0 = k1_tarski(k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f63,f35])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | k1_xboole_0 = k1_tarski(X0) | sK1(X1,k1_tarski(X0)) = X0) )),
% 0.21/0.52    inference(resolution,[],[f40,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.21/0.52    inference(equality_resolution,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.21/0.52  % (2234)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(rectify,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : ((r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f18,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X1,X0] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) => (r2_hidden(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),X0)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(flattening,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),X0) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X4,X2,X3] : (k1_tarski(X4) != X2 | k1_tarski(X4) = k3_xboole_0(X2,X3) | k1_xboole_0 = k3_xboole_0(X2,X3)) )),
% 0.21/0.52    inference(superposition,[],[f57,f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f51,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_tarski(X1) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k1_tarski(X1) = X0 & k1_tarski(X1) = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.52    inference(rectify,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.21/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.52    inference(definition_folding,[],[f20,f21])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_tarski(X0)) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(superposition,[],[f41,f86])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 | k1_tarski(X0) != k3_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(flattening,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (2232)------------------------------
% 0.21/0.52  % (2232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2232)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (2232)Memory used [KB]: 6140
% 0.21/0.52  % (2232)Time elapsed: 0.097 s
% 0.21/0.52  % (2232)------------------------------
% 0.21/0.52  % (2232)------------------------------
% 0.21/0.52  % (2234)Refutation not found, incomplete strategy% (2234)------------------------------
% 0.21/0.52  % (2234)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2234)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2234)Memory used [KB]: 6012
% 0.21/0.52  % (2234)Time elapsed: 0.108 s
% 0.21/0.52  % (2234)------------------------------
% 0.21/0.52  % (2234)------------------------------
% 0.21/0.52  % (2228)Success in time 0.157 s
%------------------------------------------------------------------------------
