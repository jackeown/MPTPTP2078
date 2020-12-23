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
% DateTime   : Thu Dec  3 12:54:29 EST 2020

% Result     : Theorem 1.17s
% Output     : Refutation 1.17s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 101 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :   13
%              Number of atoms          :  139 ( 208 expanded)
%              Number of equality atoms :   54 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f54,f82,f95])).

fof(f95,plain,
    ( spl2_2
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f25,f47,f81,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k6_relat_1(X0) != k7_relat_1(X1,X0)
      | k9_relat_1(X1,X0) = X0 ) ),
    inference(forward_demodulation,[],[f89,f58])).

fof(f58,plain,(
    ! [X0] : k9_relat_1(k6_relat_1(X0),X0) = X0 ),
    inference(forward_demodulation,[],[f57,f27])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f57,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0) ),
    inference(forward_demodulation,[],[f56,f26])).

fof(f26,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0))) ),
    inference(resolution,[],[f28,f25])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) != k7_relat_1(X1,X0)
      | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f87,f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k6_relat_1(X0) != k7_relat_1(X1,X0)
      | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f31,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0) ),
    inference(resolution,[],[f75,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f72,f70])).

fof(f70,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) ),
    inference(resolution,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f71,f27])).

% (14144)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f30,f25])).

% (14127)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
      | k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
          | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k9_relat_1(X1,X0) = k9_relat_1(X2,X0)
          | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X1,X0) = k7_relat_1(X2,X0)
           => k9_relat_1(X1,X0) = k9_relat_1(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).

fof(f81,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl2_6
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f47,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_2
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f25,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f82,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f77,f51,f79])).

fof(f51,plain,
    ( spl2_3
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_3 ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f54,plain,
    ( spl2_3
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f49,f40,f51])).

fof(f40,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f49,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f35,f42])).

fof(f42,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f48,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).

fof(f43,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:24:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (14124)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (14120)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (14139)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (14133)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (14123)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.17/0.51  % (14123)Refutation found. Thanks to Tanya!
% 1.17/0.51  % SZS status Theorem for theBenchmark
% 1.17/0.51  % (14140)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.17/0.51  % (14125)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.17/0.51  % (14131)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.17/0.52  % (14132)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.17/0.52  % SZS output start Proof for theBenchmark
% 1.17/0.52  fof(f96,plain,(
% 1.17/0.52    $false),
% 1.17/0.52    inference(avatar_sat_refutation,[],[f43,f48,f54,f82,f95])).
% 1.17/0.52  fof(f95,plain,(
% 1.17/0.52    spl2_2 | ~spl2_6),
% 1.17/0.52    inference(avatar_contradiction_clause,[],[f93])).
% 1.17/0.52  fof(f93,plain,(
% 1.17/0.52    $false | (spl2_2 | ~spl2_6)),
% 1.17/0.52    inference(unit_resulting_resolution,[],[f25,f47,f81,f90])).
% 1.17/0.52  fof(f90,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = X0) )),
% 1.17/0.52    inference(forward_demodulation,[],[f89,f58])).
% 1.17/0.52  fof(f58,plain,(
% 1.17/0.52    ( ! [X0] : (k9_relat_1(k6_relat_1(X0),X0) = X0) )),
% 1.17/0.52    inference(forward_demodulation,[],[f57,f27])).
% 1.17/0.52  fof(f27,plain,(
% 1.17/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f6,axiom,(
% 1.17/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.17/0.52  fof(f57,plain,(
% 1.17/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),X0)) )),
% 1.17/0.52    inference(forward_demodulation,[],[f56,f26])).
% 1.17/0.52  fof(f26,plain,(
% 1.17/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.17/0.52    inference(cnf_transformation,[],[f6])).
% 1.17/0.52  fof(f56,plain,(
% 1.17/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = k9_relat_1(k6_relat_1(X0),k1_relat_1(k6_relat_1(X0)))) )),
% 1.17/0.52    inference(resolution,[],[f28,f25])).
% 1.17/0.52  fof(f28,plain,(
% 1.17/0.52    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f12])).
% 1.17/0.52  fof(f12,plain,(
% 1.17/0.52    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.17/0.52    inference(ennf_transformation,[],[f4])).
% 1.17/0.52  fof(f4,axiom,(
% 1.17/0.52    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.17/0.52  fof(f89,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(X1)) )),
% 1.17/0.52    inference(subsumption_resolution,[],[f87,f25])).
% 1.17/0.52  fof(f87,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k6_relat_1(X0) != k7_relat_1(X1,X0) | k9_relat_1(X1,X0) = k9_relat_1(k6_relat_1(X0),X0) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.17/0.52    inference(superposition,[],[f31,f76])).
% 1.17/0.52  fof(f76,plain,(
% 1.17/0.52    ( ! [X0] : (k6_relat_1(X0) = k7_relat_1(k6_relat_1(X0),X0)) )),
% 1.17/0.52    inference(resolution,[],[f75,f37])).
% 1.17/0.52  fof(f37,plain,(
% 1.17/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.17/0.52    inference(equality_resolution,[],[f33])).
% 1.17/0.52  fof(f33,plain,(
% 1.17/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f21])).
% 1.17/0.52  fof(f21,plain,(
% 1.17/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.17/0.52    inference(flattening,[],[f20])).
% 1.17/0.52  fof(f20,plain,(
% 1.17/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.17/0.52    inference(nnf_transformation,[],[f1])).
% 1.17/0.52  fof(f1,axiom,(
% 1.17/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.17/0.52  fof(f75,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 1.17/0.52    inference(forward_demodulation,[],[f72,f70])).
% 1.17/0.52  fof(f70,plain,(
% 1.17/0.52    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X1),k6_relat_1(X0))) )),
% 1.17/0.52    inference(resolution,[],[f29,f25])).
% 1.17/0.52  fof(f29,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f13])).
% 1.17/0.52  fof(f13,plain,(
% 1.17/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 1.17/0.52    inference(ennf_transformation,[],[f8])).
% 1.17/0.52  fof(f8,axiom,(
% 1.17/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 1.17/0.52  fof(f72,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.17/0.52    inference(forward_demodulation,[],[f71,f27])).
% 1.17/0.52  % (14144)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.17/0.52  fof(f71,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 1.17/0.52    inference(resolution,[],[f30,f25])).
% 1.17/0.52  % (14127)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.17/0.52  fof(f30,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 1.17/0.52    inference(cnf_transformation,[],[f15])).
% 1.17/0.52  fof(f15,plain,(
% 1.17/0.52    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 1.17/0.52    inference(flattening,[],[f14])).
% 1.17/0.52  fof(f14,plain,(
% 1.17/0.52    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.17/0.52    inference(ennf_transformation,[],[f7])).
% 1.17/0.52  fof(f7,axiom,(
% 1.17/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 1.17/0.52  fof(f31,plain,(
% 1.17/0.52    ( ! [X2,X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f17])).
% 1.17/0.52  fof(f17,plain,(
% 1.17/0.52    ! [X0,X1] : (! [X2] : (k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.17/0.52    inference(flattening,[],[f16])).
% 1.17/0.52  fof(f16,plain,(
% 1.17/0.52    ! [X0,X1] : (! [X2] : ((k9_relat_1(X1,X0) = k9_relat_1(X2,X0) | k7_relat_1(X1,X0) != k7_relat_1(X2,X0)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.17/0.52    inference(ennf_transformation,[],[f5])).
% 1.17/0.52  fof(f5,axiom,(
% 1.17/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k7_relat_1(X1,X0) = k7_relat_1(X2,X0) => k9_relat_1(X1,X0) = k9_relat_1(X2,X0))))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t201_relat_1)).
% 1.17/0.52  fof(f81,plain,(
% 1.17/0.52    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_6),
% 1.17/0.52    inference(avatar_component_clause,[],[f79])).
% 1.17/0.52  fof(f79,plain,(
% 1.17/0.52    spl2_6 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.17/0.52  fof(f47,plain,(
% 1.17/0.52    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_2),
% 1.17/0.52    inference(avatar_component_clause,[],[f45])).
% 1.17/0.52  fof(f45,plain,(
% 1.17/0.52    spl2_2 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.17/0.52  fof(f25,plain,(
% 1.17/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.17/0.52    inference(cnf_transformation,[],[f3])).
% 1.17/0.52  fof(f3,axiom,(
% 1.17/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.17/0.52  fof(f82,plain,(
% 1.17/0.52    spl2_6 | ~spl2_3),
% 1.17/0.52    inference(avatar_split_clause,[],[f77,f51,f79])).
% 1.17/0.52  fof(f51,plain,(
% 1.17/0.52    spl2_3 <=> r1_tarski(sK1,sK0)),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.17/0.52  fof(f77,plain,(
% 1.17/0.52    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_3),
% 1.17/0.52    inference(resolution,[],[f75,f53])).
% 1.17/0.52  fof(f53,plain,(
% 1.17/0.52    r1_tarski(sK1,sK0) | ~spl2_3),
% 1.17/0.52    inference(avatar_component_clause,[],[f51])).
% 1.17/0.52  fof(f54,plain,(
% 1.17/0.52    spl2_3 | ~spl2_1),
% 1.17/0.52    inference(avatar_split_clause,[],[f49,f40,f51])).
% 1.17/0.52  fof(f40,plain,(
% 1.17/0.52    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.17/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.17/0.52  fof(f49,plain,(
% 1.17/0.52    r1_tarski(sK1,sK0) | ~spl2_1),
% 1.17/0.52    inference(resolution,[],[f35,f42])).
% 1.17/0.52  fof(f42,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 1.17/0.52    inference(avatar_component_clause,[],[f40])).
% 1.17/0.52  fof(f35,plain,(
% 1.17/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.17/0.52    inference(cnf_transformation,[],[f22])).
% 1.17/0.52  fof(f22,plain,(
% 1.17/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.17/0.52    inference(nnf_transformation,[],[f2])).
% 1.17/0.52  fof(f2,axiom,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.17/0.52  fof(f48,plain,(
% 1.17/0.52    ~spl2_2),
% 1.17/0.52    inference(avatar_split_clause,[],[f24,f45])).
% 1.17/0.52  fof(f24,plain,(
% 1.17/0.52    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  fof(f19,plain,(
% 1.17/0.52    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.17/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f18])).
% 1.17/0.52  fof(f18,plain,(
% 1.17/0.52    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.17/0.52    introduced(choice_axiom,[])).
% 1.17/0.52  fof(f11,plain,(
% 1.17/0.52    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.17/0.52    inference(ennf_transformation,[],[f10])).
% 1.17/0.52  fof(f10,negated_conjecture,(
% 1.17/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.17/0.52    inference(negated_conjecture,[],[f9])).
% 1.17/0.52  fof(f9,conjecture,(
% 1.17/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 1.17/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_funct_1)).
% 1.17/0.52  fof(f43,plain,(
% 1.17/0.52    spl2_1),
% 1.17/0.52    inference(avatar_split_clause,[],[f23,f40])).
% 1.17/0.52  fof(f23,plain,(
% 1.17/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.17/0.52    inference(cnf_transformation,[],[f19])).
% 1.17/0.52  % SZS output end Proof for theBenchmark
% 1.17/0.52  % (14123)------------------------------
% 1.17/0.52  % (14123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (14123)Termination reason: Refutation
% 1.17/0.52  
% 1.17/0.52  % (14123)Memory used [KB]: 6140
% 1.17/0.52  % (14123)Time elapsed: 0.094 s
% 1.17/0.52  % (14123)------------------------------
% 1.17/0.52  % (14123)------------------------------
% 1.17/0.52  % (14132)Refutation not found, incomplete strategy% (14132)------------------------------
% 1.17/0.52  % (14132)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (14145)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.17/0.52  % (14132)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  % (14136)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.17/0.52  
% 1.17/0.52  % (14132)Memory used [KB]: 10490
% 1.17/0.52  % (14132)Time elapsed: 0.105 s
% 1.17/0.52  % (14132)------------------------------
% 1.17/0.52  % (14132)------------------------------
% 1.17/0.52  % (14120)Refutation not found, incomplete strategy% (14120)------------------------------
% 1.17/0.52  % (14120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.17/0.52  % (14120)Termination reason: Refutation not found, incomplete strategy
% 1.17/0.52  
% 1.17/0.52  % (14120)Memory used [KB]: 10490
% 1.17/0.52  % (14120)Time elapsed: 0.102 s
% 1.17/0.52  % (14120)------------------------------
% 1.17/0.52  % (14120)------------------------------
% 1.17/0.52  % (14119)Success in time 0.157 s
%------------------------------------------------------------------------------
