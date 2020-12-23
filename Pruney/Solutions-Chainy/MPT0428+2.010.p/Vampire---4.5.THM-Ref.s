%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:43 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 100 expanded)
%              Number of leaves         :   10 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  143 ( 320 expanded)
%              Number of equality atoms :   35 (  98 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f44,f51,f80])).

fof(f80,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f78,f59])).

fof(f59,plain,(
    r1_tarski(k3_tarski(sK1),sK0) ),
    inference(forward_demodulation,[],[f55,f26])).

fof(f26,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f55,plain,(
    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f47,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( sK0 != k5_setfam_1(sK0,sK1)
      | ~ m1_setfam_1(sK1,sK0) )
    & ( sK0 = k5_setfam_1(sK0,sK1)
      | m1_setfam_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k5_setfam_1(X0,X1) != X0
          | ~ m1_setfam_1(X1,X0) )
        & ( k5_setfam_1(X0,X1) = X0
          | m1_setfam_1(X1,X0) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( sK0 != k5_setfam_1(sK0,sK1)
        | ~ m1_setfam_1(sK1,sK0) )
      & ( sK0 = k5_setfam_1(sK0,sK1)
        | m1_setfam_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k5_setfam_1(X0,X1) != X0
        | ~ m1_setfam_1(X1,X0) )
      & ( k5_setfam_1(X0,X1) = X0
        | m1_setfam_1(X1,X0) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
      <~> k5_setfam_1(X0,X1) = X0 )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( m1_setfam_1(X1,X0)
        <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( m1_setfam_1(X1,X0)
      <=> k5_setfam_1(X0,X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).

fof(f78,plain,
    ( ~ r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f74,f54])).

fof(f54,plain,
    ( sK0 != k3_tarski(sK1)
    | spl2_2 ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f53,plain,
    ( sK0 != k3_tarski(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f42,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f42,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_2
  <=> sK0 = k5_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f74,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ r1_tarski(k3_tarski(sK1),sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f52,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f52,plain,
    ( r1_tarski(sK0,k3_tarski(sK1))
    | ~ spl2_1 ),
    inference(resolution,[],[f37,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ m1_setfam_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_setfam_1(X1,X0)
        | ~ r1_tarski(X0,k3_tarski(X1)) )
      & ( r1_tarski(X0,k3_tarski(X1))
        | ~ m1_setfam_1(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
    <=> r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).

fof(f37,plain,
    ( m1_setfam_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> m1_setfam_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f51,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f49,f34])).

fof(f34,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f49,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f45,f48])).

fof(f48,plain,
    ( sK0 = k3_tarski(sK1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f46,f41])).

fof(f41,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f46,plain,(
    k5_setfam_1(sK0,sK1) = k3_tarski(sK1) ),
    inference(resolution,[],[f20,f27])).

fof(f45,plain,
    ( ~ r1_tarski(sK0,k3_tarski(sK1))
    | spl2_1 ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_setfam_1(X1,X0)
      | ~ r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,
    ( ~ m1_setfam_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f44,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f21,f40,f36])).

fof(f21,plain,
    ( sK0 = k5_setfam_1(sK0,sK1)
    | m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f40,f36])).

fof(f22,plain,
    ( sK0 != k5_setfam_1(sK0,sK1)
    | ~ m1_setfam_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:19:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.52  % (15579)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.53  % (15587)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.53  % (15572)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (15568)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (15579)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f43,f44,f51,f80])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~spl2_1 | spl2_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    $false | (~spl2_1 | spl2_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f78,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(sK1),sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f55,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    r1_tarski(k3_tarski(sK1),k3_tarski(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(resolution,[],[f47,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    r1_tarski(sK1,k1_zfmisc_1(sK0))),
% 0.22/0.53    inference(resolution,[],[f20,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.53    inference(nnf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    (sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => ((sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)) & (sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ? [X0,X1] : ((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(flattening,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ? [X0,X1] : (((k5_setfam_1(X0,X1) != X0 | ~m1_setfam_1(X1,X0)) & (k5_setfam_1(X0,X1) = X0 | m1_setfam_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(nnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0,X1] : ((m1_setfam_1(X1,X0) <~> k5_setfam_1(X0,X1) = X0) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (m1_setfam_1(X1,X0) <=> k5_setfam_1(X0,X1) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_setfam_1)).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~r1_tarski(k3_tarski(sK1),sK0) | (~spl2_1 | spl2_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    sK0 != k3_tarski(sK1) | spl2_2),
% 0.22/0.53    inference(subsumption_resolution,[],[f53,f20])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    sK0 != k3_tarski(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_2),
% 0.22/0.53    inference(superposition,[],[f42,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_tarski(X1) = k5_setfam_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k3_tarski(X1) = k5_setfam_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    sK0 != k5_setfam_1(sK0,sK1) | spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    spl2_2 <=> sK0 = k5_setfam_1(sK0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    sK0 = k3_tarski(sK1) | ~r1_tarski(k3_tarski(sK1),sK0) | ~spl2_1),
% 0.22/0.53    inference(resolution,[],[f52,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    r1_tarski(sK0,k3_tarski(sK1)) | ~spl2_1),
% 0.22/0.53    inference(resolution,[],[f37,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : ((m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) & (r1_tarski(X0,k3_tarski(X1)) | ~m1_setfam_1(X1,X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_setfam_1(X1,X0) <=> r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_setfam_1)).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    m1_setfam_1(sK1,sK0) | ~spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    spl2_1 <=> m1_setfam_1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    spl2_1 | ~spl2_2),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    $false | (spl2_1 | ~spl2_2)),
% 0.22/0.53    inference(subsumption_resolution,[],[f49,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ~r1_tarski(sK0,sK0) | (spl2_1 | ~spl2_2)),
% 0.22/0.53    inference(backward_demodulation,[],[f45,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    sK0 = k3_tarski(sK1) | ~spl2_2),
% 0.22/0.53    inference(forward_demodulation,[],[f46,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    sK0 = k5_setfam_1(sK0,sK1) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f40])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    k5_setfam_1(sK0,sK1) = k3_tarski(sK1)),
% 0.22/0.53    inference(resolution,[],[f20,f27])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ~r1_tarski(sK0,k3_tarski(sK1)) | spl2_1),
% 0.22/0.53    inference(resolution,[],[f38,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_setfam_1(X1,X0) | ~r1_tarski(X0,k3_tarski(X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ~m1_setfam_1(sK1,sK0) | spl2_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f36])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    spl2_1 | spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f21,f40,f36])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    sK0 = k5_setfam_1(sK0,sK1) | m1_setfam_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ~spl2_1 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f22,f40,f36])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    sK0 != k5_setfam_1(sK0,sK1) | ~m1_setfam_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (15579)------------------------------
% 0.22/0.53  % (15579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (15579)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (15579)Memory used [KB]: 10618
% 0.22/0.53  % (15579)Time elapsed: 0.110 s
% 0.22/0.53  % (15579)------------------------------
% 0.22/0.53  % (15579)------------------------------
% 0.22/0.53  % (15577)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.54  % (15567)Success in time 0.169 s
%------------------------------------------------------------------------------
