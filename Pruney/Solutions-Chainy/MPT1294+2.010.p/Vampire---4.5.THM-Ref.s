%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 102 expanded)
%              Number of leaves         :    8 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  108 ( 352 expanded)
%              Number of equality atoms :   53 ( 230 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f88,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f35,f52,f82,f87])).

fof(f87,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f61,f27])).

fof(f27,plain,
    ( k1_xboole_0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f13,f24,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f24,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f22,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ( ( k1_xboole_0 = sK1
        & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
      | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k7_setfam_1(X0,X1) != k1_xboole_0 )
          | ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ( ( k1_xboole_0 = sK1
          & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
        | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 = X1
          & k7_setfam_1(X0,X1) != k1_xboole_0 )
        | ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k7_setfam_1(X0,X1) != k1_xboole_0 )
          & ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k7_setfam_1(X0,X1) != k1_xboole_0 )
        & ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).

fof(f82,plain,
    ( ~ spl2_1
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl2_1
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f34,f65])).

fof(f65,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(backward_demodulation,[],[f59,f61])).

fof(f59,plain,
    ( sK1 = k7_setfam_1(sK0,k1_xboole_0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f58,f24])).

fof(f58,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f13,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f34,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_3
  <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f52,plain,
    ( ~ spl2_2
    | spl2_3 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | ~ spl2_2
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f34,f38,f39,f20])).

fof(f39,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f36,f18])).

fof(f36,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f13,f28])).

fof(f28,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f38,plain,
    ( m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f36,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f35,plain,
    ( ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f30,f32,f26])).

fof(f30,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f17,f26,f22])).

fof(f17,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:08:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (30458)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.45  % (30466)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.46  % (30458)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f29,f35,f52,f82,f87])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ~spl2_1 | spl2_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f83])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    $false | (~spl2_1 | spl2_2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f61,f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k1_xboole_0 != sK1 | spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl2_2 <=> k1_xboole_0 = sK1),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | ~spl2_1),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f13,f24,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    inference(flattening,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : ((k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl2_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    spl2_1 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1] : (((k1_xboole_0 = X1 & k7_setfam_1(X0,X1) != k1_xboole_0) | (k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1] : (((k1_xboole_0 = X1 & k7_setfam_1(X0,X1) != k1_xboole_0) | (k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k7_setfam_1(X0,X1) != k1_xboole_0) & ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f4])).
% 0.20/0.46  fof(f4,conjecture,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k7_setfam_1(X0,X1) != k1_xboole_0) & ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tops_2)).
% 0.20/0.46  fof(f82,plain,(
% 0.20/0.46    ~spl2_1 | spl2_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    $false | (~spl2_1 | spl2_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f34,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0) | ~spl2_1),
% 0.20/0.46    inference(backward_demodulation,[],[f59,f61])).
% 0.20/0.46  fof(f59,plain,(
% 0.20/0.46    sK1 = k7_setfam_1(sK0,k1_xboole_0) | ~spl2_1),
% 0.20/0.46    inference(forward_demodulation,[],[f58,f24])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f13,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | spl2_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    spl2_3 <=> k1_xboole_0 = k7_setfam_1(sK0,k1_xboole_0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ~spl2_2 | spl2_3),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f48])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    $false | (~spl2_2 | spl2_3)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f34,f38,f39,f20])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    k1_xboole_0 = k7_setfam_1(sK0,k7_setfam_1(sK0,k1_xboole_0)) | ~spl2_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f18])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 0.20/0.46    inference(backward_demodulation,[],[f13,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | ~spl2_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    m1_subset_1(k7_setfam_1(sK0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_2),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f36,f19])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ~spl2_2 | ~spl2_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f30,f32,f26])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    k1_xboole_0 != k7_setfam_1(sK0,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.20/0.46    inference(inner_rewriting,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    k1_xboole_0 != k7_setfam_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl2_1 | spl2_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f17,f26,f22])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    k1_xboole_0 = sK1 | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (30458)------------------------------
% 0.20/0.46  % (30458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (30458)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (30458)Memory used [KB]: 10618
% 0.20/0.46  % (30458)Time elapsed: 0.058 s
% 0.20/0.46  % (30458)------------------------------
% 0.20/0.46  % (30458)------------------------------
% 0.20/0.46  % (30446)Success in time 0.107 s
%------------------------------------------------------------------------------
