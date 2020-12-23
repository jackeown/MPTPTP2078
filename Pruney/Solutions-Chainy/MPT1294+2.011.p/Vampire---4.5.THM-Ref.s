%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 136 expanded)
%              Number of leaves         :   10 (  49 expanded)
%              Depth                    :   11
%              Number of atoms          :  182 ( 411 expanded)
%              Number of equality atoms :   32 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f81,f92,f97,f108,f137,f146])).

fof(f146,plain,
    ( ~ spl3_1
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl3_1
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f31,f17,f37,f141,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | ~ sQ2_eqProxy(X2,X3)
      | ~ r1_tarski(X0,X2)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

fof(f141,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK1)
    | spl3_3 ),
    inference(subsumption_resolution,[],[f140,f12])).

fof(f12,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ( ( k1_xboole_0 = sK1
        & k1_xboole_0 != k7_setfam_1(sK0,sK1) )
      | ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
          | ( k1_xboole_0 = k7_setfam_1(X0,X1)
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
          & k1_xboole_0 != k7_setfam_1(X0,X1) )
        | ( k1_xboole_0 = k7_setfam_1(X0,X1)
          & k1_xboole_0 != X1 ) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( ~ ( k1_xboole_0 = X1
              & k1_xboole_0 != k7_setfam_1(X0,X1) )
          & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
              & k1_xboole_0 != X1 ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ~ ( k1_xboole_0 = X1
            & k1_xboole_0 != k7_setfam_1(X0,X1) )
        & ~ ( k1_xboole_0 = k7_setfam_1(X0,X1)
            & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).

fof(f140,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_3 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_3 ),
    inference(resolution,[],[f76,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
              | ~ r1_tarski(X1,k7_setfam_1(X0,X2)) )
            & ( r1_tarski(X1,k7_setfam_1(X0,X2))
              | ~ r1_tarski(k7_setfam_1(X0,X1),X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f76,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl3_3
  <=> r1_tarski(sK1,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f37,plain,
    ( sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_1
  <=> sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f17,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f31,plain,(
    ! [X0] : sQ2_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f137,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f134,f37])).

fof(f134,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f129,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X1,X0)
      | ~ sQ2_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f21])).

fof(f129,plain,
    ( ~ sQ2_eqProxy(k7_setfam_1(sK0,sK1),k1_xboole_0)
    | spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f125,f75])).

fof(f75,plain,
    ( r1_tarski(sK1,k7_setfam_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | ~ sQ2_eqProxy(X0,k1_xboole_0) )
    | spl3_2 ),
    inference(resolution,[],[f112,f31])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( ~ sQ2_eqProxy(X1,sK1)
        | ~ r1_tarski(X1,X0)
        | ~ sQ2_eqProxy(X0,k1_xboole_0) )
    | spl3_2 ),
    inference(resolution,[],[f109,f29])).

fof(f109,plain,
    ( ~ r1_tarski(sK1,k1_xboole_0)
    | spl3_2 ),
    inference(resolution,[],[f40,f26])).

fof(f26,plain,(
    ! [X0] :
      ( sQ2_eqProxy(k1_xboole_0,X0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(equality_proxy_replacement,[],[f18,f21])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f40,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl3_2
  <=> sQ2_eqProxy(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f108,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f106,f41])).

fof(f41,plain,
    ( sQ2_eqProxy(k1_xboole_0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f106,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,sK1)
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f25,f37])).

fof(f25,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | ~ sQ2_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f13,f21,f21])).

fof(f13,plain,
    ( k1_xboole_0 != k7_setfam_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,
    ( ~ spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f41,f17,f31,f76,f29])).

fof(f92,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f89,f41])).

fof(f89,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,sK1)
    | spl3_4 ),
    inference(resolution,[],[f80,f32])).

fof(f80,plain,
    ( ~ sQ2_eqProxy(sK1,k1_xboole_0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_4
  <=> sQ2_eqProxy(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f81,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f72,f35,f78,f74])).

fof(f72,plain,
    ( ~ sQ2_eqProxy(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f69,f12])).

fof(f69,plain,
    ( ~ sQ2_eqProxy(sK1,k1_xboole_0)
    | ~ r1_tarski(sK1,k7_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_1 ),
    inference(resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k7_setfam_1(sK0,X0),sK1)
      | ~ r1_tarski(X0,k7_setfam_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    inference(resolution,[],[f20,f12])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f66,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k7_setfam_1(sK0,sK1),X1)
        | ~ sQ2_eqProxy(X1,k1_xboole_0) )
    | spl3_1 ),
    inference(resolution,[],[f53,f31])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( ~ sQ2_eqProxy(X1,k7_setfam_1(sK0,sK1))
        | ~ r1_tarski(X1,X0)
        | ~ sQ2_eqProxy(X0,k1_xboole_0) )
    | spl3_1 ),
    inference(resolution,[],[f29,f43])).

fof(f43,plain,
    ( ~ r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0)
    | spl3_1 ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f42,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f22,f39,f35])).

fof(f22,plain,
    ( sQ2_eqProxy(k1_xboole_0,sK1)
    | sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    inference(equality_proxy_replacement,[],[f16,f21,f21])).

fof(f16,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:19:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (29490)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.46  % (29488)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (29488)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f42,f81,f92,f97,f108,f137,f146])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~spl3_1 | spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f31,f17,f37,f141,f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (r1_tarski(X1,X3) | ~sQ2_eqProxy(X2,X3) | ~r1_tarski(X0,X2) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~r1_tarski(k7_setfam_1(sK0,sK1),sK1) | spl3_3),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (((k1_xboole_0 = sK1 & k1_xboole_0 != k7_setfam_1(sK0,sK1)) | (k1_xboole_0 = k7_setfam_1(sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0,X1] : (((k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) | (k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (~(k1_xboole_0 = X1 & k1_xboole_0 != k7_setfam_1(X0,X1)) & ~(k1_xboole_0 = k7_setfam_1(X0,X1) & k1_xboole_0 != X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tops_2)).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~r1_tarski(k7_setfam_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_3),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f138])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    ~r1_tarski(k7_setfam_1(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_3),
% 0.21/0.47    inference(resolution,[],[f76,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((r1_tarski(k7_setfam_1(X0,X1),X2) | ~r1_tarski(X1,k7_setfam_1(X0,X2))) & (r1_tarski(X1,k7_setfam_1(X0,X2)) | ~r1_tarski(k7_setfam_1(X0,X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(nnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_setfam_1)).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k7_setfam_1(sK0,sK1)) | spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(sK1,k7_setfam_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) | ~spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl3_1 <=> sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (sQ2_eqProxy(X0,X0)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    ~spl3_1 | spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f136])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    $false | (~spl3_1 | spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(subsumption_resolution,[],[f134,f37])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) | (spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(resolution,[],[f129,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (sQ2_eqProxy(X1,X0) | ~sQ2_eqProxy(X0,X1)) )),
% 0.21/0.47    inference(equality_proxy_axiom,[],[f21])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k7_setfam_1(sK0,sK1),k1_xboole_0) | (spl3_2 | ~spl3_3)),
% 0.21/0.47    inference(resolution,[],[f125,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    r1_tarski(sK1,k7_setfam_1(sK0,sK1)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f74])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(sK1,X0) | ~sQ2_eqProxy(X0,k1_xboole_0)) ) | spl3_2),
% 0.21/0.47    inference(resolution,[],[f112,f31])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sQ2_eqProxy(X1,sK1) | ~r1_tarski(X1,X0) | ~sQ2_eqProxy(X0,k1_xboole_0)) ) | spl3_2),
% 0.21/0.47    inference(resolution,[],[f109,f29])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ~r1_tarski(sK1,k1_xboole_0) | spl3_2),
% 0.21/0.47    inference(resolution,[],[f40,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (sQ2_eqProxy(k1_xboole_0,X0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f18,f21])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,sK1) | spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl3_2 <=> sQ2_eqProxy(k1_xboole_0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f107])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    $false | (~spl3_1 | ~spl3_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    sQ2_eqProxy(k1_xboole_0,sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f39])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,sK1) | ~spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f25,f37])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) | ~sQ2_eqProxy(k1_xboole_0,sK1)),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f13,f21,f21])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    k1_xboole_0 != k7_setfam_1(sK0,sK1) | k1_xboole_0 != sK1),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    ~spl3_2 | spl3_3),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f93])).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    $false | (~spl3_2 | spl3_3)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f41,f17,f31,f76,f29])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~spl3_2 | spl3_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f91])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    $false | (~spl3_2 | spl3_4)),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f41])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,sK1) | spl3_4),
% 0.21/0.47    inference(resolution,[],[f80,f32])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~sQ2_eqProxy(sK1,k1_xboole_0) | spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f78])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    spl3_4 <=> sQ2_eqProxy(sK1,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f81,plain,(
% 0.21/0.47    ~spl3_3 | ~spl3_4 | spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f72,f35,f78,f74])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~sQ2_eqProxy(sK1,k1_xboole_0) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f69,f12])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ~sQ2_eqProxy(sK1,k1_xboole_0) | ~r1_tarski(sK1,k7_setfam_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f66,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k7_setfam_1(sK0,X0),sK1) | ~r1_tarski(X0,k7_setfam_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(sK0)))) )),
% 0.21/0.47    inference(resolution,[],[f20,f12])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r1_tarski(X1,k7_setfam_1(X0,X2)) | r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    ( ! [X1] : (~r1_tarski(k7_setfam_1(sK0,sK1),X1) | ~sQ2_eqProxy(X1,k1_xboole_0)) ) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f53,f31])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~sQ2_eqProxy(X1,k7_setfam_1(sK0,sK1)) | ~r1_tarski(X1,X0) | ~sQ2_eqProxy(X0,k1_xboole_0)) ) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f29,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~r1_tarski(k7_setfam_1(sK0,sK1),k1_xboole_0) | spl3_1),
% 0.21/0.47    inference(resolution,[],[f26,f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ~sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1)) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f35])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    spl3_1 | spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f39,f35])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    sQ2_eqProxy(k1_xboole_0,sK1) | sQ2_eqProxy(k1_xboole_0,k7_setfam_1(sK0,sK1))),
% 0.21/0.47    inference(equality_proxy_replacement,[],[f16,f21,f21])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 = sK1 | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29488)------------------------------
% 0.21/0.47  % (29488)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29488)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29488)Memory used [KB]: 6140
% 0.21/0.47  % (29488)Time elapsed: 0.056 s
% 0.21/0.47  % (29488)------------------------------
% 0.21/0.47  % (29488)------------------------------
% 0.21/0.47  % (29482)Success in time 0.115 s
%------------------------------------------------------------------------------
