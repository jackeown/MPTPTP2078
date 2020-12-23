%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 123 expanded)
%              Number of leaves         :    8 (  37 expanded)
%              Depth                    :   11
%              Number of atoms          :  144 ( 752 expanded)
%              Number of equality atoms :   20 ( 165 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f80,f107])).

fof(f107,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f104,f89])).

fof(f89,plain,
    ( sQ3_eqProxy(sK1,k1_xboole_0)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f40,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | sQ3_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f40,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl4_1
  <=> sQ3_eqProxy(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f104,plain,
    ( ~ sQ3_eqProxy(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f68,f99,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ sQ3_eqProxy(X0,X1)
      | v1_xboole_0(X1) ) ),
    inference(equality_proxy_axiom,[],[f25])).

fof(f99,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f59,f45,f30])).

fof(f45,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_2
  <=> sQ3_eqProxy(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(unit_resulting_resolution,[],[f20,f18,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

fof(f18,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ v1_partfun1(sK2,sK0)
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ v1_partfun1(X2,X0)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ~ v1_partfun1(sK2,sK0)
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ v1_partfun1(X2,X0)
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X2,X0,X1)
            & v1_funct_1(X2) )
         => ( v1_partfun1(X2,X0)
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f20,plain,(
    ~ v1_partfun1(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f68,plain,(
    v1_xboole_0(sK1) ),
    inference(unit_resulting_resolution,[],[f16,f20,f17,f18,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f17,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f64,f18])).

fof(f64,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f47,f16,f20,f17,f23])).

fof(f47,plain,
    ( ~ v1_xboole_0(sK1)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f41,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sQ3_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f21,f25])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f41,plain,
    ( ~ sQ3_eqProxy(k1_xboole_0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f46,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f26,f43,f39])).

fof(f26,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK0)
    | ~ sQ3_eqProxy(k1_xboole_0,sK1) ),
    inference(equality_proxy_replacement,[],[f19,f25,f25])).

fof(f19,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (21760)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (21762)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (21769)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (21771)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.48  % (21769)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f46,f80,f107])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    ~spl4_1 | ~spl4_2),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f106])).
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    $false | (~spl4_1 | ~spl4_2)),
% 0.22/0.48    inference(subsumption_resolution,[],[f104,f89])).
% 0.22/0.48  fof(f89,plain,(
% 0.22/0.48    sQ3_eqProxy(sK1,k1_xboole_0) | ~spl4_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f40,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~sQ3_eqProxy(X0,X1) | sQ3_eqProxy(X1,X0)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.22/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    sQ3_eqProxy(k1_xboole_0,sK1) | ~spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl4_1 <=> sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.48  fof(f104,plain,(
% 0.22/0.48    ~sQ3_eqProxy(sK1,k1_xboole_0) | ~spl4_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f68,f99,f30])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~sQ3_eqProxy(X0,X1) | v1_xboole_0(X1)) )),
% 0.22/0.48    inference(equality_proxy_axiom,[],[f25])).
% 0.22/0.48  fof(f99,plain,(
% 0.22/0.48    ~v1_xboole_0(k1_xboole_0) | ~spl4_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f59,f45,f30])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    sQ3_eqProxy(k1_xboole_0,sK0) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl4_2 <=> sQ3_eqProxy(k1_xboole_0,sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    ~v1_xboole_0(sK0)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f20,f18,f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (~v1_partfun1(sK2,sK0) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 0.22/0.48    inference(flattening,[],[f6])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (((~v1_partfun1(X2,X0) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ~v1_partfun1(sK2,sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    v1_xboole_0(sK1)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f16,f20,f17,f18,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f79])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    $false | spl4_1),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f18])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f47,f16,f20,f17,f23])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~v1_xboole_0(sK1) | spl4_1),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f41,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_xboole_0(X0) | sQ3_eqProxy(k1_xboole_0,X0)) )),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f21,f25])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~sQ3_eqProxy(k1_xboole_0,sK1) | spl4_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~spl4_1 | spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f43,f39])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    sQ3_eqProxy(k1_xboole_0,sK0) | ~sQ3_eqProxy(k1_xboole_0,sK1)),
% 0.22/0.48    inference(equality_proxy_replacement,[],[f19,f25,f25])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (21769)------------------------------
% 0.22/0.48  % (21769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21769)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (21769)Memory used [KB]: 10618
% 0.22/0.48  % (21769)Time elapsed: 0.054 s
% 0.22/0.48  % (21769)------------------------------
% 0.22/0.48  % (21769)------------------------------
% 0.22/0.48  % (21754)Success in time 0.121 s
%------------------------------------------------------------------------------
