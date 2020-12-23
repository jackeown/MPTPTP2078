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
% DateTime   : Thu Dec  3 12:57:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 103 expanded)
%              Number of leaves         :   12 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  139 ( 285 expanded)
%              Number of equality atoms :   22 (  55 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f134,f137])).

fof(f137,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f109,f99])).

fof(f99,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f67,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ sQ4_eqProxy(X0,k2_relset_1(sK1,sK0,sK2))
      | ~ sQ4_eqProxy(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f35,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | ~ sQ4_eqProxy(X1,X2)
      | sQ4_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f34])).

% (24144)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
fof(f34,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f35,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k2_relset_1(sK1,sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f24,f34])).

fof(f24,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                    & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
                  & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).

fof(f67,plain,(
    sQ4_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[],[f46,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f34])).

fof(f46,plain,(
    sQ4_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ4_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f30,f34])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,
    ( sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_6
  <=> sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl5_5 ),
    inference(subsumption_resolution,[],[f132,f61])).

fof(f61,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_relset_1(sK1,sK0,sK2)) ),
    inference(subsumption_resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f59,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_relset_1(sK1,sK0,sK2))
      | m1_subset_1(X0,sK1) ) ),
    inference(resolution,[],[f44,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f44,plain,(
    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f23,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f132,plain,
    ( r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2))
    | spl5_5 ),
    inference(subsumption_resolution,[],[f130,f105])).

fof(f105,plain,
    ( ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_5
  <=> sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))
    | r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[],[f65,f38])).

fof(f38,plain,(
    ! [X0] :
      ( sQ4_eqProxy(k1_xboole_0,X0)
      | r2_hidden(sK3(X0),X0) ) ),
    inference(equality_proxy_replacement,[],[f28,f34])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f65,plain,(
    ! [X0] :
      ( ~ sQ4_eqProxy(X0,k1_relset_1(sK1,sK0,sK2))
      | sQ4_eqProxy(X0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f45,f43])).

fof(f45,plain,(
    sQ4_eqProxy(k1_relset_1(sK1,sK0,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f23,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ4_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f31,f34])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f112,plain,
    ( ~ spl5_5
    | spl5_6 ),
    inference(avatar_split_clause,[],[f52,f108,f104])).

fof(f52,plain,
    ( sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2))
    | ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f49,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sQ4_eqProxy(k1_xboole_0,k2_relat_1(X0))
      | ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f26,f34,f34])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f48,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:46:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.53  % (24130)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.53  % (24125)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.53  % (24123)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.53  % (24124)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.53  % (24126)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.53  % (24127)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.53  % (24124)Refutation not found, incomplete strategy% (24124)------------------------------
% 0.20/0.53  % (24124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (24126)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.54  % (24142)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.54  % (24143)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.54  % (24121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.54  % (24140)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.54  % (24122)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.54  % (24134)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f138,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f112,f134,f137])).
% 0.20/0.54  fof(f137,plain,(
% 0.20/0.54    ~spl5_6),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.54  fof(f136,plain,(
% 0.20/0.54    $false | ~spl5_6),
% 0.20/0.54    inference(subsumption_resolution,[],[f109,f99])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    ~sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f67,f55])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X0] : (~sQ4_eqProxy(X0,k2_relset_1(sK1,sK0,sK2)) | ~sQ4_eqProxy(k1_xboole_0,X0)) )),
% 0.20/0.54    inference(resolution,[],[f35,f43])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~sQ4_eqProxy(X0,X1) | ~sQ4_eqProxy(X1,X2) | sQ4_eqProxy(X0,X2)) )),
% 0.20/0.54    inference(equality_proxy_axiom,[],[f34])).
% 0.20/0.54  % (24144)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 0.20/0.54  fof(f35,plain,(
% 0.20/0.54    ~sQ4_eqProxy(k1_xboole_0,k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f24,f34])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.54    inference(flattening,[],[f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.54    inference(ennf_transformation,[],[f11])).
% 0.20/0.54  fof(f11,plain,(
% 0.20/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 0.20/0.54    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.54  fof(f10,negated_conjecture,(
% 0.20/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.54    inference(negated_conjecture,[],[f9])).
% 0.20/0.54  fof(f9,conjecture,(
% 0.20/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.20/0.54  fof(f67,plain,(
% 0.20/0.54    sQ4_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f46,f42])).
% 0.20/0.54  fof(f42,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~sQ4_eqProxy(X0,X1) | sQ4_eqProxy(X1,X0)) )),
% 0.20/0.54    inference(equality_proxy_axiom,[],[f34])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    sQ4_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f23,f39])).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ4_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f30,f34])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2)) | ~spl5_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f108])).
% 0.20/0.54  fof(f108,plain,(
% 0.20/0.54    spl5_6 <=> sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.54  fof(f134,plain,(
% 0.20/0.54    spl5_5),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.54  fof(f133,plain,(
% 0.20/0.54    $false | spl5_5),
% 0.20/0.54    inference(subsumption_resolution,[],[f132,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relset_1(sK1,sK0,sK2))) )),
% 0.20/0.54    inference(subsumption_resolution,[],[f59,f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f13])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(X0,k1_relset_1(sK1,sK0,sK2)) | m1_subset_1(X0,sK1)) )),
% 0.20/0.54    inference(resolution,[],[f44,f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.54    inference(flattening,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 0.20/0.54    inference(resolution,[],[f23,f32])).
% 0.20/0.54  fof(f32,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.54    inference(ennf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 0.20/0.54  fof(f132,plain,(
% 0.20/0.54    r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2)) | spl5_5),
% 0.20/0.54    inference(subsumption_resolution,[],[f130,f105])).
% 0.20/0.54  fof(f105,plain,(
% 0.20/0.54    ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) | spl5_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f104])).
% 0.20/0.54  fof(f104,plain,(
% 0.20/0.54    spl5_5 <=> sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.54  fof(f130,plain,(
% 0.20/0.54    sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) | r2_hidden(sK3(k1_relset_1(sK1,sK0,sK2)),k1_relset_1(sK1,sK0,sK2))),
% 0.20/0.54    inference(resolution,[],[f65,f38])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    ( ! [X0] : (sQ4_eqProxy(k1_xboole_0,X0) | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.54    inference(equality_proxy_replacement,[],[f28,f34])).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.54  fof(f65,plain,(
% 0.20/0.54    ( ! [X0] : (~sQ4_eqProxy(X0,k1_relset_1(sK1,sK0,sK2)) | sQ4_eqProxy(X0,k1_relat_1(sK2))) )),
% 0.20/0.54    inference(resolution,[],[f45,f43])).
% 0.20/0.54  fof(f45,plain,(
% 0.20/0.54    sQ4_eqProxy(k1_relset_1(sK1,sK0,sK2),k1_relat_1(sK2))),
% 0.20/0.54    inference(resolution,[],[f23,f40])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ4_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2))) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f31,f34])).
% 0.20/0.55  fof(f31,plain,(
% 0.20/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f18])).
% 0.20/0.55  fof(f18,plain,(
% 0.20/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.55    inference(ennf_transformation,[],[f7])).
% 0.20/0.55  fof(f7,axiom,(
% 0.20/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.55  fof(f112,plain,(
% 0.20/0.55    ~spl5_5 | spl5_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f52,f108,f104])).
% 0.20/0.55  fof(f52,plain,(
% 0.20/0.55    sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2)) | ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))),
% 0.20/0.55    inference(resolution,[],[f49,f36])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | sQ4_eqProxy(k1_xboole_0,k2_relat_1(X0)) | ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(X0))) )),
% 0.20/0.55    inference(equality_proxy_replacement,[],[f26,f34,f34])).
% 0.20/0.55  fof(f26,plain,(
% 0.20/0.55    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f14])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f5])).
% 0.20/0.55  fof(f5,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.55  fof(f49,plain,(
% 0.20/0.55    v1_relat_1(sK2)),
% 0.20/0.55    inference(subsumption_resolution,[],[f48,f29])).
% 0.20/0.55  fof(f29,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.55    inference(cnf_transformation,[],[f4])).
% 0.20/0.55  fof(f4,axiom,(
% 0.20/0.55    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.55  fof(f48,plain,(
% 0.20/0.55    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.20/0.55    inference(resolution,[],[f23,f27])).
% 0.20/0.55  fof(f27,plain,(
% 0.20/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f15])).
% 0.20/0.55  fof(f15,plain,(
% 0.20/0.55    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.55    inference(ennf_transformation,[],[f3])).
% 0.20/0.55  fof(f3,axiom,(
% 0.20/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (24126)------------------------------
% 0.20/0.55  % (24126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (24126)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (24126)Memory used [KB]: 6140
% 0.20/0.55  % (24126)Time elapsed: 0.116 s
% 0.20/0.55  % (24126)------------------------------
% 0.20/0.55  % (24126)------------------------------
% 0.20/0.55  % (24120)Success in time 0.186 s
%------------------------------------------------------------------------------
