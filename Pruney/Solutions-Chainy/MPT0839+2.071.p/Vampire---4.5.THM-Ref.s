%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:52 EST 2020

% Result     : Theorem 1.40s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 110 expanded)
%              Number of leaves         :   11 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  160 ( 323 expanded)
%              Number of equality atoms :   24 (  61 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f206,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f196,f205])).

fof(f205,plain,
    ( spl5_4
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | spl5_4
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f203,f102])).

fof(f102,plain,
    ( ~ sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl5_4
  <=> sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f203,plain,
    ( sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f202,f43])).

fof(f43,plain,(
    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
          | ~ m1_subset_1(X3,X1) )
      & k1_xboole_0 != k2_relset_1(X1,X0,X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ~ ( ! [X3] :
                ( m1_subset_1(X3,X1)
               => ~ r2_hidden(X3,k1_relset_1(X1,X0,X2)) )
            & k1_xboole_0 != k2_relset_1(X1,X0,X2) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f202,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))
    | ~ spl5_5 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))
    | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))
    | ~ spl5_5 ),
    inference(resolution,[],[f106,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ4_eqProxy(k1_xboole_0,X1)
      | m1_subset_1(sK3(X0,X1),X0) ) ),
    inference(equality_proxy_replacement,[],[f27,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ4_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | m1_subset_1(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)
        | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)
        | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f196,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f195])).

fof(f195,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f194,f21])).

fof(f194,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f186,f156])).

fof(f156,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f151,f49])).

fof(f49,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f48,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f21,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) ),
    inference(resolution,[],[f147,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | sQ4_eqProxy(k1_xboole_0,k2_relat_1(X0))
      | ~ sQ4_eqProxy(k1_xboole_0,k1_relat_1(X0)) ) ),
    inference(equality_proxy_replacement,[],[f24,f32,f32])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f147,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2)) ),
    inference(resolution,[],[f68,f56])).

fof(f56,plain,(
    ! [X2] :
      ( ~ sQ4_eqProxy(X2,k2_relset_1(sK1,sK0,sK2))
      | ~ sQ4_eqProxy(k1_xboole_0,X2) ) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | ~ sQ4_eqProxy(X1,X2)
      | sQ4_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f33,plain,(
    ~ sQ4_eqProxy(k1_xboole_0,k2_relset_1(sK1,sK0,sK2)) ),
    inference(equality_proxy_replacement,[],[f22,f32])).

fof(f22,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f68,plain,(
    sQ4_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[],[f45,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ sQ4_eqProxy(X0,X1)
      | sQ4_eqProxy(X1,X0) ) ),
    inference(equality_proxy_axiom,[],[f32])).

fof(f45,plain,(
    sQ4_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2)) ),
    inference(resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ4_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f29,f32])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f186,plain,
    ( sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_4 ),
    inference(resolution,[],[f113,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sQ4_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2)) ) ),
    inference(equality_proxy_replacement,[],[f30,f32])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f113,plain,
    ( ! [X1] :
        ( ~ sQ4_eqProxy(k1_relset_1(sK1,sK0,sK2),X1)
        | sQ4_eqProxy(k1_xboole_0,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f103,f42])).

fof(f103,plain,
    ( sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f107,plain,
    ( spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f57,f105,f101])).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1)
      | ~ m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))
      | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) ) ),
    inference(resolution,[],[f20,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | sQ4_eqProxy(k1_xboole_0,X1)
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f32])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k1_xboole_0 = X1
      | r2_hidden(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:46:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (16328)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.53  % (16319)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (16323)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.54  % (16323)Refutation not found, incomplete strategy% (16323)------------------------------
% 0.21/0.54  % (16323)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16323)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16323)Memory used [KB]: 10618
% 0.21/0.54  % (16323)Time elapsed: 0.108 s
% 0.21/0.54  % (16323)------------------------------
% 0.21/0.54  % (16323)------------------------------
% 1.40/0.54  % (16318)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 1.40/0.54  % (16318)Refutation found. Thanks to Tanya!
% 1.40/0.54  % SZS status Theorem for theBenchmark
% 1.40/0.54  % SZS output start Proof for theBenchmark
% 1.40/0.54  fof(f206,plain,(
% 1.40/0.54    $false),
% 1.40/0.54    inference(avatar_sat_refutation,[],[f107,f196,f205])).
% 1.40/0.54  fof(f205,plain,(
% 1.40/0.54    spl5_4 | ~spl5_5),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f204])).
% 1.40/0.54  fof(f204,plain,(
% 1.40/0.54    $false | (spl5_4 | ~spl5_5)),
% 1.40/0.54    inference(subsumption_resolution,[],[f203,f102])).
% 1.40/0.54  fof(f102,plain,(
% 1.40/0.54    ~sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) | spl5_4),
% 1.40/0.54    inference(avatar_component_clause,[],[f101])).
% 1.40/0.54  fof(f101,plain,(
% 1.40/0.54    spl5_4 <=> sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.40/0.54  fof(f203,plain,(
% 1.40/0.54    sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) | ~spl5_5),
% 1.40/0.54    inference(subsumption_resolution,[],[f202,f43])).
% 1.40/0.54  fof(f43,plain,(
% 1.40/0.54    m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1))),
% 1.40/0.54    inference(resolution,[],[f21,f31])).
% 1.40/0.54  fof(f31,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f19])).
% 1.40/0.54  fof(f19,plain,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.54    inference(ennf_transformation,[],[f5])).
% 1.40/0.54  fof(f5,axiom,(
% 1.40/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.40/0.54  fof(f21,plain,(
% 1.40/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.40/0.54    inference(cnf_transformation,[],[f12])).
% 1.40/0.54  fof(f12,plain,(
% 1.40/0.54    ? [X0,X1,X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.40/0.54    inference(flattening,[],[f11])).
% 1.40/0.54  fof(f11,plain,(
% 1.40/0.54    ? [X0,X1,X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.40/0.54    inference(ennf_transformation,[],[f10])).
% 1.40/0.54  fof(f10,plain,(
% 1.40/0.54    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))),
% 1.40/0.54    inference(pure_predicate_removal,[],[f9])).
% 1.40/0.54  fof(f9,negated_conjecture,(
% 1.40/0.54    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.40/0.54    inference(negated_conjecture,[],[f8])).
% 1.40/0.54  fof(f8,conjecture,(
% 1.40/0.54    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 1.40/0.54  fof(f202,plain,(
% 1.40/0.54    ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) | ~spl5_5),
% 1.40/0.54    inference(duplicate_literal_removal,[],[f201])).
% 1.40/0.54  fof(f201,plain,(
% 1.40/0.54    ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(sK1)) | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) | ~spl5_5),
% 1.40/0.54    inference(resolution,[],[f106,f37])).
% 1.40/0.54  fof(f37,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ4_eqProxy(k1_xboole_0,X1) | m1_subset_1(sK3(X0,X1),X0)) )),
% 1.40/0.54    inference(equality_proxy_replacement,[],[f27,f32])).
% 1.40/0.54  fof(f32,plain,(
% 1.40/0.54    ! [X1,X0] : (sQ4_eqProxy(X0,X1) <=> X0 = X1)),
% 1.40/0.54    introduced(equality_proxy_definition,[new_symbols(naming,[sQ4_eqProxy])])).
% 1.40/0.54  fof(f27,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | m1_subset_1(sK3(X0,X1),X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f16])).
% 1.40/0.54  fof(f16,plain,(
% 1.40/0.54    ! [X0,X1] : (? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(flattening,[],[f15])).
% 1.40/0.54  fof(f15,plain,(
% 1.40/0.54    ! [X0,X1] : ((? [X2] : (r2_hidden(X2,X1) & m1_subset_1(X2,X0)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.40/0.54    inference(ennf_transformation,[],[f1])).
% 1.40/0.54  fof(f1,axiom,(
% 1.40/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ~(! [X2] : (m1_subset_1(X2,X0) => ~r2_hidden(X2,X1)) & k1_xboole_0 != X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_subset_1)).
% 1.40/0.54  fof(f106,plain,(
% 1.40/0.54    ( ! [X0] : (~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0))) ) | ~spl5_5),
% 1.40/0.54    inference(avatar_component_clause,[],[f105])).
% 1.40/0.54  fof(f105,plain,(
% 1.40/0.54    spl5_5 <=> ! [X0] : (~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)))),
% 1.40/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.40/0.54  fof(f196,plain,(
% 1.40/0.54    ~spl5_4),
% 1.40/0.54    inference(avatar_contradiction_clause,[],[f195])).
% 1.40/0.54  fof(f195,plain,(
% 1.40/0.54    $false | ~spl5_4),
% 1.40/0.54    inference(subsumption_resolution,[],[f194,f21])).
% 1.40/0.54  fof(f194,plain,(
% 1.40/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_4),
% 1.40/0.54    inference(subsumption_resolution,[],[f186,f156])).
% 1.40/0.54  fof(f156,plain,(
% 1.40/0.54    ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))),
% 1.40/0.54    inference(subsumption_resolution,[],[f151,f49])).
% 1.40/0.54  fof(f49,plain,(
% 1.40/0.54    v1_relat_1(sK2)),
% 1.40/0.54    inference(subsumption_resolution,[],[f48,f26])).
% 1.40/0.54  fof(f26,plain,(
% 1.40/0.54    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.40/0.54    inference(cnf_transformation,[],[f3])).
% 1.40/0.54  fof(f3,axiom,(
% 1.40/0.54    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.40/0.54  fof(f48,plain,(
% 1.40/0.54    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 1.40/0.54    inference(resolution,[],[f21,f25])).
% 1.40/0.54  fof(f25,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f14])).
% 1.40/0.54  fof(f14,plain,(
% 1.40/0.54    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f2])).
% 1.40/0.54  fof(f2,axiom,(
% 1.40/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.40/0.54  fof(f151,plain,(
% 1.40/0.54    ~v1_relat_1(sK2) | ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2))),
% 1.40/0.54    inference(resolution,[],[f147,f34])).
% 1.40/0.54  fof(f34,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_relat_1(X0) | sQ4_eqProxy(k1_xboole_0,k2_relat_1(X0)) | ~sQ4_eqProxy(k1_xboole_0,k1_relat_1(X0))) )),
% 1.40/0.54    inference(equality_proxy_replacement,[],[f24,f32,f32])).
% 1.40/0.54  fof(f24,plain,(
% 1.40/0.54    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.40/0.54    inference(cnf_transformation,[],[f13])).
% 1.40/0.54  fof(f13,plain,(
% 1.40/0.54    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.40/0.54    inference(ennf_transformation,[],[f4])).
% 1.40/0.54  fof(f4,axiom,(
% 1.40/0.54    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.40/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.40/0.54  fof(f147,plain,(
% 1.40/0.54    ~sQ4_eqProxy(k1_xboole_0,k2_relat_1(sK2))),
% 1.40/0.54    inference(resolution,[],[f68,f56])).
% 1.40/0.54  fof(f56,plain,(
% 1.40/0.54    ( ! [X2] : (~sQ4_eqProxy(X2,k2_relset_1(sK1,sK0,sK2)) | ~sQ4_eqProxy(k1_xboole_0,X2)) )),
% 1.40/0.54    inference(resolution,[],[f33,f42])).
% 1.40/0.54  fof(f42,plain,(
% 1.40/0.54    ( ! [X2,X0,X1] : (~sQ4_eqProxy(X0,X1) | ~sQ4_eqProxy(X1,X2) | sQ4_eqProxy(X0,X2)) )),
% 1.40/0.54    inference(equality_proxy_axiom,[],[f32])).
% 1.40/0.54  fof(f33,plain,(
% 1.40/0.54    ~sQ4_eqProxy(k1_xboole_0,k2_relset_1(sK1,sK0,sK2))),
% 1.40/0.54    inference(equality_proxy_replacement,[],[f22,f32])).
% 1.40/0.54  fof(f22,plain,(
% 1.40/0.54    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 1.40/0.54    inference(cnf_transformation,[],[f12])).
% 1.40/0.54  fof(f68,plain,(
% 1.40/0.54    sQ4_eqProxy(k2_relat_1(sK2),k2_relset_1(sK1,sK0,sK2))),
% 1.40/0.54    inference(resolution,[],[f45,f41])).
% 1.40/0.54  fof(f41,plain,(
% 1.40/0.54    ( ! [X0,X1] : (~sQ4_eqProxy(X0,X1) | sQ4_eqProxy(X1,X0)) )),
% 1.40/0.54    inference(equality_proxy_axiom,[],[f32])).
% 1.40/0.54  fof(f45,plain,(
% 1.40/0.54    sQ4_eqProxy(k2_relset_1(sK1,sK0,sK2),k2_relat_1(sK2))),
% 1.40/0.54    inference(resolution,[],[f21,f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ4_eqProxy(k2_relset_1(X0,X1,X2),k2_relat_1(X2))) )),
% 1.40/0.55    inference(equality_proxy_replacement,[],[f29,f32])).
% 1.40/0.55  fof(f29,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f17])).
% 1.40/0.55  fof(f17,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f7])).
% 1.40/0.55  fof(f7,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.40/0.55  fof(f186,plain,(
% 1.40/0.55    sQ4_eqProxy(k1_xboole_0,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_4),
% 1.40/0.55    inference(resolution,[],[f113,f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sQ4_eqProxy(k1_relset_1(X0,X1,X2),k1_relat_1(X2))) )),
% 1.40/0.55    inference(equality_proxy_replacement,[],[f30,f32])).
% 1.40/0.55  fof(f30,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f18])).
% 1.40/0.55  fof(f18,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f6])).
% 1.40/0.55  fof(f6,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.40/0.55  fof(f113,plain,(
% 1.40/0.55    ( ! [X1] : (~sQ4_eqProxy(k1_relset_1(sK1,sK0,sK2),X1) | sQ4_eqProxy(k1_xboole_0,X1)) ) | ~spl5_4),
% 1.40/0.55    inference(resolution,[],[f103,f42])).
% 1.40/0.55  fof(f103,plain,(
% 1.40/0.55    sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2)) | ~spl5_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f101])).
% 1.40/0.55  fof(f107,plain,(
% 1.40/0.55    spl5_4 | spl5_5),
% 1.40/0.55    inference(avatar_split_clause,[],[f57,f105,f101])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ( ! [X0] : (~m1_subset_1(sK3(X0,k1_relset_1(sK1,sK0,sK2)),sK1) | ~m1_subset_1(k1_relset_1(sK1,sK0,sK2),k1_zfmisc_1(X0)) | sQ4_eqProxy(k1_xboole_0,k1_relset_1(sK1,sK0,sK2))) )),
% 1.40/0.55    inference(resolution,[],[f20,f36])).
% 1.40/0.55  fof(f36,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | sQ4_eqProxy(k1_xboole_0,X1) | r2_hidden(sK3(X0,X1),X1)) )),
% 1.40/0.55    inference(equality_proxy_replacement,[],[f28,f32])).
% 1.40/0.55  fof(f28,plain,(
% 1.40/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k1_xboole_0 = X1 | r2_hidden(sK3(X0,X1),X1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f16])).
% 1.40/0.55  fof(f20,plain,(
% 1.40/0.55    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f12])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (16318)------------------------------
% 1.40/0.55  % (16318)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (16318)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (16318)Memory used [KB]: 6140
% 1.40/0.55  % (16318)Time elapsed: 0.111 s
% 1.40/0.55  % (16318)------------------------------
% 1.40/0.55  % (16318)------------------------------
% 1.40/0.55  % (16312)Success in time 0.188 s
%------------------------------------------------------------------------------
