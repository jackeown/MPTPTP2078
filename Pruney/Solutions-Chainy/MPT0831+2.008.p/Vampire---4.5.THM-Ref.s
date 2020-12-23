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
% DateTime   : Thu Dec  3 12:56:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 121 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :    7
%              Number of atoms          :  189 ( 296 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f53,f59,f65,f71,f77,f85,f95,f97,f102])).

fof(f102,plain,
    ( ~ spl5_7
    | ~ spl5_2
    | spl5_9 ),
    inference(avatar_split_clause,[],[f99,f88,f45,f74])).

fof(f74,plain,
    ( spl5_7
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f45,plain,
    ( spl5_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f88,plain,
    ( spl5_9
  <=> r1_tarski(k1_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f99,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_2
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f47,f90,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

% (1339)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f90,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f88])).

fof(f47,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f97,plain,
    ( spl5_10
    | ~ spl5_3
    | spl5_6 ),
    inference(avatar_split_clause,[],[f96,f68,f50,f92])).

fof(f92,plain,
    ( spl5_10
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f50,plain,
    ( spl5_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f68,plain,
    ( spl5_6
  <=> sP4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f96,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl5_3
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f52,f70,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X1,X0) ) ),
    inference(cnf_transformation,[],[f37_D])).

fof(f37_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_relset_1(X0,X1,X2,X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    <=> ~ sP4(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f70,plain,
    ( ~ sP4(sK0,sK1)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f52,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f95,plain,
    ( ~ spl5_4
    | ~ spl5_9
    | ~ spl5_10
    | spl5_8 ),
    inference(avatar_split_clause,[],[f86,f82,f92,f88,f56])).

fof(f56,plain,
    ( spl5_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f82,plain,
    ( spl5_8
  <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f86,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ r1_tarski(k1_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | spl5_8 ),
    inference(superposition,[],[f84,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f84,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( ~ spl5_8
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f80,f50,f40,f82])).

fof(f40,plain,
    ( spl5_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f80,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | spl5_1
    | ~ spl5_3 ),
    inference(backward_demodulation,[],[f42,f78])).

fof(f78,plain,
    ( ! [X0] : k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f52,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f42,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f77,plain,
    ( spl5_7
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f72,f62,f56,f74])).

fof(f62,plain,
    ( spl5_5
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl5_4
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f58,f64,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f64,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f58,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f71,plain,
    ( ~ spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f50,f68])).

fof(f66,plain,
    ( ~ sP4(sK0,sK1)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f52,f38])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(general_splitting,[],[f29,f37_D])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f65,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f60,f50,f62])).

fof(f60,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f52,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f59,plain,
    ( spl5_4
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f54,f50,f56])).

fof(f54,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f53,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f26,f50])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f48,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f27,f45])).

fof(f27,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f28,f40])).

fof(f28,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n011.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:02:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1323)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (1322)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (1324)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (1324)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (1319)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (1321)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (1336)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.51  % (1337)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (1340)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f109,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f43,f48,f53,f59,f65,f71,f77,f85,f95,f97,f102])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    ~spl5_7 | ~spl5_2 | spl5_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f99,f88,f45,f74])).
% 0.22/0.51  fof(f74,plain,(
% 0.22/0.51    spl5_7 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    spl5_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl5_9 <=> r1_tarski(k1_relat_1(sK3),sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK3),sK1) | (~spl5_2 | spl5_9)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f47,f90,f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  % (1339)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ~r1_tarski(k1_relat_1(sK3),sK2) | spl5_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2) | ~spl5_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f45])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    spl5_10 | ~spl5_3 | spl5_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f96,f68,f50,f92])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    spl5_10 <=> r2_relset_1(sK1,sK0,sK3,sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    spl5_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    spl5_6 <=> sP4(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    r2_relset_1(sK1,sK0,sK3,sK3) | (~spl5_3 | spl5_6)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f70,f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37_D])).
% 0.22/0.51  fof(f37_D,plain,(
% 0.22/0.51    ( ! [X0,X1] : (( ! [X2] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) <=> ~sP4(X1,X0)) )),
% 0.22/0.51    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ~sP4(sK0,sK1) | spl5_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f68])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl5_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f50])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~spl5_4 | ~spl5_9 | ~spl5_10 | spl5_8),
% 0.22/0.51    inference(avatar_split_clause,[],[f86,f82,f92,f88,f56])).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    spl5_4 <=> v1_relat_1(sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    spl5_8 <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,sK3,sK3) | ~r1_tarski(k1_relat_1(sK3),sK2) | ~v1_relat_1(sK3) | spl5_8),
% 0.22/0.51    inference(superposition,[],[f84,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : ((k7_relat_1(X1,X0) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k7_relat_1(X1,X0) = X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | spl5_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f82])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ~spl5_8 | spl5_1 | ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f80,f50,f40,f82])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    spl5_1 <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) | (spl5_1 | ~spl5_3)),
% 0.22/0.51    inference(backward_demodulation,[],[f42,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (k5_relset_1(sK1,sK0,sK3,X0) = k7_relat_1(sK3,X0)) ) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) | spl5_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f40])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    spl5_7 | ~spl5_4 | ~spl5_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f72,f62,f56,f74])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    spl5_5 <=> v4_relat_1(sK3,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    r1_tarski(k1_relat_1(sK3),sK1) | (~spl5_4 | ~spl5_5)),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f58,f64,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    v4_relat_1(sK3,sK1) | ~spl5_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f62])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl5_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f56])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ~spl5_6 | ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f66,f50,f68])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ~sP4(sK0,sK1) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X3,X1] : (~sP4(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(general_splitting,[],[f29,f37_D])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(flattening,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    spl5_5 | ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f60,f50,f62])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    v4_relat_1(sK3,sK1) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    spl5_4 | ~spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f54,f50,f56])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    v1_relat_1(sK3) | ~spl5_3),
% 0.22/0.51    inference(unit_resulting_resolution,[],[f52,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    spl5_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f26,f50])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) => (~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : (~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.51    inference(flattening,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0,X1,X2,X3] : ((~r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) & r1_tarski(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(X1,X2) => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    spl5_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f27,f45])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    r1_tarski(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ~spl5_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f28,f40])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ~r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (1324)------------------------------
% 0.22/0.51  % (1324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1324)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (1324)Memory used [KB]: 10618
% 0.22/0.51  % (1324)Time elapsed: 0.098 s
% 0.22/0.51  % (1324)------------------------------
% 0.22/0.51  % (1324)------------------------------
% 0.22/0.51  % (1317)Success in time 0.148 s
%------------------------------------------------------------------------------
