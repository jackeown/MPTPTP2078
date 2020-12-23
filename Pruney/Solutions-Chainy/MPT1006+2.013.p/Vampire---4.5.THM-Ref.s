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
% DateTime   : Thu Dec  3 13:03:44 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 110 expanded)
%              Number of leaves         :   12 (  29 expanded)
%              Depth                    :   14
%              Number of atoms          :  134 ( 262 expanded)
%              Number of equality atoms :   39 ( 109 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10047)Refutation not found, incomplete strategy% (10047)------------------------------
% (10047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10047)Termination reason: Refutation not found, incomplete strategy

% (10047)Memory used [KB]: 6140
% (10047)Time elapsed: 0.108 s
% (10047)------------------------------
% (10047)------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f77,f89,f94,f96])).

fof(f96,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f50,f21])).

fof(f21,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f50,plain,
    ( ! [X0] : ~ v1_xboole_0(X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_3
  <=> ! [X0] : ~ v1_xboole_0(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,
    ( ~ spl3_2
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl3_2
    | spl3_5 ),
    inference(subsumption_resolution,[],[f92,f46])).

fof(f46,plain,
    ( v1_xboole_0(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f92,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_5 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_5 ),
    inference(superposition,[],[f76,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

fof(f76,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_5
  <=> v1_xboole_0(k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( ~ spl3_2
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl3_2
    | spl3_4 ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( ~ v1_xboole_0(sK2)
    | spl3_4 ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl3_4 ),
    inference(superposition,[],[f83,f33])).

fof(f83,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,sK1))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f80,f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(sK2,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f31,f23])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f19,f30])).

fof(f30,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f19,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).

fof(f80,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK2,sK1)))
    | ~ v1_xboole_0(k10_relat_1(sK2,sK1))
    | spl3_4 ),
    inference(superposition,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f30,f23])).

fof(f73,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f77,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f69,f75,f72])).

fof(f69,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK2,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0))) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( k10_relat_1(sK2,sK1) != X0
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ) ),
    inference(superposition,[],[f34,f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f34,plain,(
    ! [X0] :
      ( k8_relset_1(X0,sK0,sK2,sK1) != X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f20,f23])).

fof(f20,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f51,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f40,f45,f49])).

fof(f40,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2)
      | ~ v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(sK2)
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f24,f35])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:18:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (10050)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (10050)Refutation not found, incomplete strategy% (10050)------------------------------
% 0.21/0.48  % (10050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (10050)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (10050)Memory used [KB]: 10618
% 0.21/0.48  % (10050)Time elapsed: 0.028 s
% 0.21/0.48  % (10050)------------------------------
% 0.21/0.48  % (10050)------------------------------
% 0.21/0.50  % (10062)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (10055)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (10054)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.53  % (10052)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (10047)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (10060)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.54  % (10060)Refutation not found, incomplete strategy% (10060)------------------------------
% 0.21/0.54  % (10060)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10060)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10060)Memory used [KB]: 1535
% 0.21/0.54  % (10060)Time elapsed: 0.104 s
% 0.21/0.54  % (10060)------------------------------
% 0.21/0.54  % (10060)------------------------------
% 1.48/0.56  % (10049)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.48/0.56  % (10064)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.48/0.56  % (10049)Refutation found. Thanks to Tanya!
% 1.48/0.56  % SZS status Theorem for theBenchmark
% 1.48/0.56  % SZS output start Proof for theBenchmark
% 1.48/0.56  % (10047)Refutation not found, incomplete strategy% (10047)------------------------------
% 1.48/0.56  % (10047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (10047)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (10047)Memory used [KB]: 6140
% 1.48/0.56  % (10047)Time elapsed: 0.108 s
% 1.48/0.56  % (10047)------------------------------
% 1.48/0.56  % (10047)------------------------------
% 1.48/0.56  fof(f97,plain,(
% 1.48/0.56    $false),
% 1.48/0.56    inference(avatar_sat_refutation,[],[f51,f77,f89,f94,f96])).
% 1.48/0.56  fof(f96,plain,(
% 1.48/0.56    ~spl3_3),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f95])).
% 1.48/0.56  fof(f95,plain,(
% 1.48/0.56    $false | ~spl3_3),
% 1.48/0.56    inference(resolution,[],[f50,f21])).
% 1.48/0.56  fof(f21,plain,(
% 1.48/0.56    v1_xboole_0(o_0_0_xboole_0)),
% 1.48/0.56    inference(cnf_transformation,[],[f1])).
% 1.48/0.56  fof(f1,axiom,(
% 1.48/0.56    v1_xboole_0(o_0_0_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 1.48/0.56  fof(f50,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_xboole_0(X0)) ) | ~spl3_3),
% 1.48/0.56    inference(avatar_component_clause,[],[f49])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    spl3_3 <=> ! [X0] : ~v1_xboole_0(X0)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.48/0.56  fof(f94,plain,(
% 1.48/0.56    ~spl3_2 | spl3_5),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f93])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    $false | (~spl3_2 | spl3_5)),
% 1.48/0.56    inference(subsumption_resolution,[],[f92,f46])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    v1_xboole_0(sK2) | ~spl3_2),
% 1.48/0.56    inference(avatar_component_clause,[],[f45])).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    spl3_2 <=> v1_xboole_0(sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.48/0.56  fof(f92,plain,(
% 1.48/0.56    ~v1_xboole_0(sK2) | spl3_5),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f91])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_5),
% 1.48/0.56    inference(superposition,[],[f76,f33])).
% 1.48/0.56  fof(f33,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k10_relat_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(superposition,[],[f22,f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,plain,(
% 1.48/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f5])).
% 1.48/0.56  fof(f5,axiom,(
% 1.48/0.56    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.48/0.56  fof(f76,plain,(
% 1.48/0.56    ~v1_xboole_0(k10_relat_1(sK2,sK1)) | spl3_5),
% 1.48/0.56    inference(avatar_component_clause,[],[f75])).
% 1.48/0.56  fof(f75,plain,(
% 1.48/0.56    spl3_5 <=> v1_xboole_0(k10_relat_1(sK2,sK1))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.48/0.56  fof(f89,plain,(
% 1.48/0.56    ~spl3_2 | spl3_4),
% 1.48/0.56    inference(avatar_contradiction_clause,[],[f88])).
% 1.48/0.56  fof(f88,plain,(
% 1.48/0.56    $false | (~spl3_2 | spl3_4)),
% 1.48/0.56    inference(subsumption_resolution,[],[f87,f46])).
% 1.48/0.56  fof(f87,plain,(
% 1.48/0.56    ~v1_xboole_0(sK2) | spl3_4),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f86])).
% 1.48/0.56  fof(f86,plain,(
% 1.48/0.56    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl3_4),
% 1.48/0.56    inference(superposition,[],[f83,f33])).
% 1.48/0.56  fof(f83,plain,(
% 1.48/0.56    ~v1_xboole_0(k10_relat_1(sK2,sK1)) | spl3_4),
% 1.48/0.56    inference(subsumption_resolution,[],[f80,f35])).
% 1.48/0.56  fof(f35,plain,(
% 1.48/0.56    ( ! [X0] : (m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(superposition,[],[f31,f23])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.48/0.56    inference(backward_demodulation,[],[f19,f30])).
% 1.48/0.56  fof(f30,plain,(
% 1.48/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.48/0.56    inference(equality_resolution,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f18])).
% 1.48/0.56  fof(f18,plain,(
% 1.48/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.56    inference(flattening,[],[f17])).
% 1.48/0.56  fof(f17,plain,(
% 1.48/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.48/0.56    inference(nnf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.56  fof(f19,plain,(
% 1.48/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 1.48/0.56    inference(cnf_transformation,[],[f16])).
% 1.48/0.56  fof(f16,plain,(
% 1.48/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 1.48/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 1.48/0.56  fof(f15,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 1.48/0.56    introduced(choice_axiom,[])).
% 1.48/0.56  fof(f11,plain,(
% 1.48/0.56    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 1.48/0.56    inference(ennf_transformation,[],[f10])).
% 1.48/0.56  fof(f10,plain,(
% 1.48/0.56    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.48/0.56    inference(pure_predicate_removal,[],[f9])).
% 1.48/0.56  fof(f9,plain,(
% 1.48/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.48/0.56    inference(pure_predicate_removal,[],[f8])).
% 1.48/0.56  fof(f8,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.48/0.56    inference(negated_conjecture,[],[f7])).
% 1.48/0.56  fof(f7,conjecture,(
% 1.48/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_2)).
% 1.48/0.56  fof(f80,plain,(
% 1.48/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k10_relat_1(sK2,sK1))) | ~v1_xboole_0(k10_relat_1(sK2,sK1)) | spl3_4),
% 1.48/0.56    inference(superposition,[],[f73,f37])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = X0 | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(superposition,[],[f30,f23])).
% 1.48/0.56  fof(f73,plain,(
% 1.48/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0))) | spl3_4),
% 1.48/0.56    inference(avatar_component_clause,[],[f72])).
% 1.48/0.56  fof(f72,plain,(
% 1.48/0.56    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0)))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.48/0.56  fof(f77,plain,(
% 1.48/0.56    ~spl3_4 | ~spl3_5),
% 1.48/0.56    inference(avatar_split_clause,[],[f69,f75,f72])).
% 1.48/0.56  fof(f69,plain,(
% 1.48/0.56    ~v1_xboole_0(k10_relat_1(sK2,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k10_relat_1(sK2,sK1),sK0)))),
% 1.48/0.56    inference(equality_resolution,[],[f57])).
% 1.48/0.56  fof(f57,plain,(
% 1.48/0.56    ( ! [X0] : (k10_relat_1(sK2,sK1) != X0 | ~v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) )),
% 1.48/0.56    inference(superposition,[],[f34,f28])).
% 1.48/0.56  fof(f28,plain,(
% 1.48/0.56    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,plain,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f6])).
% 1.48/0.56  fof(f6,axiom,(
% 1.48/0.56    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ( ! [X0] : (k8_relset_1(X0,sK0,sK2,sK1) != X0 | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(superposition,[],[f20,f23])).
% 1.48/0.56  fof(f20,plain,(
% 1.48/0.56    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f16])).
% 1.48/0.56  fof(f51,plain,(
% 1.48/0.56    spl3_3 | spl3_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f40,f45,f49])).
% 1.48/0.56  fof(f40,plain,(
% 1.48/0.56    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(duplicate_literal_removal,[],[f39])).
% 1.48/0.56  fof(f39,plain,(
% 1.48/0.56    ( ! [X0] : (v1_xboole_0(sK2) | ~v1_xboole_0(X0) | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(resolution,[],[f24,f35])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,plain,(
% 1.48/0.56    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f4])).
% 1.48/0.56  fof(f4,axiom,(
% 1.48/0.56    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (10049)------------------------------
% 1.48/0.56  % (10049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (10049)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (10049)Memory used [KB]: 10618
% 1.48/0.56  % (10049)Time elapsed: 0.124 s
% 1.48/0.56  % (10049)------------------------------
% 1.48/0.56  % (10049)------------------------------
% 1.48/0.56  % (10046)Success in time 0.199 s
%------------------------------------------------------------------------------
