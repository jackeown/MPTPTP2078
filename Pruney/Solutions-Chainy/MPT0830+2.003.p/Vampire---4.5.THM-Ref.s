%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:56:45 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 104 expanded)
%              Number of leaves         :   15 (  29 expanded)
%              Depth                    :   10
%              Number of atoms          :  154 ( 220 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f98,f102,f105,f283])).

fof(f283,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl4_6 ),
    inference(resolution,[],[f279,f56])).

fof(f56,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f36,f26])).

fof(f26,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
       => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f279,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_6 ),
    inference(resolution,[],[f273,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f273,plain,
    ( ~ r1_tarski(k7_relat_1(sK3,sK1),sK3)
    | spl4_6 ),
    inference(resolution,[],[f136,f26])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
        | ~ r1_tarski(k7_relat_1(sK3,sK1),X0) )
    | spl4_6 ),
    inference(resolution,[],[f73,f101])).

fof(f101,plain,
    ( ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_6
  <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f73,plain,(
    ! [X6,X8,X7,X5] :
      ( v5_relat_1(X5,X8)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ r1_tarski(X5,X6) ) ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

fof(f105,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl4_5 ),
    inference(resolution,[],[f103,f56])).

fof(f103,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(resolution,[],[f93,f30])).

% (23917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f93,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_5
  <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f102,plain,
    ( ~ spl4_6
    | ~ spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f96,f89,f86,f100])).

fof(f86,plain,
    ( spl4_3
  <=> v1_relat_1(k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,
    ( spl4_4
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f96,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | ~ v5_relat_1(k7_relat_1(sK3,sK1),sK2)
    | spl4_4 ),
    inference(resolution,[],[f90,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f90,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f98,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f97])).

% (23915)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f97,plain,
    ( $false
    | spl4_3 ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_3 ),
    inference(resolution,[],[f87,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f44,f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f87,plain,
    ( ~ v1_relat_1(k7_relat_1(sK3,sK1))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f94,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f84,f92,f89,f86])).

fof(f84,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)
    | ~ r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)
    | ~ v1_relat_1(k7_relat_1(sK3,sK1)) ),
    inference(resolution,[],[f35,f70])).

fof(f70,plain,(
    ~ m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(backward_demodulation,[],[f27,f67])).

fof(f67,plain,(
    ! [X0] : k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f38,f26])).

% (23920)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f27,plain,(
    ~ m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : run_vampire %s %d
% 0.11/0.31  % Computer   : n019.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % WCLimit    : 600
% 0.11/0.31  % DateTime   : Tue Dec  1 18:25:22 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.18/0.41  % (23916)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.18/0.41  % (23912)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.18/0.41  % (23931)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.18/0.41  % (23914)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.18/0.42  % (23928)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.18/0.42  % (23933)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.18/0.43  % (23923)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.18/0.43  % (23925)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.18/0.43  % (23919)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.44  % (23923)Refutation not found, incomplete strategy% (23923)------------------------------
% 0.18/0.44  % (23923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.44  % (23923)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.44  
% 0.18/0.44  % (23923)Memory used [KB]: 10490
% 0.18/0.44  % (23923)Time elapsed: 0.087 s
% 0.18/0.44  % (23923)------------------------------
% 0.18/0.44  % (23923)------------------------------
% 0.18/0.45  % (23925)Refutation found. Thanks to Tanya!
% 0.18/0.45  % SZS status Theorem for theBenchmark
% 0.18/0.45  % (23919)Refutation not found, incomplete strategy% (23919)------------------------------
% 0.18/0.45  % (23919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.45  % (23919)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.45  
% 0.18/0.45  % (23919)Memory used [KB]: 6012
% 0.18/0.45  % (23919)Time elapsed: 0.094 s
% 0.18/0.45  % (23919)------------------------------
% 0.18/0.45  % (23919)------------------------------
% 0.18/0.45  % SZS output start Proof for theBenchmark
% 0.18/0.45  fof(f284,plain,(
% 0.18/0.45    $false),
% 0.18/0.45    inference(avatar_sat_refutation,[],[f94,f98,f102,f105,f283])).
% 0.18/0.47  fof(f283,plain,(
% 0.18/0.47    spl4_6),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f282])).
% 0.18/0.47  fof(f282,plain,(
% 0.18/0.47    $false | spl4_6),
% 0.18/0.47    inference(resolution,[],[f279,f56])).
% 0.18/0.47  fof(f56,plain,(
% 0.18/0.47    v1_relat_1(sK3)),
% 0.18/0.47    inference(resolution,[],[f36,f26])).
% 0.18/0.47  fof(f26,plain,(
% 0.18/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.18/0.47    inference(cnf_transformation,[],[f14])).
% 0.18/0.47  fof(f14,plain,(
% 0.18/0.47    ? [X0,X1,X2,X3] : (~m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.18/0.47    inference(ennf_transformation,[],[f12])).
% 0.18/0.47  fof(f12,negated_conjecture,(
% 0.18/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.18/0.47    inference(negated_conjecture,[],[f11])).
% 0.18/0.47  fof(f11,conjecture,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => m1_subset_1(k5_relset_1(X0,X2,X3,X1),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).
% 0.18/0.47  fof(f36,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f21])).
% 0.18/0.47  fof(f21,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f6])).
% 0.18/0.47  fof(f6,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.47  fof(f279,plain,(
% 0.18/0.47    ~v1_relat_1(sK3) | spl4_6),
% 0.18/0.47    inference(resolution,[],[f273,f29])).
% 0.18/0.47  fof(f29,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f16])).
% 0.18/0.47  fof(f16,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f5])).
% 0.18/0.47  fof(f5,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.18/0.47  fof(f273,plain,(
% 0.18/0.47    ~r1_tarski(k7_relat_1(sK3,sK1),sK3) | spl4_6),
% 0.18/0.47    inference(resolution,[],[f136,f26])).
% 0.18/0.47  fof(f136,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) | ~r1_tarski(k7_relat_1(sK3,sK1),X0)) ) | spl4_6),
% 0.18/0.47    inference(resolution,[],[f73,f101])).
% 0.18/0.47  fof(f101,plain,(
% 0.18/0.47    ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_6),
% 0.18/0.47    inference(avatar_component_clause,[],[f100])).
% 0.18/0.47  fof(f100,plain,(
% 0.18/0.47    spl4_6 <=> v5_relat_1(k7_relat_1(sK3,sK1),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.18/0.47  fof(f73,plain,(
% 0.18/0.47    ( ! [X6,X8,X7,X5] : (v5_relat_1(X5,X8) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~r1_tarski(X5,X6)) )),
% 0.18/0.47    inference(resolution,[],[f39,f37])).
% 0.18/0.47  fof(f37,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f22])).
% 0.18/0.47  fof(f22,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f13])).
% 0.18/0.47  fof(f13,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.18/0.47    inference(pure_predicate_removal,[],[f7])).
% 0.18/0.47  fof(f7,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.47  fof(f39,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.18/0.47    inference(cnf_transformation,[],[f25])).
% 0.18/0.47  fof(f25,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.18/0.47    inference(flattening,[],[f24])).
% 0.18/0.47  fof(f24,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.18/0.47    inference(ennf_transformation,[],[f10])).
% 0.18/0.47  fof(f10,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).
% 0.18/0.47  fof(f105,plain,(
% 0.18/0.47    spl4_5),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f104])).
% 0.18/0.47  fof(f104,plain,(
% 0.18/0.47    $false | spl4_5),
% 0.18/0.47    inference(resolution,[],[f103,f56])).
% 0.18/0.47  fof(f103,plain,(
% 0.18/0.47    ~v1_relat_1(sK3) | spl4_5),
% 0.18/0.47    inference(resolution,[],[f93,f30])).
% 0.18/0.47  % (23917)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.18/0.47  fof(f30,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f17])).
% 0.18/0.47  fof(f17,plain,(
% 0.18/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f4])).
% 0.18/0.47  fof(f4,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 0.18/0.47  fof(f93,plain,(
% 0.18/0.47    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | spl4_5),
% 0.18/0.47    inference(avatar_component_clause,[],[f92])).
% 0.18/0.47  fof(f92,plain,(
% 0.18/0.47    spl4_5 <=> r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.18/0.47  fof(f102,plain,(
% 0.18/0.47    ~spl4_6 | ~spl4_3 | spl4_4),
% 0.18/0.47    inference(avatar_split_clause,[],[f96,f89,f86,f100])).
% 0.18/0.47  fof(f86,plain,(
% 0.18/0.47    spl4_3 <=> v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.18/0.47  fof(f89,plain,(
% 0.18/0.47    spl4_4 <=> r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2)),
% 0.18/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.18/0.47  fof(f96,plain,(
% 0.18/0.47    ~v1_relat_1(k7_relat_1(sK3,sK1)) | ~v5_relat_1(k7_relat_1(sK3,sK1),sK2) | spl4_4),
% 0.18/0.47    inference(resolution,[],[f90,f32])).
% 0.18/0.47  fof(f32,plain,(
% 0.18/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f18])).
% 0.18/0.47  fof(f18,plain,(
% 0.18/0.47    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.18/0.47    inference(ennf_transformation,[],[f3])).
% 0.18/0.47  fof(f3,axiom,(
% 0.18/0.47    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.18/0.47  fof(f90,plain,(
% 0.18/0.47    ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | spl4_4),
% 0.18/0.47    inference(avatar_component_clause,[],[f89])).
% 0.18/0.47  fof(f98,plain,(
% 0.18/0.47    spl4_3),
% 0.18/0.47    inference(avatar_contradiction_clause,[],[f97])).
% 0.18/0.47  % (23915)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.18/0.47  fof(f97,plain,(
% 0.18/0.47    $false | spl4_3),
% 0.18/0.47    inference(resolution,[],[f95,f56])).
% 0.18/0.47  fof(f95,plain,(
% 0.18/0.47    ~v1_relat_1(sK3) | spl4_3),
% 0.18/0.47    inference(resolution,[],[f87,f55])).
% 0.18/0.47  fof(f55,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(duplicate_literal_removal,[],[f52])).
% 0.18/0.47  fof(f52,plain,(
% 0.18/0.47    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(resolution,[],[f44,f29])).
% 0.18/0.47  fof(f44,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.18/0.47    inference(resolution,[],[f28,f33])).
% 0.18/0.47  fof(f33,plain,(
% 0.18/0.47    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f1])).
% 0.18/0.47  fof(f1,axiom,(
% 0.18/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.18/0.47  fof(f28,plain,(
% 0.18/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f15])).
% 0.18/0.47  fof(f15,plain,(
% 0.18/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.18/0.47    inference(ennf_transformation,[],[f2])).
% 0.18/0.47  fof(f2,axiom,(
% 0.18/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.18/0.47  fof(f87,plain,(
% 0.18/0.47    ~v1_relat_1(k7_relat_1(sK3,sK1)) | spl4_3),
% 0.18/0.47    inference(avatar_component_clause,[],[f86])).
% 0.18/0.47  fof(f94,plain,(
% 0.18/0.47    ~spl4_3 | ~spl4_4 | ~spl4_5),
% 0.18/0.47    inference(avatar_split_clause,[],[f84,f92,f89,f86])).
% 0.18/0.47  fof(f84,plain,(
% 0.18/0.47    ~r1_tarski(k1_relat_1(k7_relat_1(sK3,sK1)),sK1) | ~r1_tarski(k2_relat_1(k7_relat_1(sK3,sK1)),sK2) | ~v1_relat_1(k7_relat_1(sK3,sK1))),
% 0.18/0.47    inference(resolution,[],[f35,f70])).
% 0.18/0.47  fof(f70,plain,(
% 0.18/0.47    ~m1_subset_1(k7_relat_1(sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.18/0.47    inference(backward_demodulation,[],[f27,f67])).
% 0.18/0.47  fof(f67,plain,(
% 0.18/0.47    ( ! [X0] : (k5_relset_1(sK0,sK2,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.18/0.47    inference(resolution,[],[f38,f26])).
% 0.18/0.47  % (23920)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.18/0.47  fof(f38,plain,(
% 0.18/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f23])).
% 0.18/0.47  fof(f23,plain,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.47    inference(ennf_transformation,[],[f8])).
% 0.18/0.47  fof(f8,axiom,(
% 0.18/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.18/0.47  fof(f27,plain,(
% 0.18/0.47    ~m1_subset_1(k5_relset_1(sK0,sK2,sK3,sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.18/0.47    inference(cnf_transformation,[],[f14])).
% 0.18/0.47  fof(f35,plain,(
% 0.18/0.47    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~r1_tarski(k2_relat_1(X2),X1) | ~v1_relat_1(X2)) )),
% 0.18/0.47    inference(cnf_transformation,[],[f20])).
% 0.18/0.47  fof(f20,plain,(
% 0.18/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(flattening,[],[f19])).
% 0.18/0.47  fof(f19,plain,(
% 0.18/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.18/0.47    inference(ennf_transformation,[],[f9])).
% 0.18/0.47  fof(f9,axiom,(
% 0.18/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.18/0.47  % SZS output end Proof for theBenchmark
% 0.18/0.47  % (23925)------------------------------
% 0.18/0.47  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (23925)Termination reason: Refutation
% 0.18/0.47  
% 0.18/0.47  % (23925)Memory used [KB]: 10874
% 0.18/0.47  % (23925)Time elapsed: 0.098 s
% 0.18/0.47  % (23925)------------------------------
% 0.18/0.47  % (23925)------------------------------
% 0.18/0.47  % (23920)Refutation not found, incomplete strategy% (23920)------------------------------
% 0.18/0.47  % (23920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.47  % (23920)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.47  
% 0.18/0.47  % (23920)Memory used [KB]: 10490
% 0.18/0.47  % (23920)Time elapsed: 0.078 s
% 0.18/0.47  % (23920)------------------------------
% 0.18/0.47  % (23920)------------------------------
% 0.18/0.47  % (23911)Success in time 0.142 s
%------------------------------------------------------------------------------
