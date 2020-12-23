%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:07 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 291 expanded)
%              Number of leaves         :   37 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  489 (1200 expanded)
%              Number of equality atoms :   86 ( 202 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f559,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f205,f221,f257,f290,f327,f334,f336,f381,f385,f387,f414,f424,f428,f446,f491,f510,f517,f548,f552,f558])).

fof(f558,plain,(
    spl6_44 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | spl6_44 ),
    inference(subsumption_resolution,[],[f107,f547])).

fof(f547,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | spl6_44 ),
    inference(avatar_component_clause,[],[f545])).

% (15580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (15573)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% (15561)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% (15567)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (15571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% (15584)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% (15571)Refutation not found, incomplete strategy% (15571)------------------------------
% (15571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15571)Termination reason: Refutation not found, incomplete strategy

% (15571)Memory used [KB]: 10746
% (15571)Time elapsed: 0.135 s
% (15571)------------------------------
% (15571)------------------------------
% (15565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% (15576)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% (15577)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% (15572)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (15581)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (15583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% (15564)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f545,plain,
    ( spl6_44
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f107,plain,(
    v5_relat_1(sK2,sK1) ),
    inference(resolution,[],[f66,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ~ v2_funct_1(X2)
      & ? [X3] :
          ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ~ ( ~ v2_funct_1(X2)
            & ? [X3] :
                ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & k1_xboole_0 != X1 ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ~ ( ~ v2_funct_1(X2)
          & ? [X3] :
              ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f552,plain,(
    spl6_41 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | spl6_41 ),
    inference(unit_resulting_resolution,[],[f78,f532])).

fof(f532,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_41 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl6_41
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f47,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f548,plain,
    ( spl6_30
    | ~ spl6_26
    | ~ spl6_27
    | ~ spl6_19
    | ~ spl6_18
    | ~ spl6_41
    | ~ spl6_44
    | ~ spl6_10
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f543,f497,f201,f545,f530,f308,f312,f368,f364,f403])).

fof(f403,plain,
    ( spl6_30
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f364,plain,
    ( spl6_26
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f368,plain,
    ( spl6_27
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f312,plain,
    ( spl6_19
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f308,plain,
    ( spl6_18
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f201,plain,
    ( spl6_10
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f497,plain,
    ( spl6_39
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f543,plain,
    ( ~ v5_relat_1(sK2,sK1)
    | ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK2)
    | ~ spl6_10
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f527,f203])).

fof(f203,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f527,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK2)
    | ~ v5_relat_1(sK2,k1_relat_1(sK3))
    | ~ spl6_39 ),
    inference(superposition,[],[f146,f499])).

fof(f499,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f497])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1)
      | ~ v5_relat_1(X1,k1_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f56,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_funct_1(X1)
          | ~ r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => v2_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).

fof(f517,plain,
    ( ~ spl6_19
    | ~ spl6_9
    | ~ spl6_27
    | ~ spl6_11
    | spl6_39
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f514,f488,f497,f211,f368,f197,f312])).

fof(f197,plain,
    ( spl6_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f211,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f488,plain,
    ( spl6_37
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f514,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_37 ),
    inference(superposition,[],[f75,f490])).

fof(f490,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f488])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f510,plain,(
    spl6_36 ),
    inference(avatar_contradiction_clause,[],[f507])).

fof(f507,plain,
    ( $false
    | spl6_36 ),
    inference(unit_resulting_resolution,[],[f42,f38,f40,f44,f486,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f486,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_36 ),
    inference(avatar_component_clause,[],[f484])).

fof(f484,plain,
    ( spl6_36
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f491,plain,
    ( ~ spl6_36
    | spl6_37 ),
    inference(avatar_split_clause,[],[f481,f488,f484])).

fof(f481,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f187,f41])).

fof(f41,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f187,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f74,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f446,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | spl6_11 ),
    inference(subsumption_resolution,[],[f44,f213])).

fof(f213,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f211])).

fof(f428,plain,(
    ~ spl6_32 ),
    inference(avatar_contradiction_clause,[],[f425])).

fof(f425,plain,
    ( $false
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f88,f413])).

fof(f413,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl6_32
  <=> r2_hidden(sK4(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f88,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f57,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f57,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f424,plain,(
    ~ spl6_30 ),
    inference(avatar_contradiction_clause,[],[f423])).

fof(f423,plain,
    ( $false
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f46,f405])).

fof(f405,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f403])).

fof(f46,plain,(
    ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f414,plain,
    ( ~ spl6_18
    | spl6_30
    | ~ spl6_19
    | spl6_32
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f397,f324,f411,f312,f403,f308])).

fof(f324,plain,
    ( spl6_22
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f397,plain,
    ( r2_hidden(sK4(sK2),k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_22 ),
    inference(superposition,[],[f53,f326])).

fof(f326,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f324])).

fof(f53,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( ! [X1] :
            ( ? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2)
            | ~ r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ! [X1] :
            ~ ( ! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2)
              & r2_hidden(X1,k2_relat_1(X0)) )
      <=> v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).

fof(f387,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl6_27 ),
    inference(subsumption_resolution,[],[f38,f370])).

fof(f370,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f368])).

fof(f385,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f382])).

fof(f382,plain,
    ( $false
    | spl6_26 ),
    inference(subsumption_resolution,[],[f92,f366])).

fof(f366,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f364])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f63,f40])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f381,plain,
    ( ~ spl6_3
    | spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f376,f166,f162,f158])).

fof(f158,plain,
    ( spl6_3
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f162,plain,
    ( spl6_4
  <=> sK1 = k1_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f166,plain,
    ( spl6_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f376,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f40,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f336,plain,(
    spl6_19 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl6_19 ),
    inference(subsumption_resolution,[],[f42,f314])).

fof(f314,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f312])).

fof(f334,plain,(
    spl6_18 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl6_18 ),
    inference(subsumption_resolution,[],[f93,f310])).

fof(f310,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f308])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f44])).

fof(f327,plain,
    ( ~ spl6_18
    | spl6_22
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f300,f254,f324,f308])).

fof(f254,plain,
    ( spl6_16
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f300,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(trivial_inequality_removal,[],[f299])).

fof(f299,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(superposition,[],[f52,f256])).

fof(f256,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f254])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f290,plain,
    ( ~ spl6_5
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | ~ spl6_5
    | spl6_15 ),
    inference(subsumption_resolution,[],[f231,f252])).

fof(f252,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl6_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f231,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f225,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f225,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_5 ),
    inference(superposition,[],[f44,f168])).

fof(f168,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f257,plain,
    ( ~ spl6_15
    | spl6_16
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f248,f166,f254,f250])).

fof(f248,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_5 ),
    inference(resolution,[],[f224,f133])).

fof(f133,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,k1_xboole_0,X2)
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(duplicate_literal_removal,[],[f132])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2) ) ),
    inference(forward_demodulation,[],[f130,f80])).

fof(f130,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k1_relat_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X3,k1_xboole_0,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) ) ),
    inference(superposition,[],[f129,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f129,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f224,plain,
    ( v1_funct_2(sK2,k1_xboole_0,sK1)
    | ~ spl6_5 ),
    inference(superposition,[],[f43,f168])).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f221,plain,(
    spl6_9 ),
    inference(avatar_contradiction_clause,[],[f220])).

fof(f220,plain,
    ( $false
    | spl6_9 ),
    inference(subsumption_resolution,[],[f40,f199])).

fof(f199,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f197])).

fof(f205,plain,
    ( ~ spl6_9
    | spl6_10
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f194,f162,f201,f197])).

fof(f194,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_4 ),
    inference(superposition,[],[f64,f164])).

fof(f164,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f184,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f39,f160])).

fof(f160,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:47:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.21/0.50  % (15578)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.50  % (15562)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (15557)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (15568)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (15579)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (15558)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (15566)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (15560)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (15574)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.52  % (15559)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (15569)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (15555)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (15575)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (15563)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.53  % (15570)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.53  % (15556)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.39/0.53  % (15568)Refutation found. Thanks to Tanya!
% 1.39/0.53  % SZS status Theorem for theBenchmark
% 1.39/0.53  % SZS output start Proof for theBenchmark
% 1.39/0.53  fof(f559,plain,(
% 1.39/0.53    $false),
% 1.39/0.53    inference(avatar_sat_refutation,[],[f184,f205,f221,f257,f290,f327,f334,f336,f381,f385,f387,f414,f424,f428,f446,f491,f510,f517,f548,f552,f558])).
% 1.39/0.53  fof(f558,plain,(
% 1.39/0.53    spl6_44),
% 1.39/0.53    inference(avatar_contradiction_clause,[],[f553])).
% 1.39/0.53  fof(f553,plain,(
% 1.39/0.53    $false | spl6_44),
% 1.39/0.53    inference(subsumption_resolution,[],[f107,f547])).
% 1.39/0.53  fof(f547,plain,(
% 1.39/0.53    ~v5_relat_1(sK2,sK1) | spl6_44),
% 1.39/0.53    inference(avatar_component_clause,[],[f545])).
% 1.39/0.53  % (15580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.39/0.54  % (15573)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.39/0.54  % (15561)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.54  % (15567)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.39/0.54  % (15571)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.54  % (15584)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.39/0.54  % (15571)Refutation not found, incomplete strategy% (15571)------------------------------
% 1.39/0.54  % (15571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (15571)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.54  
% 1.39/0.54  % (15571)Memory used [KB]: 10746
% 1.39/0.54  % (15571)Time elapsed: 0.135 s
% 1.39/0.54  % (15571)------------------------------
% 1.39/0.54  % (15571)------------------------------
% 1.39/0.54  % (15565)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.49/0.54  % (15576)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.49/0.54  % (15577)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.49/0.55  % (15572)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.55  % (15581)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.49/0.55  % (15583)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.49/0.55  % (15564)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.55  fof(f545,plain,(
% 1.49/0.55    spl6_44 <=> v5_relat_1(sK2,sK1)),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 1.49/0.55  fof(f107,plain,(
% 1.49/0.55    v5_relat_1(sK2,sK1)),
% 1.49/0.55    inference(resolution,[],[f66,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.55    inference(cnf_transformation,[],[f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ? [X0,X1,X2] : (~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.49/0.55    inference(flattening,[],[f19])).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ? [X0,X1,X2] : ((~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.49/0.55    inference(ennf_transformation,[],[f18])).
% 1.49/0.55  fof(f18,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.49/0.55    inference(negated_conjecture,[],[f17])).
% 1.49/0.55  fof(f17,conjecture,(
% 1.49/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ~(~v2_funct_1(X2) & ? [X3] : (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & k1_xboole_0 != X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_funct_2)).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f29])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.55    inference(ennf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.49/0.55  fof(f552,plain,(
% 1.49/0.55    spl6_41),
% 1.49/0.55    inference(avatar_contradiction_clause,[],[f549])).
% 1.49/0.55  fof(f549,plain,(
% 1.49/0.55    $false | spl6_41),
% 1.49/0.55    inference(unit_resulting_resolution,[],[f78,f532])).
% 1.49/0.55  fof(f532,plain,(
% 1.49/0.55    ~v2_funct_1(k6_partfun1(sK0)) | spl6_41),
% 1.49/0.55    inference(avatar_component_clause,[],[f530])).
% 1.49/0.55  fof(f530,plain,(
% 1.49/0.55    spl6_41 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.49/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 1.49/0.55  fof(f78,plain,(
% 1.49/0.55    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f47,f48])).
% 1.49/0.55  fof(f48,plain,(
% 1.49/0.55    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f16])).
% 1.49/0.56  fof(f16,axiom,(
% 1.49/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.49/0.56  fof(f47,plain,(
% 1.49/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f7])).
% 1.49/0.56  fof(f7,axiom,(
% 1.49/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.49/0.56  fof(f548,plain,(
% 1.49/0.56    spl6_30 | ~spl6_26 | ~spl6_27 | ~spl6_19 | ~spl6_18 | ~spl6_41 | ~spl6_44 | ~spl6_10 | ~spl6_39),
% 1.49/0.56    inference(avatar_split_clause,[],[f543,f497,f201,f545,f530,f308,f312,f368,f364,f403])).
% 1.49/0.56  fof(f403,plain,(
% 1.49/0.56    spl6_30 <=> v2_funct_1(sK2)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 1.49/0.56  fof(f364,plain,(
% 1.49/0.56    spl6_26 <=> v1_relat_1(sK3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 1.49/0.56  fof(f368,plain,(
% 1.49/0.56    spl6_27 <=> v1_funct_1(sK3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.49/0.56  fof(f312,plain,(
% 1.49/0.56    spl6_19 <=> v1_funct_1(sK2)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 1.49/0.56  fof(f308,plain,(
% 1.49/0.56    spl6_18 <=> v1_relat_1(sK2)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 1.49/0.56  fof(f201,plain,(
% 1.49/0.56    spl6_10 <=> sK1 = k1_relat_1(sK3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.49/0.56  fof(f497,plain,(
% 1.49/0.56    spl6_39 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 1.49/0.56  fof(f543,plain,(
% 1.49/0.56    ~v5_relat_1(sK2,sK1) | ~v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v2_funct_1(sK2) | (~spl6_10 | ~spl6_39)),
% 1.49/0.56    inference(forward_demodulation,[],[f527,f203])).
% 1.49/0.56  fof(f203,plain,(
% 1.49/0.56    sK1 = k1_relat_1(sK3) | ~spl6_10),
% 1.49/0.56    inference(avatar_component_clause,[],[f201])).
% 1.49/0.56  fof(f527,plain,(
% 1.49/0.56    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | v2_funct_1(sK2) | ~v5_relat_1(sK2,k1_relat_1(sK3)) | ~spl6_39),
% 1.49/0.56    inference(superposition,[],[f146,f499])).
% 1.49/0.56  fof(f499,plain,(
% 1.49/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_39),
% 1.49/0.56    inference(avatar_component_clause,[],[f497])).
% 1.49/0.56  fof(f146,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X1) | ~v5_relat_1(X1,k1_relat_1(X0))) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f145])).
% 1.49/0.56  fof(f145,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,k1_relat_1(X0))) )),
% 1.49/0.56    inference(resolution,[],[f56,f59])).
% 1.49/0.56  fof(f59,plain,(
% 1.49/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f26])).
% 1.49/0.56  fof(f26,plain,(
% 1.49/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.49/0.56    inference(ennf_transformation,[],[f3])).
% 1.49/0.56  fof(f3,axiom,(
% 1.49/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.49/0.56  fof(f56,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f25])).
% 1.49/0.56  fof(f25,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : (v2_funct_1(X1) | ~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f24])).
% 1.49/0.56  fof(f24,plain,(
% 1.49/0.56    ! [X0] : (! [X1] : ((v2_funct_1(X1) | (~r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f6])).
% 1.49/0.56  fof(f6,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) & v2_funct_1(k5_relat_1(X1,X0))) => v2_funct_1(X1))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_funct_1)).
% 1.49/0.56  fof(f517,plain,(
% 1.49/0.56    ~spl6_19 | ~spl6_9 | ~spl6_27 | ~spl6_11 | spl6_39 | ~spl6_37),
% 1.49/0.56    inference(avatar_split_clause,[],[f514,f488,f497,f211,f368,f197,f312])).
% 1.49/0.56  fof(f197,plain,(
% 1.49/0.56    spl6_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.49/0.56  fof(f211,plain,(
% 1.49/0.56    spl6_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.49/0.56  fof(f488,plain,(
% 1.49/0.56    spl6_37 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 1.49/0.56  fof(f514,plain,(
% 1.49/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl6_37),
% 1.49/0.56    inference(superposition,[],[f75,f490])).
% 1.49/0.56  fof(f490,plain,(
% 1.49/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl6_37),
% 1.49/0.56    inference(avatar_component_clause,[],[f488])).
% 1.49/0.56  fof(f75,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f35])).
% 1.49/0.56  fof(f35,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.49/0.56    inference(flattening,[],[f34])).
% 1.49/0.56  fof(f34,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.49/0.56    inference(ennf_transformation,[],[f15])).
% 1.49/0.56  fof(f15,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.49/0.56  fof(f510,plain,(
% 1.49/0.56    spl6_36),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f507])).
% 1.49/0.56  fof(f507,plain,(
% 1.49/0.56    $false | spl6_36),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f42,f38,f40,f44,f486,f77])).
% 1.49/0.56  fof(f77,plain,(
% 1.49/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f37])).
% 1.49/0.56  fof(f37,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.49/0.56    inference(flattening,[],[f36])).
% 1.49/0.56  fof(f36,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.49/0.56    inference(ennf_transformation,[],[f13])).
% 1.49/0.56  fof(f13,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.49/0.56  fof(f486,plain,(
% 1.49/0.56    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_36),
% 1.49/0.56    inference(avatar_component_clause,[],[f484])).
% 1.49/0.56  fof(f484,plain,(
% 1.49/0.56    spl6_36 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 1.49/0.56  fof(f40,plain,(
% 1.49/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f38,plain,(
% 1.49/0.56    v1_funct_1(sK3)),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f42,plain,(
% 1.49/0.56    v1_funct_1(sK2)),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f491,plain,(
% 1.49/0.56    ~spl6_36 | spl6_37),
% 1.49/0.56    inference(avatar_split_clause,[],[f481,f488,f484])).
% 1.49/0.56  fof(f481,plain,(
% 1.49/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.49/0.56    inference(resolution,[],[f187,f41])).
% 1.49/0.56  fof(f41,plain,(
% 1.49/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f187,plain,(
% 1.49/0.56    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.49/0.56    inference(resolution,[],[f74,f50])).
% 1.49/0.56  fof(f50,plain,(
% 1.49/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f14])).
% 1.49/0.56  fof(f14,axiom,(
% 1.49/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.49/0.56  fof(f74,plain,(
% 1.49/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f33])).
% 1.49/0.56  fof(f33,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(flattening,[],[f32])).
% 1.49/0.56  fof(f32,plain,(
% 1.49/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.49/0.56    inference(ennf_transformation,[],[f11])).
% 1.49/0.56  fof(f11,axiom,(
% 1.49/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.49/0.56  fof(f446,plain,(
% 1.49/0.56    spl6_11),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f445])).
% 1.49/0.56  fof(f445,plain,(
% 1.49/0.56    $false | spl6_11),
% 1.49/0.56    inference(subsumption_resolution,[],[f44,f213])).
% 1.49/0.56  fof(f213,plain,(
% 1.49/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_11),
% 1.49/0.56    inference(avatar_component_clause,[],[f211])).
% 1.49/0.56  fof(f428,plain,(
% 1.49/0.56    ~spl6_32),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f425])).
% 1.49/0.56  fof(f425,plain,(
% 1.49/0.56    $false | ~spl6_32),
% 1.49/0.56    inference(unit_resulting_resolution,[],[f88,f413])).
% 1.49/0.56  fof(f413,plain,(
% 1.49/0.56    r2_hidden(sK4(sK2),k1_xboole_0) | ~spl6_32),
% 1.49/0.56    inference(avatar_component_clause,[],[f411])).
% 1.49/0.56  fof(f411,plain,(
% 1.49/0.56    spl6_32 <=> r2_hidden(sK4(sK2),k1_xboole_0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 1.49/0.56  fof(f88,plain,(
% 1.49/0.56    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.49/0.56    inference(superposition,[],[f57,f79])).
% 1.49/0.56  fof(f79,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.49/0.56    inference(equality_resolution,[],[f62])).
% 1.49/0.56  fof(f62,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f1,axiom,(
% 1.49/0.56    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.49/0.56  fof(f57,plain,(
% 1.49/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f2])).
% 1.49/0.56  fof(f2,axiom,(
% 1.49/0.56    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 1.49/0.56  fof(f424,plain,(
% 1.49/0.56    ~spl6_30),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f423])).
% 1.49/0.56  fof(f423,plain,(
% 1.49/0.56    $false | ~spl6_30),
% 1.49/0.56    inference(subsumption_resolution,[],[f46,f405])).
% 1.49/0.56  fof(f405,plain,(
% 1.49/0.56    v2_funct_1(sK2) | ~spl6_30),
% 1.49/0.56    inference(avatar_component_clause,[],[f403])).
% 1.49/0.56  fof(f46,plain,(
% 1.49/0.56    ~v2_funct_1(sK2)),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f414,plain,(
% 1.49/0.56    ~spl6_18 | spl6_30 | ~spl6_19 | spl6_32 | ~spl6_22),
% 1.49/0.56    inference(avatar_split_clause,[],[f397,f324,f411,f312,f403,f308])).
% 1.49/0.56  fof(f324,plain,(
% 1.49/0.56    spl6_22 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.49/0.56  fof(f397,plain,(
% 1.49/0.56    r2_hidden(sK4(sK2),k1_xboole_0) | ~v1_funct_1(sK2) | v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl6_22),
% 1.49/0.56    inference(superposition,[],[f53,f326])).
% 1.49/0.56  fof(f326,plain,(
% 1.49/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl6_22),
% 1.49/0.56    inference(avatar_component_clause,[],[f324])).
% 1.49/0.56  fof(f53,plain,(
% 1.49/0.56    ( ! [X0] : (r2_hidden(sK4(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f23])).
% 1.49/0.56  fof(f23,plain,(
% 1.49/0.56    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(flattening,[],[f22])).
% 1.49/0.56  fof(f22,plain,(
% 1.49/0.56    ! [X0] : ((! [X1] : (? [X2] : k10_relat_1(X0,k1_tarski(X1)) = k1_tarski(X2) | ~r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.49/0.56    inference(ennf_transformation,[],[f5])).
% 1.49/0.56  fof(f5,axiom,(
% 1.49/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (! [X1] : ~(! [X2] : k10_relat_1(X0,k1_tarski(X1)) != k1_tarski(X2) & r2_hidden(X1,k2_relat_1(X0))) <=> v2_funct_1(X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_funct_1)).
% 1.49/0.56  fof(f387,plain,(
% 1.49/0.56    spl6_27),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f386])).
% 1.49/0.56  fof(f386,plain,(
% 1.49/0.56    $false | spl6_27),
% 1.49/0.56    inference(subsumption_resolution,[],[f38,f370])).
% 1.49/0.56  fof(f370,plain,(
% 1.49/0.56    ~v1_funct_1(sK3) | spl6_27),
% 1.49/0.56    inference(avatar_component_clause,[],[f368])).
% 1.49/0.56  fof(f385,plain,(
% 1.49/0.56    spl6_26),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f382])).
% 1.49/0.56  fof(f382,plain,(
% 1.49/0.56    $false | spl6_26),
% 1.49/0.56    inference(subsumption_resolution,[],[f92,f366])).
% 1.49/0.56  fof(f366,plain,(
% 1.49/0.56    ~v1_relat_1(sK3) | spl6_26),
% 1.49/0.56    inference(avatar_component_clause,[],[f364])).
% 1.49/0.56  fof(f92,plain,(
% 1.49/0.56    v1_relat_1(sK3)),
% 1.49/0.56    inference(resolution,[],[f63,f40])).
% 1.49/0.56  fof(f63,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f27])).
% 1.49/0.56  fof(f27,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f8])).
% 1.49/0.56  fof(f8,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.49/0.56  fof(f381,plain,(
% 1.49/0.56    ~spl6_3 | spl6_4 | spl6_5),
% 1.49/0.56    inference(avatar_split_clause,[],[f376,f166,f162,f158])).
% 1.49/0.56  fof(f158,plain,(
% 1.49/0.56    spl6_3 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.49/0.56  fof(f162,plain,(
% 1.49/0.56    spl6_4 <=> sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.49/0.56  fof(f166,plain,(
% 1.49/0.56    spl6_5 <=> k1_xboole_0 = sK0),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.49/0.56  fof(f376,plain,(
% 1.49/0.56    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.49/0.56    inference(resolution,[],[f40,f72])).
% 1.49/0.56  fof(f72,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f31,plain,(
% 1.49/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(flattening,[],[f30])).
% 1.49/0.56  fof(f30,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f12])).
% 1.49/0.56  fof(f12,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.49/0.56  fof(f336,plain,(
% 1.49/0.56    spl6_19),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f335])).
% 1.49/0.56  fof(f335,plain,(
% 1.49/0.56    $false | spl6_19),
% 1.49/0.56    inference(subsumption_resolution,[],[f42,f314])).
% 1.49/0.56  fof(f314,plain,(
% 1.49/0.56    ~v1_funct_1(sK2) | spl6_19),
% 1.49/0.56    inference(avatar_component_clause,[],[f312])).
% 1.49/0.56  fof(f334,plain,(
% 1.49/0.56    spl6_18),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f331])).
% 1.49/0.56  fof(f331,plain,(
% 1.49/0.56    $false | spl6_18),
% 1.49/0.56    inference(subsumption_resolution,[],[f93,f310])).
% 1.49/0.56  fof(f310,plain,(
% 1.49/0.56    ~v1_relat_1(sK2) | spl6_18),
% 1.49/0.56    inference(avatar_component_clause,[],[f308])).
% 1.49/0.56  fof(f93,plain,(
% 1.49/0.56    v1_relat_1(sK2)),
% 1.49/0.56    inference(resolution,[],[f63,f44])).
% 1.49/0.56  fof(f327,plain,(
% 1.49/0.56    ~spl6_18 | spl6_22 | ~spl6_16),
% 1.49/0.56    inference(avatar_split_clause,[],[f300,f254,f324,f308])).
% 1.49/0.56  fof(f254,plain,(
% 1.49/0.56    spl6_16 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.49/0.56  fof(f300,plain,(
% 1.49/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl6_16),
% 1.49/0.56    inference(trivial_inequality_removal,[],[f299])).
% 1.49/0.56  fof(f299,plain,(
% 1.49/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl6_16),
% 1.49/0.56    inference(superposition,[],[f52,f256])).
% 1.49/0.56  fof(f256,plain,(
% 1.49/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_16),
% 1.49/0.56    inference(avatar_component_clause,[],[f254])).
% 1.49/0.56  fof(f52,plain,(
% 1.49/0.56    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f21])).
% 1.49/0.56  fof(f21,plain,(
% 1.49/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.49/0.56    inference(ennf_transformation,[],[f4])).
% 1.49/0.56  fof(f4,axiom,(
% 1.49/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 1.49/0.56  fof(f290,plain,(
% 1.49/0.56    ~spl6_5 | spl6_15),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f289])).
% 1.49/0.56  fof(f289,plain,(
% 1.49/0.56    $false | (~spl6_5 | spl6_15)),
% 1.49/0.56    inference(subsumption_resolution,[],[f231,f252])).
% 1.49/0.56  fof(f252,plain,(
% 1.49/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_15),
% 1.49/0.56    inference(avatar_component_clause,[],[f250])).
% 1.49/0.56  fof(f250,plain,(
% 1.49/0.56    spl6_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.49/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.49/0.56  fof(f231,plain,(
% 1.49/0.56    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_5),
% 1.49/0.56    inference(forward_demodulation,[],[f225,f80])).
% 1.49/0.56  fof(f80,plain,(
% 1.49/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f61])).
% 1.49/0.56  fof(f61,plain,(
% 1.49/0.56    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 1.49/0.56    inference(cnf_transformation,[],[f1])).
% 1.49/0.56  fof(f225,plain,(
% 1.49/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | ~spl6_5),
% 1.49/0.56    inference(superposition,[],[f44,f168])).
% 1.49/0.56  fof(f168,plain,(
% 1.49/0.56    k1_xboole_0 = sK0 | ~spl6_5),
% 1.49/0.56    inference(avatar_component_clause,[],[f166])).
% 1.49/0.56  fof(f257,plain,(
% 1.49/0.56    ~spl6_15 | spl6_16 | ~spl6_5),
% 1.49/0.56    inference(avatar_split_clause,[],[f248,f166,f254,f250])).
% 1.49/0.56  fof(f248,plain,(
% 1.49/0.56    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_5),
% 1.49/0.56    inference(resolution,[],[f224,f133])).
% 1.49/0.56  fof(f133,plain,(
% 1.49/0.56    ( ! [X2,X3] : (~v1_funct_2(X3,k1_xboole_0,X2) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))) )),
% 1.49/0.56    inference(duplicate_literal_removal,[],[f132])).
% 1.49/0.56  fof(f132,plain,(
% 1.49/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f130,f80])).
% 1.49/0.56  fof(f130,plain,(
% 1.49/0.56    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) )),
% 1.49/0.56    inference(superposition,[],[f129,f64])).
% 1.49/0.56  fof(f64,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.49/0.56    inference(cnf_transformation,[],[f28])).
% 1.49/0.56  fof(f28,plain,(
% 1.49/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.49/0.56    inference(ennf_transformation,[],[f10])).
% 1.49/0.56  fof(f10,axiom,(
% 1.49/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.49/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.49/0.56  fof(f129,plain,(
% 1.49/0.56    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.49/0.56    inference(forward_demodulation,[],[f81,f80])).
% 1.49/0.56  fof(f81,plain,(
% 1.49/0.56    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.49/0.56    inference(equality_resolution,[],[f70])).
% 1.49/0.56  fof(f70,plain,(
% 1.49/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.49/0.56    inference(cnf_transformation,[],[f31])).
% 1.49/0.56  fof(f224,plain,(
% 1.49/0.56    v1_funct_2(sK2,k1_xboole_0,sK1) | ~spl6_5),
% 1.49/0.56    inference(superposition,[],[f43,f168])).
% 1.49/0.56  fof(f43,plain,(
% 1.49/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  fof(f221,plain,(
% 1.49/0.56    spl6_9),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f220])).
% 1.49/0.56  fof(f220,plain,(
% 1.49/0.56    $false | spl6_9),
% 1.49/0.56    inference(subsumption_resolution,[],[f40,f199])).
% 1.49/0.56  fof(f199,plain,(
% 1.49/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_9),
% 1.49/0.56    inference(avatar_component_clause,[],[f197])).
% 1.49/0.56  fof(f205,plain,(
% 1.49/0.56    ~spl6_9 | spl6_10 | ~spl6_4),
% 1.49/0.56    inference(avatar_split_clause,[],[f194,f162,f201,f197])).
% 1.49/0.56  fof(f194,plain,(
% 1.49/0.56    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_4),
% 1.49/0.56    inference(superposition,[],[f64,f164])).
% 1.49/0.56  fof(f164,plain,(
% 1.49/0.56    sK1 = k1_relset_1(sK1,sK0,sK3) | ~spl6_4),
% 1.49/0.56    inference(avatar_component_clause,[],[f162])).
% 1.49/0.56  fof(f184,plain,(
% 1.49/0.56    spl6_3),
% 1.49/0.56    inference(avatar_contradiction_clause,[],[f183])).
% 1.49/0.56  fof(f183,plain,(
% 1.49/0.56    $false | spl6_3),
% 1.49/0.56    inference(subsumption_resolution,[],[f39,f160])).
% 1.49/0.56  fof(f160,plain,(
% 1.49/0.56    ~v1_funct_2(sK3,sK1,sK0) | spl6_3),
% 1.49/0.56    inference(avatar_component_clause,[],[f158])).
% 1.49/0.56  fof(f39,plain,(
% 1.49/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.49/0.56    inference(cnf_transformation,[],[f20])).
% 1.49/0.56  % SZS output end Proof for theBenchmark
% 1.49/0.56  % (15568)------------------------------
% 1.49/0.56  % (15568)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (15568)Termination reason: Refutation
% 1.49/0.56  
% 1.49/0.56  % (15568)Memory used [KB]: 6524
% 1.49/0.56  % (15568)Time elapsed: 0.136 s
% 1.49/0.56  % (15568)------------------------------
% 1.49/0.56  % (15568)------------------------------
% 1.49/0.56  % (15554)Success in time 0.207 s
%------------------------------------------------------------------------------
