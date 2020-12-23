%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 126 expanded)
%              Number of leaves         :   20 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  194 ( 314 expanded)
%              Number of equality atoms :   54 (  97 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f66,f98,f108,f132])).

fof(f132,plain,
    ( ~ spl4_12
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f130,f96,f59,f55,f47,f106])).

fof(f106,plain,
    ( spl4_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f47,plain,
    ( spl4_1
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f55,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f59,plain,
    ( spl4_4
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f96,plain,
    ( spl4_10
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f130,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f129,f97])).

fof(f97,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f96])).

fof(f129,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f128,f45])).

fof(f45,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f126,f114])).

fof(f114,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f112,f60])).

fof(f60,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f112,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),X0)
    | ~ spl4_3 ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) ),
    inference(global_subsumption,[],[f33,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)
      | ~ v1_relat_1(k6_relat_1(X0)) ) ),
    inference(superposition,[],[f37,f34])).

fof(f34,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f33,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f92,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X0 )
    | ~ spl4_3 ),
    inference(resolution,[],[f91,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).

fof(f91,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f126,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f124,f97])).

fof(f124,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl4_1 ),
    inference(superposition,[],[f48,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f48,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f108,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f100,f96,f64,f106])).

fof(f64,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(superposition,[],[f65,f97])).

fof(f65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f64])).

fof(f98,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f93,f64,f55,f96])).

fof(f93,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f92,f65])).

fof(f66,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f62,f51,f64])).

fof(f51,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f52,f45])).

fof(f52,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f61,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f57,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f55])).

fof(f31,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f53,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
   => ( k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0,X1,X2] :
        ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
          & v1_funct_2(X2,k1_xboole_0,X0)
          & v1_funct_1(X2) )
       => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        & v1_funct_2(X2,k1_xboole_0,X0)
        & v1_funct_1(X2) )
     => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).

fof(f49,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f30,f47])).

fof(f30,plain,(
    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:31:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (31637)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.47  % (31645)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.47  % (31639)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (31637)Refutation not found, incomplete strategy% (31637)------------------------------
% 0.20/0.47  % (31637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (31637)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (31637)Memory used [KB]: 10618
% 0.20/0.47  % (31637)Time elapsed: 0.060 s
% 0.20/0.47  % (31637)------------------------------
% 0.20/0.47  % (31637)------------------------------
% 0.20/0.48  % (31642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (31642)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f49,f53,f57,f61,f66,f98,f108,f132])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ~spl4_12 | spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f130,f96,f59,f55,f47,f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl4_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    spl4_1 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    spl4_4 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    spl4_10 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f129,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f96])).
% 0.20/0.48  fof(f129,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f128,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f127])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f126,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl4_3 | ~spl4_4)),
% 0.20/0.48    inference(forward_demodulation,[],[f112,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f59])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k6_relat_1(k1_xboole_0),X0)) ) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f94,f84])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f33,f82])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(k6_relat_1(X0),X1),X0) | ~v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(superposition,[],[f37,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f92,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X0) ) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f91,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.48    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_mcart_1)).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_3),
% 0.20/0.48    inference(resolution,[],[f42,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f55])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.48  fof(f126,plain,(
% 0.20/0.48    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl4_1 | ~spl4_10)),
% 0.20/0.48    inference(forward_demodulation,[],[f124,f97])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    k1_xboole_0 != k10_relat_1(sK2,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | spl4_1),
% 0.20/0.48    inference(superposition,[],[f48,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) | spl4_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f47])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    spl4_12 | ~spl4_5 | ~spl4_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f100,f96,f64,f106])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.48  fof(f100,plain,(
% 0.20/0.48    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_5 | ~spl4_10)),
% 0.20/0.48    inference(superposition,[],[f65,f97])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f64])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl4_10 | ~spl4_3 | ~spl4_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f93,f64,f55,f96])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | (~spl4_3 | ~spl4_5)),
% 0.20/0.48    inference(resolution,[],[f92,f65])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    spl4_5 | ~spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f62,f51,f64])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    spl4_2 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.20/0.48    inference(forward_demodulation,[],[f52,f45])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | ~spl4_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f51])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl4_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f32,f59])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    spl4_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f31,f55])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    spl4_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f29,f51])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) => (k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (k1_xboole_0 != k8_relset_1(k1_xboole_0,X0,X2,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ~! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(pure_predicate_removal,[],[f12])).
% 0.20/0.48  fof(f12,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    inference(negated_conjecture,[],[f11])).
% 0.20/0.48  fof(f11,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) & v1_funct_2(X2,k1_xboole_0,X0) & v1_funct_1(X2)) => k1_xboole_0 = k8_relset_1(k1_xboole_0,X0,X2,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_funct_2)).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ~spl4_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f30,f47])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    k1_xboole_0 != k8_relset_1(k1_xboole_0,sK0,sK2,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (31642)------------------------------
% 0.20/0.48  % (31642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (31642)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (31642)Memory used [KB]: 10618
% 0.20/0.48  % (31642)Time elapsed: 0.075 s
% 0.20/0.48  % (31642)------------------------------
% 0.20/0.48  % (31642)------------------------------
% 0.20/0.48  % (31635)Success in time 0.129 s
%------------------------------------------------------------------------------
