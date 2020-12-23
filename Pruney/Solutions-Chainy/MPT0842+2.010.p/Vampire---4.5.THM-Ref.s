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
% DateTime   : Thu Dec  3 12:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 128 expanded)
%              Number of leaves         :   12 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  199 ( 524 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f55,f64,f80,f132])).

fof(f132,plain,
    ( ~ spl10_1
    | ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f130,f66])).

fof(f66,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f21,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <~> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) )
                      & m1_subset_1(X4,X0) )
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) )
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ~ v1_xboole_0(X2)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                   => ! [X4] :
                        ( m1_subset_1(X4,X0)
                       => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                        <=> ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X4,X5),X3)
                              & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k8_relset_1(X0,X2,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X4,X5),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).

fof(f130,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl10_1
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f129,f83])).

fof(f83,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f82,f21])).

fof(f82,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl10_1 ),
    inference(superposition,[],[f45,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

% (25026)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f45,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl10_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f129,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ spl10_5 ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ v1_relat_1(sK3)
    | ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ spl10_5 ),
    inference(resolution,[],[f125,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f124,f93])).

fof(f93,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(subsumption_resolution,[],[f92,f66])).

fof(f92,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK9(X2,X3,sK3),sK2)
      | ~ v1_relat_1(sK3)
      | ~ r2_hidden(X2,k10_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f74,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f74,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k4_tarski(X2,X3),sK3)
      | r2_hidden(X3,sK2) ) ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f67,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_zfmisc_1(sK0,sK2))
      | ~ r2_hidden(X0,sK3) ) ),
    inference(resolution,[],[f21,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f124,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK2) )
    | ~ spl10_5 ),
    inference(resolution,[],[f99,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f99,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f95,f66])).

% (25030)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f95,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK9(sK4,X0,sK3),sK1)
        | ~ m1_subset_1(sK9(sK4,X0,sK3),sK2)
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(sK4,k10_relat_1(sK3,X0)) )
    | ~ spl10_5 ),
    inference(resolution,[],[f63,f32])).

fof(f63,plain,
    ( ! [X5] :
        ( ~ r2_hidden(k4_tarski(sK4,X5),sK3)
        | ~ r2_hidden(X5,sK1)
        | ~ m1_subset_1(X5,sK2) )
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl10_5
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,sK2)
        | ~ r2_hidden(X5,sK1)
        | ~ r2_hidden(k4_tarski(sK4,X5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f80,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f77,f49])).

fof(f49,plain,
    ( r2_hidden(sK5,sK1)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl10_2
  <=> r2_hidden(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f77,plain,
    ( ~ r2_hidden(sK5,sK1)
    | spl10_1
    | ~ spl10_3 ),
    inference(resolution,[],[f72,f54])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl10_3
  <=> r2_hidden(k4_tarski(sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X2),X0)
      | r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f71,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1) )
    | spl10_1 ),
    inference(subsumption_resolution,[],[f70,f66])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(sK3))
        | ~ r2_hidden(k4_tarski(sK4,X0),sK3)
        | ~ r2_hidden(X0,sK1)
        | ~ v1_relat_1(sK3) )
    | spl10_1 ),
    inference(resolution,[],[f69,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f68,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl10_1 ),
    inference(superposition,[],[f44,f36])).

fof(f44,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f64,plain,
    ( ~ spl10_1
    | spl10_5 ),
    inference(avatar_split_clause,[],[f16,f62,f43])).

fof(f16,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK2)
      | ~ r2_hidden(k4_tarski(sK4,X5),sK3)
      | ~ r2_hidden(X5,sK1)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f55,plain,
    ( spl10_1
    | spl10_3 ),
    inference(avatar_split_clause,[],[f18,f52,f43])).

fof(f18,plain,
    ( r2_hidden(k4_tarski(sK4,sK5),sK3)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f19,f47,f43])).

fof(f19,plain,
    ( r2_hidden(sK5,sK1)
    | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (25035)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (25021)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (25025)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (25022)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (25024)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (25029)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (25036)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (25028)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (25017)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (25019)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (25020)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (25017)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (25018)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f50,f55,f64,f80,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ~spl10_1 | ~spl10_5),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    $false | (~spl10_1 | ~spl10_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f130,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    v1_relat_1(sK3)),
% 0.21/0.49    inference(resolution,[],[f21,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <~> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))) & m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k8_relset_1(X0,X2,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X4,X5),X3) & m1_subset_1(X5,X2))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_relset_1)).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    ~v1_relat_1(sK3) | (~spl10_1 | ~spl10_5)),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f83])).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f21])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl10_1),
% 0.21/0.49    inference(superposition,[],[f45,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  % (25026)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | ~spl10_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    spl10_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~spl10_5),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f128])).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~spl10_5),
% 0.21/0.49    inference(resolution,[],[f125,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK9(X0,X1,X2),X1) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f92,f66])).
% 0.21/0.49  fof(f92,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(sK9(X2,X3,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(X2,k10_relat_1(sK3,X3))) )),
% 0.21/0.49    inference(resolution,[],[f74,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK9(X0,X1,X2)),X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK3) | r2_hidden(X3,sK2)) )),
% 0.21/0.49    inference(resolution,[],[f67,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK2)) | ~r2_hidden(X0,sK3)) )),
% 0.21/0.49    inference(resolution,[],[f21,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0)) | ~r2_hidden(sK9(sK4,X0,sK3),sK2)) ) | ~spl10_5),
% 0.21/0.49    inference(resolution,[],[f99,f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.21/0.49    inference(subsumption_resolution,[],[f95,f66])).
% 0.21/0.49  % (25030)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(sK9(sK4,X0,sK3),sK1) | ~m1_subset_1(sK9(sK4,X0,sK3),sK2) | ~v1_relat_1(sK3) | ~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | ~spl10_5),
% 0.21/0.49    inference(resolution,[],[f63,f32])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ( ! [X5] : (~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~m1_subset_1(X5,sK2)) ) | ~spl10_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl10_5 <=> ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(X5,sK1) | ~r2_hidden(k4_tarski(sK4,X5),sK3))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl10_1 | ~spl10_2 | ~spl10_3),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f79])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    $false | (spl10_1 | ~spl10_2 | ~spl10_3)),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f49])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | ~spl10_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    spl10_2 <=> r2_hidden(sK5,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    ~r2_hidden(sK5,sK1) | (spl10_1 | ~spl10_3)),
% 0.21/0.49    inference(resolution,[],[f72,f54])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK4,sK5),sK3) | ~spl10_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f52])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl10_3 <=> r2_hidden(k4_tarski(sK4,sK5),sK3)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X3] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,k2_relat_1(X0))) )),
% 0.21/0.49    inference(equality_resolution,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X2),X0) | r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1)) ) | spl10_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f66])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK3)) | ~r2_hidden(k4_tarski(sK4,X0),sK3) | ~r2_hidden(X0,sK1) | ~v1_relat_1(sK3)) ) | spl10_1),
% 0.21/0.49    inference(resolution,[],[f69,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k10_relat_1(X2,X1)) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f69,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | spl10_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f68,f21])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k10_relat_1(sK3,sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl10_1),
% 0.21/0.49    inference(superposition,[],[f44,f36])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1)) | spl10_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f43])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~spl10_1 | spl10_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f16,f62,f43])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ( ! [X5] : (~m1_subset_1(X5,sK2) | ~r2_hidden(k4_tarski(sK4,X5),sK3) | ~r2_hidden(X5,sK1) | ~r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    spl10_1 | spl10_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f18,f52,f43])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK4,sK5),sK3) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl10_1 | spl10_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f19,f47,f43])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    r2_hidden(sK5,sK1) | r2_hidden(sK4,k8_relset_1(sK0,sK2,sK3,sK1))),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (25017)------------------------------
% 0.21/0.49  % (25017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (25017)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (25017)Memory used [KB]: 10618
% 0.21/0.49  % (25017)Time elapsed: 0.077 s
% 0.21/0.49  % (25017)------------------------------
% 0.21/0.49  % (25017)------------------------------
% 0.21/0.49  % (25033)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (25016)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (25023)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (25027)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (25031)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (25034)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (25032)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (25015)Success in time 0.149 s
%------------------------------------------------------------------------------
