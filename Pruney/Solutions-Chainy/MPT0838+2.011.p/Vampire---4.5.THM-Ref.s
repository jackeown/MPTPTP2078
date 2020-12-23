%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:31 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 110 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :  183 ( 302 expanded)
%              Number of equality atoms :   31 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f133,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f69,f80,f98,f103,f112,f115,f128,f132])).

fof(f132,plain,
    ( ~ spl5_5
    | ~ spl5_7
    | spl5_12 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_7
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f68,f79,f127,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f127,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl5_12
  <=> r1_tarski(k2_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f79,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl5_7
  <=> v5_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f68,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl5_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f128,plain,
    ( spl5_8
    | ~ spl5_12
    | spl5_11 ),
    inference(avatar_split_clause,[],[f118,f109,f125,f91])).

fof(f91,plain,
    ( spl5_8
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f109,plain,
    ( spl5_11
  <=> r2_hidden(sK3(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f118,plain,
    ( ~ r1_tarski(k2_relat_1(sK2),sK1)
    | k1_xboole_0 = k2_relat_1(sK2)
    | spl5_11 ),
    inference(resolution,[],[f113,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(k2_relat_1(sK2)),X0)
        | ~ r1_tarski(X0,sK1) )
    | spl5_11 ),
    inference(resolution,[],[f111,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f111,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f109])).

fof(f115,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | spl5_10 ),
    inference(avatar_split_clause,[],[f105,f100,f91,f66])).

fof(f100,plain,
    ( spl5_10
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f105,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_10 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_10 ),
    inference(superposition,[],[f102,f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
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

fof(f102,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f112,plain,
    ( ~ spl5_11
    | spl5_9 ),
    inference(avatar_split_clause,[],[f106,f95,f109])).

fof(f95,plain,
    ( spl5_9
  <=> m1_subset_1(sK3(k2_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f106,plain,
    ( ~ r2_hidden(sK3(k2_relat_1(sK2)),sK1)
    | spl5_9 ),
    inference(resolution,[],[f97,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f97,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f95])).

fof(f103,plain,
    ( ~ spl5_3
    | ~ spl5_10
    | spl5_4 ),
    inference(avatar_split_clause,[],[f70,f58,f100,f53])).

fof(f53,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f58,plain,
    ( spl5_4
  <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f70,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_4 ),
    inference(superposition,[],[f60,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f60,plain,
    ( k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f58])).

fof(f98,plain,
    ( spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f86,f95,f91])).

fof(f86,plain,
    ( ~ m1_subset_1(sK3(k2_relat_1(sK2)),sK1)
    | k1_xboole_0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f85,f30])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(global_subsumption,[],[f24,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK2))
      | ~ m1_subset_1(X0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    inference(superposition,[],[f23,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f23,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k2_relset_1(sK0,sK1,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k2_relset_1(X0,X1,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k1_relset_1(X0,X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,X1)
                       => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                    & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
             => ~ ( ! [X3] :
                      ( m1_subset_1(X3,X1)
                     => ~ r2_hidden(X3,k2_relset_1(X0,X1,X2)) )
                  & k1_xboole_0 != k1_relset_1(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

fof(f24,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f80,plain,
    ( spl5_7
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f63,f53,f77])).

fof(f63,plain,
    ( v5_relat_1(sK2,sK1)
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f55,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f69,plain,
    ( spl5_5
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f64,f53,f66])).

fof(f64,plain,
    ( v1_relat_1(sK2)
    | ~ spl5_3 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f61,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f24,f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:36:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (32366)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.50  % (32349)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.51  % (32366)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f56,f61,f69,f80,f98,f103,f112,f115,f128,f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ~spl5_5 | ~spl5_7 | spl5_12),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    $false | (~spl5_5 | ~spl5_7 | spl5_12)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f68,f79,f127,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK2),sK1) | spl5_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    spl5_12 <=> r1_tarski(k2_relat_1(sK2),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl5_7 <=> v5_relat_1(sK2,sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f66])).
% 0.20/0.51  fof(f66,plain,(
% 0.20/0.51    spl5_5 <=> v1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f128,plain,(
% 0.20/0.51    spl5_8 | ~spl5_12 | spl5_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f118,f109,f125,f91])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl5_8 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl5_11 <=> r2_hidden(sK3(k2_relat_1(sK2)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK2),sK1) | k1_xboole_0 = k2_relat_1(sK2) | spl5_11),
% 0.20/0.51    inference(resolution,[],[f113,f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK3(k2_relat_1(sK2)),X0) | ~r1_tarski(X0,sK1)) ) | spl5_11),
% 0.20/0.51    inference(resolution,[],[f111,f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k2_relat_1(sK2)),sK1) | spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f109])).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~spl5_5 | ~spl5_8 | spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f105,f100,f91,f66])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl5_10 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | spl5_10),
% 0.20/0.51    inference(trivial_inequality_removal,[],[f104])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | spl5_10),
% 0.20/0.51    inference(superposition,[],[f102,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(sK2) | spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ~spl5_11 | spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f106,f95,f109])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl5_9 <=> m1_subset_1(sK3(k2_relat_1(sK2)),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ~r2_hidden(sK3(k2_relat_1(sK2)),sK1) | spl5_9),
% 0.20/0.51    inference(resolution,[],[f97,f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | spl5_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f95])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~spl5_3 | ~spl5_10 | spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f70,f58,f100,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    spl5_4 <=> k1_xboole_0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_4),
% 0.20/0.51    inference(superposition,[],[f60,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2) | spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f58])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl5_8 | ~spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f86,f95,f91])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~m1_subset_1(sK3(k2_relat_1(sK2)),sK1) | k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.51    inference(resolution,[],[f85,f30])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | ~m1_subset_1(X0,sK1)) )),
% 0.20/0.51    inference(global_subsumption,[],[f24,f84])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK2)) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))) )),
% 0.20/0.51    inference(superposition,[],[f23,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X3] : (~r2_hidden(X3,k2_relset_1(sK0,sK1,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k1_relset_1(X0,X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f10])).
% 0.20/0.51  fof(f10,conjecture,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k2_relset_1(X0,X1,X2))) & k1_xboole_0 != k1_relset_1(X0,X1,X2)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    spl5_7 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f63,f53,f77])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    v5_relat_1(sK2,sK1) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f55,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f53])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    spl5_5 | ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f64,f53,f66])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    v1_relat_1(sK2) | ~spl5_3),
% 0.20/0.51    inference(resolution,[],[f55,f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f25,f58])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    k1_xboole_0 != k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f24,f53])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (32366)------------------------------
% 0.20/0.51  % (32366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (32366)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (32366)Memory used [KB]: 10746
% 0.20/0.51  % (32366)Time elapsed: 0.009 s
% 0.20/0.51  % (32366)------------------------------
% 0.20/0.51  % (32366)------------------------------
% 0.20/0.51  % (32343)Success in time 0.145 s
%------------------------------------------------------------------------------
