%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 568 expanded)
%              Number of leaves         :   27 ( 152 expanded)
%              Depth                    :   16
%              Number of atoms          :  485 (2582 expanded)
%              Number of equality atoms :  130 ( 672 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (11551)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f945,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f100,f114,f175,f186,f204,f321,f465,f513,f528,f602,f604,f651,f868,f944])).

fof(f944,plain,
    ( ~ spl4_3
    | spl4_5
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(avatar_contradiction_clause,[],[f943])).

fof(f943,plain,
    ( $false
    | ~ spl4_3
    | spl4_5
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(subsumption_resolution,[],[f942,f98])).

fof(f98,plain,
    ( k1_xboole_0 != sK0
    | spl4_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f942,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f930,f526])).

fof(f526,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f294,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

% (11552)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f294,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f293,f115])).

fof(f115,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f46,f72])).

fof(f72,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f293,plain,(
    ! [X0] :
      ( r1_tarski(k1_relat_1(k1_xboole_0),X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f217,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f217,plain,(
    ! [X11] : v4_relat_1(k1_xboole_0,X11) ),
    inference(resolution,[],[f119,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

% (11547)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f119,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f55,f44])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f930,plain,
    ( sK0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_28
    | ~ spl4_29 ),
    inference(superposition,[],[f805,f873])).

fof(f873,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(resolution,[],[f808,f126])).

fof(f808,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f807,f72])).

fof(f807,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl4_3
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f802,f594])).

fof(f594,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f592])).

fof(f592,plain,
    ( spl4_28
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f802,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f89,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f805,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_29 ),
    inference(forward_demodulation,[],[f798,f597])).

fof(f597,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f596])).

fof(f596,plain,
    ( spl4_29
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f798,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_3 ),
    inference(resolution,[],[f89,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f868,plain,
    ( spl4_2
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(avatar_contradiction_clause,[],[f867])).

fof(f867,plain,
    ( $false
    | spl4_2
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_18
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f853,f316])).

fof(f316,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f315])).

fof(f315,plain,
    ( spl4_18
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f853,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_13
    | ~ spl4_28 ),
    inference(superposition,[],[f747,f786])).

fof(f786,plain,
    ( k1_xboole_0 = sK3
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f785,f73])).

fof(f73,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f785,plain,
    ( sK3 = k2_zfmisc_1(k1_xboole_0,sK1)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f185,f99])).

fof(f99,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f97])).

fof(f185,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl4_13
  <=> sK3 = k2_zfmisc_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f747,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | spl4_2
    | ~ spl4_5
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f727,f594])).

fof(f727,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f86,f99])).

fof(f86,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_2
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f651,plain,
    ( ~ spl4_5
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f650])).

fof(f650,plain,
    ( $false
    | ~ spl4_5
    | spl4_10 ),
    inference(subsumption_resolution,[],[f649,f44])).

fof(f649,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl4_5
    | spl4_10 ),
    inference(forward_demodulation,[],[f170,f99])).

fof(f170,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_10
  <=> r1_tarski(sK0,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f604,plain,
    ( spl4_2
    | ~ spl4_11
    | spl4_28 ),
    inference(avatar_contradiction_clause,[],[f603])).

fof(f603,plain,
    ( $false
    | spl4_2
    | ~ spl4_11
    | spl4_28 ),
    inference(global_subsumption,[],[f590,f600,f593])).

% (11548)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (11543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% (11558)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (11541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
fof(f593,plain,
    ( k1_xboole_0 != sK2
    | spl4_28 ),
    inference(avatar_component_clause,[],[f592])).

fof(f600,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f585,f174])).

fof(f174,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_11
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f585,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f514,f60])).

fof(f514,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f510,f174])).

fof(f510,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2))) ),
    inference(resolution,[],[f284,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f284,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(sK3),X0)
      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) ) ),
    inference(subsumption_resolution,[],[f280,f122])).

fof(f122,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f28])).

fof(f28,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f280,plain,(
    ! [X0] :
      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
      | ~ r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f208,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X2),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f208,plain,(
    r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(superposition,[],[f41,f150])).

fof(f150,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f61,f40])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f41,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f590,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | spl4_2
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f582,f86])).

fof(f582,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | k1_xboole_0 = sK2
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl4_11 ),
    inference(resolution,[],[f514,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f602,plain,
    ( ~ spl4_11
    | spl4_29 ),
    inference(avatar_contradiction_clause,[],[f601])).

fof(f601,plain,
    ( $false
    | ~ spl4_11
    | spl4_29 ),
    inference(subsumption_resolution,[],[f598,f600])).

fof(f598,plain,
    ( sK0 != k1_relset_1(sK0,sK2,sK3)
    | spl4_29 ),
    inference(avatar_component_clause,[],[f596])).

fof(f528,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | spl4_19 ),
    inference(subsumption_resolution,[],[f526,f320])).

fof(f320,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl4_19 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl4_19
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f513,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f512])).

fof(f512,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f509,f90])).

fof(f90,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f509,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(resolution,[],[f284,f141])).

fof(f141,plain,(
    r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(subsumption_resolution,[],[f140,f122])).

fof(f140,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f137,f47])).

fof(f137,plain,(
    v4_relat_1(sK3,sK0) ),
    inference(resolution,[],[f62,f40])).

fof(f465,plain,
    ( ~ spl4_5
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | ~ spl4_5
    | spl4_12 ),
    inference(subsumption_resolution,[],[f463,f44])).

fof(f463,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl4_5
    | spl4_12 ),
    inference(forward_demodulation,[],[f450,f73])).

fof(f450,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3)
    | ~ spl4_5
    | spl4_12 ),
    inference(superposition,[],[f181,f99])).

fof(f181,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl4_12
  <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f321,plain,
    ( spl4_18
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f313,f318,f315])).

fof(f313,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(superposition,[],[f218,f215])).

fof(f215,plain,(
    ! [X8,X9] : k1_relset_1(X8,X9,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f119,f60])).

fof(f218,plain,(
    ! [X12] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X12,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X12) ) ),
    inference(resolution,[],[f119,f111])).

fof(f111,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) ) ),
    inference(forward_demodulation,[],[f77,f73])).

fof(f77,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f204,plain,
    ( spl4_4
    | spl4_11 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_4
    | spl4_11 ),
    inference(subsumption_resolution,[],[f200,f173])).

fof(f173,plain,
    ( sK0 != k1_relat_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f172])).

fof(f200,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl4_4 ),
    inference(superposition,[],[f160,f147])).

fof(f147,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f60,f40])).

fof(f160,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f159,f95])).

fof(f95,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f159,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f156,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f156,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f64,f40])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f186,plain,
    ( ~ spl4_12
    | spl4_13 ),
    inference(avatar_split_clause,[],[f176,f183,f179])).

fof(f176,plain,
    ( sK3 = k2_zfmisc_1(sK0,sK1)
    | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) ),
    inference(resolution,[],[f117,f53])).

fof(f117,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f54,f40])).

fof(f175,plain,
    ( ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f165,f172,f168])).

fof(f165,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ r1_tarski(sK0,k1_relat_1(sK3)) ),
    inference(resolution,[],[f141,f53])).

fof(f114,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f82,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f100,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f42,f97,f93])).

fof(f42,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f43,f88,f84,f80])).

fof(f43,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:49:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (11550)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (11542)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.53  % (11545)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.53  % (11544)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (11546)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (11546)Refutation not found, incomplete strategy% (11546)------------------------------
% 0.22/0.54  % (11546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (11546)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (11546)Memory used [KB]: 10618
% 0.22/0.54  % (11546)Time elapsed: 0.105 s
% 0.22/0.54  % (11546)------------------------------
% 0.22/0.54  % (11546)------------------------------
% 0.22/0.54  % (11563)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.54  % (11540)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.54  % (11562)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (11561)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  % (11554)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (11555)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.55  % (11556)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (11553)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (11550)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  % (11551)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  fof(f945,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f91,f100,f114,f175,f186,f204,f321,f465,f513,f528,f602,f604,f651,f868,f944])).
% 0.22/0.56  fof(f944,plain,(
% 0.22/0.56    ~spl4_3 | spl4_5 | ~spl4_28 | ~spl4_29),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f943])).
% 0.22/0.56  fof(f943,plain,(
% 0.22/0.56    $false | (~spl4_3 | spl4_5 | ~spl4_28 | ~spl4_29)),
% 0.22/0.56    inference(subsumption_resolution,[],[f942,f98])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    k1_xboole_0 != sK0 | spl4_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    spl4_5 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.56  fof(f942,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | (~spl4_3 | ~spl4_28 | ~spl4_29)),
% 0.22/0.56    inference(forward_demodulation,[],[f930,f526])).
% 0.22/0.56  fof(f526,plain,(
% 0.22/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(resolution,[],[f294,f126])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.22/0.56    inference(resolution,[],[f53,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(flattening,[],[f32])).
% 0.22/0.56  % (11552)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.56  fof(f294,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f293,f115])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    v1_relat_1(k1_xboole_0)),
% 0.22/0.56    inference(superposition,[],[f46,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.22/0.56    inference(equality_resolution,[],[f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.22/0.56    inference(nnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.56  fof(f293,plain,(
% 0.22/0.56    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.22/0.56    inference(resolution,[],[f217,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(nnf_transformation,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.22/0.56  fof(f217,plain,(
% 0.22/0.56    ( ! [X11] : (v4_relat_1(k1_xboole_0,X11)) )),
% 0.22/0.56    inference(resolution,[],[f119,f62])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  % (11547)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.56    inference(resolution,[],[f55,f44])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.56  fof(f930,plain,(
% 0.22/0.56    sK0 = k1_relat_1(k1_xboole_0) | (~spl4_3 | ~spl4_28 | ~spl4_29)),
% 0.22/0.56    inference(superposition,[],[f805,f873])).
% 0.22/0.56  fof(f873,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | (~spl4_3 | ~spl4_28)),
% 0.22/0.56    inference(resolution,[],[f808,f126])).
% 0.22/0.56  fof(f808,plain,(
% 0.22/0.56    r1_tarski(sK3,k1_xboole_0) | (~spl4_3 | ~spl4_28)),
% 0.22/0.56    inference(forward_demodulation,[],[f807,f72])).
% 0.22/0.56  fof(f807,plain,(
% 0.22/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,k1_xboole_0)) | (~spl4_3 | ~spl4_28)),
% 0.22/0.56    inference(forward_demodulation,[],[f802,f594])).
% 0.22/0.56  fof(f594,plain,(
% 0.22/0.56    k1_xboole_0 = sK2 | ~spl4_28),
% 0.22/0.56    inference(avatar_component_clause,[],[f592])).
% 0.22/0.56  fof(f592,plain,(
% 0.22/0.56    spl4_28 <=> k1_xboole_0 = sK2),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.56  fof(f802,plain,(
% 0.22/0.56    r1_tarski(sK3,k2_zfmisc_1(sK0,sK2)) | ~spl4_3),
% 0.22/0.56    inference(resolution,[],[f89,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f88])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    spl4_3 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f805,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK3) | (~spl4_3 | ~spl4_29)),
% 0.22/0.56    inference(forward_demodulation,[],[f798,f597])).
% 0.22/0.56  fof(f597,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl4_29),
% 0.22/0.56    inference(avatar_component_clause,[],[f596])).
% 0.22/0.56  fof(f596,plain,(
% 0.22/0.56    spl4_29 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.22/0.56  fof(f798,plain,(
% 0.22/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl4_3),
% 0.22/0.56    inference(resolution,[],[f89,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f868,plain,(
% 0.22/0.56    spl4_2 | ~spl4_5 | ~spl4_13 | ~spl4_18 | ~spl4_28),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f867])).
% 0.22/0.56  fof(f867,plain,(
% 0.22/0.56    $false | (spl4_2 | ~spl4_5 | ~spl4_13 | ~spl4_18 | ~spl4_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f853,f316])).
% 0.22/0.56  fof(f316,plain,(
% 0.22/0.56    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl4_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f315])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    spl4_18 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.56  fof(f853,plain,(
% 0.22/0.56    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_13 | ~spl4_28)),
% 0.22/0.56    inference(superposition,[],[f747,f786])).
% 0.22/0.56  fof(f786,plain,(
% 0.22/0.56    k1_xboole_0 = sK3 | (~spl4_5 | ~spl4_13)),
% 0.22/0.56    inference(forward_demodulation,[],[f785,f73])).
% 0.22/0.56  fof(f73,plain,(
% 0.22/0.56    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.22/0.56    inference(equality_resolution,[],[f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f785,plain,(
% 0.22/0.56    sK3 = k2_zfmisc_1(k1_xboole_0,sK1) | (~spl4_5 | ~spl4_13)),
% 0.22/0.56    inference(forward_demodulation,[],[f185,f99])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | ~spl4_5),
% 0.22/0.56    inference(avatar_component_clause,[],[f97])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    sK3 = k2_zfmisc_1(sK0,sK1) | ~spl4_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f183])).
% 0.22/0.56  fof(f183,plain,(
% 0.22/0.56    spl4_13 <=> sK3 = k2_zfmisc_1(sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.56  fof(f747,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (spl4_2 | ~spl4_5 | ~spl4_28)),
% 0.22/0.56    inference(forward_demodulation,[],[f727,f594])).
% 0.22/0.56  fof(f727,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (spl4_2 | ~spl4_5)),
% 0.22/0.56    inference(superposition,[],[f86,f99])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ~v1_funct_2(sK3,sK0,sK2) | spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f84])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    spl4_2 <=> v1_funct_2(sK3,sK0,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f651,plain,(
% 0.22/0.56    ~spl4_5 | spl4_10),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f650])).
% 0.22/0.56  fof(f650,plain,(
% 0.22/0.56    $false | (~spl4_5 | spl4_10)),
% 0.22/0.56    inference(subsumption_resolution,[],[f649,f44])).
% 0.22/0.56  fof(f649,plain,(
% 0.22/0.56    ~r1_tarski(k1_xboole_0,k1_relat_1(sK3)) | (~spl4_5 | spl4_10)),
% 0.22/0.56    inference(forward_demodulation,[],[f170,f99])).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    ~r1_tarski(sK0,k1_relat_1(sK3)) | spl4_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f168])).
% 0.22/0.56  fof(f168,plain,(
% 0.22/0.56    spl4_10 <=> r1_tarski(sK0,k1_relat_1(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.56  fof(f604,plain,(
% 0.22/0.56    spl4_2 | ~spl4_11 | spl4_28),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f603])).
% 0.22/0.56  fof(f603,plain,(
% 0.22/0.56    $false | (spl4_2 | ~spl4_11 | spl4_28)),
% 0.22/0.56    inference(global_subsumption,[],[f590,f600,f593])).
% 0.22/0.56  % (11548)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (11543)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (11558)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.57  % (11541)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  fof(f593,plain,(
% 0.22/0.57    k1_xboole_0 != sK2 | spl4_28),
% 0.22/0.57    inference(avatar_component_clause,[],[f592])).
% 0.22/0.57  fof(f600,plain,(
% 0.22/0.57    sK0 = k1_relset_1(sK0,sK2,sK3) | ~spl4_11),
% 0.22/0.57    inference(forward_demodulation,[],[f585,f174])).
% 0.22/0.57  fof(f174,plain,(
% 0.22/0.57    sK0 = k1_relat_1(sK3) | ~spl4_11),
% 0.22/0.57    inference(avatar_component_clause,[],[f172])).
% 0.22/0.57  fof(f172,plain,(
% 0.22/0.57    spl4_11 <=> sK0 = k1_relat_1(sK3)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.57  fof(f585,plain,(
% 0.22/0.57    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl4_11),
% 0.22/0.57    inference(resolution,[],[f514,f60])).
% 0.22/0.57  fof(f514,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl4_11),
% 0.22/0.57    inference(forward_demodulation,[],[f510,f174])).
% 0.22/0.57  fof(f510,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK2)))),
% 0.22/0.57    inference(resolution,[],[f284,f70])).
% 0.22/0.57  fof(f70,plain,(
% 0.22/0.57    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.57    inference(equality_resolution,[],[f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.57    inference(cnf_transformation,[],[f33])).
% 0.22/0.57  fof(f284,plain,(
% 0.22/0.57    ( ! [X0] : (~r1_tarski(k1_relat_1(sK3),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) )),
% 0.22/0.57    inference(subsumption_resolution,[],[f280,f122])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    v1_relat_1(sK3)),
% 0.22/0.57    inference(subsumption_resolution,[],[f121,f46])).
% 0.22/0.57  fof(f121,plain,(
% 0.22/0.57    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.22/0.57    inference(resolution,[],[f45,f40])).
% 0.22/0.57  fof(f40,plain,(
% 0.22/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.57    inference(cnf_transformation,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.22/0.57    inference(flattening,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,negated_conjecture,(
% 0.22/0.57    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.57    inference(negated_conjecture,[],[f14])).
% 0.22/0.57  fof(f14,conjecture,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 0.22/0.57  fof(f45,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.58  fof(f5,axiom,(
% 0.22/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.58  fof(f280,plain,(
% 0.22/0.58    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) | ~r1_tarski(k1_relat_1(sK3),X0) | ~v1_relat_1(sK3)) )),
% 0.22/0.58    inference(resolution,[],[f208,f59])).
% 0.22/0.58  fof(f59,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r1_tarski(k2_relat_1(X2),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f22])).
% 0.22/0.58  fof(f22,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(flattening,[],[f21])).
% 0.22/0.58  fof(f21,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 0.22/0.58    inference(ennf_transformation,[],[f12])).
% 0.22/0.58  fof(f12,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.22/0.58  fof(f208,plain,(
% 0.22/0.58    r1_tarski(k2_relat_1(sK3),sK2)),
% 0.22/0.58    inference(superposition,[],[f41,f150])).
% 0.22/0.58  fof(f150,plain,(
% 0.22/0.58    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.22/0.58    inference(resolution,[],[f61,f40])).
% 0.22/0.58  fof(f61,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f24])).
% 0.22/0.58  fof(f24,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f11])).
% 0.22/0.58  fof(f11,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f590,plain,(
% 0.22/0.58    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | (spl4_2 | ~spl4_11)),
% 0.22/0.58    inference(subsumption_resolution,[],[f582,f86])).
% 0.22/0.58  fof(f582,plain,(
% 0.22/0.58    sK0 != k1_relset_1(sK0,sK2,sK3) | k1_xboole_0 = sK2 | v1_funct_2(sK3,sK0,sK2) | ~spl4_11),
% 0.22/0.58    inference(resolution,[],[f514,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | v1_funct_2(X2,X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(nnf_transformation,[],[f27])).
% 0.22/0.58  fof(f27,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(flattening,[],[f26])).
% 0.22/0.58  fof(f26,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.58    inference(ennf_transformation,[],[f13])).
% 0.22/0.58  fof(f13,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.58  fof(f602,plain,(
% 0.22/0.58    ~spl4_11 | spl4_29),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f601])).
% 0.22/0.58  fof(f601,plain,(
% 0.22/0.58    $false | (~spl4_11 | spl4_29)),
% 0.22/0.58    inference(subsumption_resolution,[],[f598,f600])).
% 0.22/0.58  fof(f598,plain,(
% 0.22/0.58    sK0 != k1_relset_1(sK0,sK2,sK3) | spl4_29),
% 0.22/0.58    inference(avatar_component_clause,[],[f596])).
% 0.22/0.58  fof(f528,plain,(
% 0.22/0.58    spl4_19),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f527])).
% 0.22/0.58  fof(f527,plain,(
% 0.22/0.58    $false | spl4_19),
% 0.22/0.58    inference(subsumption_resolution,[],[f526,f320])).
% 0.22/0.58  fof(f320,plain,(
% 0.22/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl4_19),
% 0.22/0.58    inference(avatar_component_clause,[],[f318])).
% 0.22/0.58  fof(f318,plain,(
% 0.22/0.58    spl4_19 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.58  fof(f513,plain,(
% 0.22/0.58    spl4_3),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f512])).
% 0.22/0.58  fof(f512,plain,(
% 0.22/0.58    $false | spl4_3),
% 0.22/0.58    inference(subsumption_resolution,[],[f509,f90])).
% 0.22/0.58  fof(f90,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl4_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f88])).
% 0.22/0.58  fof(f509,plain,(
% 0.22/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.58    inference(resolution,[],[f284,f141])).
% 0.22/0.58  fof(f141,plain,(
% 0.22/0.58    r1_tarski(k1_relat_1(sK3),sK0)),
% 0.22/0.58    inference(subsumption_resolution,[],[f140,f122])).
% 0.22/0.58  fof(f140,plain,(
% 0.22/0.58    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3)),
% 0.22/0.58    inference(resolution,[],[f137,f47])).
% 0.22/0.58  fof(f137,plain,(
% 0.22/0.58    v4_relat_1(sK3,sK0)),
% 0.22/0.58    inference(resolution,[],[f62,f40])).
% 0.22/0.58  fof(f465,plain,(
% 0.22/0.58    ~spl4_5 | spl4_12),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f464])).
% 0.22/0.58  fof(f464,plain,(
% 0.22/0.58    $false | (~spl4_5 | spl4_12)),
% 0.22/0.58    inference(subsumption_resolution,[],[f463,f44])).
% 0.22/0.58  fof(f463,plain,(
% 0.22/0.58    ~r1_tarski(k1_xboole_0,sK3) | (~spl4_5 | spl4_12)),
% 0.22/0.58    inference(forward_demodulation,[],[f450,f73])).
% 0.22/0.58  fof(f450,plain,(
% 0.22/0.58    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),sK3) | (~spl4_5 | spl4_12)),
% 0.22/0.58    inference(superposition,[],[f181,f99])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3) | spl4_12),
% 0.22/0.58    inference(avatar_component_clause,[],[f179])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    spl4_12 <=> r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.58  fof(f321,plain,(
% 0.22/0.58    spl4_18 | ~spl4_19),
% 0.22/0.58    inference(avatar_split_clause,[],[f313,f318,f315])).
% 0.22/0.58  fof(f313,plain,(
% 0.22/0.58    ( ! [X0] : (k1_xboole_0 != k1_relat_1(k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 0.22/0.58    inference(superposition,[],[f218,f215])).
% 0.22/0.58  fof(f215,plain,(
% 0.22/0.58    ( ! [X8,X9] : (k1_relset_1(X8,X9,k1_xboole_0) = k1_relat_1(k1_xboole_0)) )),
% 0.22/0.58    inference(resolution,[],[f119,f60])).
% 0.22/0.58  fof(f218,plain,(
% 0.22/0.58    ( ! [X12] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X12,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X12)) )),
% 0.22/0.58    inference(resolution,[],[f119,f111])).
% 0.22/0.58  fof(f111,plain,(
% 0.22/0.58    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)) )),
% 0.22/0.58    inference(forward_demodulation,[],[f77,f73])).
% 0.22/0.58  fof(f77,plain,(
% 0.22/0.58    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 0.22/0.58    inference(equality_resolution,[],[f67])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f204,plain,(
% 0.22/0.58    spl4_4 | spl4_11),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f203])).
% 0.22/0.58  fof(f203,plain,(
% 0.22/0.58    $false | (spl4_4 | spl4_11)),
% 0.22/0.58    inference(subsumption_resolution,[],[f200,f173])).
% 0.22/0.58  fof(f173,plain,(
% 0.22/0.58    sK0 != k1_relat_1(sK3) | spl4_11),
% 0.22/0.58    inference(avatar_component_clause,[],[f172])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    sK0 = k1_relat_1(sK3) | spl4_4),
% 0.22/0.58    inference(superposition,[],[f160,f147])).
% 0.22/0.58  fof(f147,plain,(
% 0.22/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.58    inference(resolution,[],[f60,f40])).
% 0.22/0.58  fof(f160,plain,(
% 0.22/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | spl4_4),
% 0.22/0.58    inference(subsumption_resolution,[],[f159,f95])).
% 0.22/0.58  fof(f95,plain,(
% 0.22/0.58    k1_xboole_0 != sK1 | spl4_4),
% 0.22/0.58    inference(avatar_component_clause,[],[f93])).
% 0.22/0.58  fof(f93,plain,(
% 0.22/0.58    spl4_4 <=> k1_xboole_0 = sK1),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.58  fof(f159,plain,(
% 0.22/0.58    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f156,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    v1_funct_2(sK3,sK0,sK1)),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f156,plain,(
% 0.22/0.58    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.22/0.58    inference(resolution,[],[f64,f40])).
% 0.22/0.58  fof(f64,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.22/0.58    inference(cnf_transformation,[],[f37])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    ~spl4_12 | spl4_13),
% 0.22/0.58    inference(avatar_split_clause,[],[f176,f183,f179])).
% 0.22/0.58  fof(f176,plain,(
% 0.22/0.58    sK3 = k2_zfmisc_1(sK0,sK1) | ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK3)),
% 0.22/0.58    inference(resolution,[],[f117,f53])).
% 0.22/0.58  fof(f117,plain,(
% 0.22/0.58    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 0.22/0.58    inference(resolution,[],[f54,f40])).
% 0.22/0.58  fof(f175,plain,(
% 0.22/0.58    ~spl4_10 | spl4_11),
% 0.22/0.58    inference(avatar_split_clause,[],[f165,f172,f168])).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    sK0 = k1_relat_1(sK3) | ~r1_tarski(sK0,k1_relat_1(sK3))),
% 0.22/0.58    inference(resolution,[],[f141,f53])).
% 0.22/0.58  fof(f114,plain,(
% 0.22/0.58    spl4_1),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f113])).
% 0.22/0.58  fof(f113,plain,(
% 0.22/0.58    $false | spl4_1),
% 0.22/0.58    inference(subsumption_resolution,[],[f82,f38])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    v1_funct_1(sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ~v1_funct_1(sK3) | spl4_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    spl4_1 <=> v1_funct_1(sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.58  fof(f100,plain,(
% 0.22/0.58    ~spl4_4 | spl4_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f42,f97,f93])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.22/0.58    inference(avatar_split_clause,[],[f43,f88,f84,f80])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 0.22/0.58    inference(cnf_transformation,[],[f29])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (11550)------------------------------
% 0.22/0.58  % (11550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (11550)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (11550)Memory used [KB]: 11129
% 0.22/0.58  % (11550)Time elapsed: 0.129 s
% 0.22/0.58  % (11550)------------------------------
% 0.22/0.58  % (11550)------------------------------
% 0.22/0.58  % (11559)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.58  % (11539)Success in time 0.213 s
%------------------------------------------------------------------------------
