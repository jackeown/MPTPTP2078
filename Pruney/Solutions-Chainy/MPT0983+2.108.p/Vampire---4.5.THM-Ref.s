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
% DateTime   : Thu Dec  3 13:01:50 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 429 expanded)
%              Number of leaves         :   51 ( 165 expanded)
%              Depth                    :   12
%              Number of atoms          :  690 (1788 expanded)
%              Number of equality atoms :   83 ( 180 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3060,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f133,f279,f308,f380,f382,f401,f404,f573,f639,f686,f692,f694,f1181,f1186,f1192,f1260,f1821,f1822,f1865,f1873,f1882,f1884,f1885,f2993,f3005,f3034,f3059])).

fof(f3059,plain,
    ( spl6_1
    | ~ spl6_154 ),
    inference(avatar_contradiction_clause,[],[f3058])).

fof(f3058,plain,
    ( $false
    | spl6_1
    | ~ spl6_154 ),
    inference(resolution,[],[f3036,f160])).

fof(f160,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f115,f154])).

fof(f154,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(equality_resolution,[],[f150])).

% (4025)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f150,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k6_partfun1(X0) ) ),
    inference(resolution,[],[f134,f116])).

fof(f116,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f78,f76])).

fof(f76,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f78,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f134,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k6_partfun1(X0))
      | k1_xboole_0 = k6_partfun1(X0)
      | k1_xboole_0 != X0 ) ),
    inference(superposition,[],[f83,f118])).

fof(f118,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f80,f76])).

fof(f80,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f115,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f79,f76])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f3036,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl6_1
    | ~ spl6_154 ),
    inference(backward_demodulation,[],[f128,f3018])).

fof(f3018,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_154 ),
    inference(avatar_component_clause,[],[f3016])).

fof(f3016,plain,
    ( spl6_154
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).

fof(f128,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f3034,plain,
    ( ~ spl6_71
    | spl6_154
    | ~ spl6_153 ),
    inference(avatar_split_clause,[],[f3013,f2990,f3016,f1047])).

fof(f1047,plain,
    ( spl6_71
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).

fof(f2990,plain,
    ( spl6_153
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).

fof(f3013,plain,
    ( k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl6_153 ),
    inference(trivial_inequality_removal,[],[f3012])).

fof(f3012,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK2
    | ~ v1_relat_1(sK2)
    | ~ spl6_153 ),
    inference(superposition,[],[f83,f2992])).

fof(f2992,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_153 ),
    inference(avatar_component_clause,[],[f2990])).

fof(f3005,plain,(
    spl6_152 ),
    inference(avatar_contradiction_clause,[],[f3001])).

fof(f3001,plain,
    ( $false
    | spl6_152 ),
    inference(resolution,[],[f3000,f75])).

fof(f75,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f3000,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_152 ),
    inference(resolution,[],[f2994,f88])).

fof(f88,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK4(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2994,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0)
    | spl6_152 ),
    inference(resolution,[],[f2988,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f2988,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | spl6_152 ),
    inference(avatar_component_clause,[],[f2986])).

fof(f2986,plain,
    ( spl6_152
  <=> r1_tarski(k1_xboole_0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f2993,plain,
    ( ~ spl6_152
    | spl6_153
    | ~ spl6_71
    | ~ spl6_80
    | ~ spl6_91 ),
    inference(avatar_split_clause,[],[f2981,f1468,f1202,f1047,f2990,f2986])).

fof(f1202,plain,
    ( spl6_80
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f1468,plain,
    ( spl6_91
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).

fof(f2981,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = k1_relat_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK2))
    | ~ spl6_80
    | ~ spl6_91 ),
    inference(resolution,[],[f1229,f1922])).

fof(f1922,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl6_80
    | ~ spl6_91 ),
    inference(backward_demodulation,[],[f69,f1920])).

fof(f1920,plain,
    ( k1_xboole_0 = sK0
    | ~ spl6_80
    | ~ spl6_91 ),
    inference(forward_demodulation,[],[f1904,f158])).

fof(f158,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f117,f154])).

fof(f117,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f81,f76])).

fof(f81,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f1904,plain,
    ( sK0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_80
    | ~ spl6_91 ),
    inference(backward_demodulation,[],[f1204,f1470])).

fof(f1470,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_91 ),
    inference(avatar_component_clause,[],[f1468])).

fof(f1204,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f1202])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f50,f49])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

fof(f1229,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f147,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_relat_1(X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f105,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1885,plain,
    ( ~ spl6_72
    | spl6_91
    | ~ spl6_65
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1852,f1202,f654,f1468,f1051])).

fof(f1051,plain,
    ( spl6_72
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f654,plain,
    ( spl6_65
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).

fof(f1852,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl6_80 ),
    inference(superposition,[],[f84,f1204])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1884,plain,
    ( ~ spl6_29
    | ~ spl6_63
    | ~ spl6_30
    | ~ spl6_31
    | ~ spl6_64
    | ~ spl6_32
    | spl6_1
    | spl6_65
    | ~ spl6_66
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f1166,f276,f658,f654,f126,f371,f650,f367,f363,f646,f359])).

fof(f359,plain,
    ( spl6_29
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f646,plain,
    ( spl6_63
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f363,plain,
    ( spl6_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f367,plain,
    ( spl6_31
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f650,plain,
    ( spl6_64
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f371,plain,
    ( spl6_32
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f658,plain,
    ( spl6_66
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).

fof(f276,plain,
    ( spl6_18
  <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1166,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl6_18 ),
    inference(superposition,[],[f107,f278])).

fof(f278,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f276])).

fof(f107,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

fof(f1882,plain,(
    spl6_105 ),
    inference(avatar_contradiction_clause,[],[f1879])).

fof(f1879,plain,
    ( $false
    | spl6_105 ),
    inference(resolution,[],[f1872,f120])).

fof(f120,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1872,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl6_105 ),
    inference(avatar_component_clause,[],[f1870])).

fof(f1870,plain,
    ( spl6_105
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f1873,plain,
    ( ~ spl6_72
    | ~ spl6_105
    | ~ spl6_80
    | spl6_104 ),
    inference(avatar_split_clause,[],[f1868,f1862,f1202,f1870,f1051])).

fof(f1862,plain,
    ( spl6_104
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1868,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_80
    | spl6_104 ),
    inference(forward_demodulation,[],[f1867,f1204])).

fof(f1867,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | spl6_104 ),
    inference(resolution,[],[f1864,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f1864,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_104 ),
    inference(avatar_component_clause,[],[f1862])).

fof(f1865,plain,
    ( ~ spl6_72
    | ~ spl6_104
    | spl6_2
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f1851,f1202,f130,f1862,f1051])).

fof(f130,plain,
    ( spl6_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1851,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_80 ),
    inference(superposition,[],[f119,f1204])).

fof(f119,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

fof(f1822,plain,
    ( ~ spl6_79
    | spl6_80
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1770,f1189,f1202,f1198])).

fof(f1198,plain,
    ( spl6_79
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f1189,plain,
    ( spl6_78
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1770,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl6_78 ),
    inference(resolution,[],[f1191,f99])).

fof(f1191,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1189])).

fof(f1821,plain,(
    ~ spl6_84 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl6_84 ),
    inference(resolution,[],[f1259,f72])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1259,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f1258,plain,
    ( spl6_84
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f1260,plain,
    ( ~ spl6_72
    | spl6_84
    | spl6_79 ),
    inference(avatar_split_clause,[],[f1252,f1198,f1258,f1051])).

fof(f1252,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
        | ~ v1_relat_1(sK3) )
    | spl6_79 ),
    inference(resolution,[],[f148,f1200])).

fof(f1200,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_79 ),
    inference(avatar_component_clause,[],[f1198])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f106,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1192,plain,
    ( ~ spl6_71
    | ~ spl6_72
    | spl6_78
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f1187,f440,f1189,f1051,f1047])).

fof(f440,plain,
    ( spl6_41
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1187,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f1169,f117])).

fof(f1169,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_41 ),
    inference(superposition,[],[f85,f442])).

fof(f442,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f440])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1186,plain,(
    spl6_72 ),
    inference(avatar_contradiction_clause,[],[f1184])).

fof(f1184,plain,
    ( $false
    | spl6_72 ),
    inference(resolution,[],[f1182,f90])).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f1182,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl6_72 ),
    inference(resolution,[],[f1060,f72])).

fof(f1060,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_72 ),
    inference(resolution,[],[f1053,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1053,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_72 ),
    inference(avatar_component_clause,[],[f1051])).

fof(f1181,plain,(
    spl6_71 ),
    inference(avatar_contradiction_clause,[],[f1179])).

fof(f1179,plain,
    ( $false
    | spl6_71 ),
    inference(resolution,[],[f1177,f90])).

fof(f1177,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_71 ),
    inference(resolution,[],[f1059,f69])).

fof(f1059,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_71 ),
    inference(resolution,[],[f1049,f86])).

fof(f1049,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_71 ),
    inference(avatar_component_clause,[],[f1047])).

fof(f694,plain,(
    spl6_64 ),
    inference(avatar_contradiction_clause,[],[f693])).

fof(f693,plain,
    ( $false
    | spl6_64 ),
    inference(resolution,[],[f652,f71])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f652,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl6_64 ),
    inference(avatar_component_clause,[],[f650])).

fof(f692,plain,(
    spl6_63 ),
    inference(avatar_contradiction_clause,[],[f691])).

fof(f691,plain,
    ( $false
    | spl6_63 ),
    inference(resolution,[],[f648,f68])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f648,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl6_63 ),
    inference(avatar_component_clause,[],[f646])).

fof(f686,plain,(
    spl6_66 ),
    inference(avatar_contradiction_clause,[],[f685])).

fof(f685,plain,
    ( $false
    | spl6_66 ),
    inference(resolution,[],[f660,f115])).

fof(f660,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl6_66 ),
    inference(avatar_component_clause,[],[f658])).

fof(f639,plain,
    ( ~ spl6_29
    | ~ spl6_30
    | ~ spl6_31
    | ~ spl6_32
    | spl6_41
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f635,f276,f440,f371,f367,f363,f359])).

fof(f635,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl6_18 ),
    inference(superposition,[],[f111,f278])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f573,plain,
    ( ~ spl6_29
    | ~ spl6_30
    | ~ spl6_31
    | ~ spl6_32
    | spl6_16 ),
    inference(avatar_split_clause,[],[f570,f268,f371,f367,f363,f359])).

fof(f268,plain,
    ( spl6_16
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f570,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl6_16 ),
    inference(resolution,[],[f270,f113])).

fof(f113,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f270,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_16 ),
    inference(avatar_component_clause,[],[f268])).

fof(f404,plain,(
    spl6_32 ),
    inference(avatar_contradiction_clause,[],[f402])).

fof(f402,plain,
    ( $false
    | spl6_32 ),
    inference(resolution,[],[f373,f72])).

fof(f373,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f371])).

fof(f401,plain,(
    spl6_30 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | spl6_30 ),
    inference(resolution,[],[f365,f69])).

fof(f365,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl6_30 ),
    inference(avatar_component_clause,[],[f363])).

fof(f382,plain,(
    spl6_31 ),
    inference(avatar_contradiction_clause,[],[f381])).

fof(f381,plain,
    ( $false
    | spl6_31 ),
    inference(resolution,[],[f369,f70])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f369,plain,
    ( ~ v1_funct_1(sK3)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f367])).

fof(f380,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | spl6_29 ),
    inference(resolution,[],[f361,f67])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f361,plain,
    ( ~ v1_funct_1(sK2)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f359])).

fof(f308,plain,(
    spl6_17 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl6_17 ),
    inference(resolution,[],[f274,f114])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f76])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f274,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl6_17 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl6_17
  <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f279,plain,
    ( ~ spl6_16
    | ~ spl6_17
    | spl6_18 ),
    inference(avatar_split_clause,[],[f264,f276,f272,f268])).

fof(f264,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f109,f73])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f133,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f74,f130,f126])).

fof(f74,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:42:35 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.48  % (4007)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.50  % (4023)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.53  % (3998)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (4015)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (3994)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (4019)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (4013)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (3995)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (3999)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (4005)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (4020)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.55  % (4021)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.42/0.55  % (4016)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.55  % (3997)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.42/0.55  % (4011)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (4022)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.55  % (4014)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.42/0.55  % (4008)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.42/0.55  % (4011)Refutation not found, incomplete strategy% (4011)------------------------------
% 1.42/0.55  % (4011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (4011)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (4011)Memory used [KB]: 10746
% 1.42/0.55  % (4011)Time elapsed: 0.131 s
% 1.42/0.55  % (4011)------------------------------
% 1.42/0.55  % (4011)------------------------------
% 1.42/0.55  % (4003)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.55  % (4009)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (4001)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.42/0.56  % (4012)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.42/0.56  % (4000)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.42/0.56  % (4010)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.42/0.56  % (4017)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.42/0.56  % (3996)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.56  % (4006)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (4004)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.57  % (4016)Refutation not found, incomplete strategy% (4016)------------------------------
% 1.42/0.57  % (4016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (4018)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.56/0.57  % (4016)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.57  
% 1.56/0.57  % (4016)Memory used [KB]: 11001
% 1.56/0.57  % (4016)Time elapsed: 0.116 s
% 1.56/0.57  % (4016)------------------------------
% 1.56/0.57  % (4016)------------------------------
% 1.56/0.58  % (4002)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 2.20/0.69  % (4006)Refutation found. Thanks to Tanya!
% 2.20/0.69  % SZS status Theorem for theBenchmark
% 2.20/0.70  % SZS output start Proof for theBenchmark
% 2.20/0.70  fof(f3060,plain,(
% 2.20/0.70    $false),
% 2.20/0.70    inference(avatar_sat_refutation,[],[f133,f279,f308,f380,f382,f401,f404,f573,f639,f686,f692,f694,f1181,f1186,f1192,f1260,f1821,f1822,f1865,f1873,f1882,f1884,f1885,f2993,f3005,f3034,f3059])).
% 2.20/0.71  fof(f3059,plain,(
% 2.20/0.71    spl6_1 | ~spl6_154),
% 2.20/0.71    inference(avatar_contradiction_clause,[],[f3058])).
% 2.20/0.71  fof(f3058,plain,(
% 2.20/0.71    $false | (spl6_1 | ~spl6_154)),
% 2.20/0.71    inference(resolution,[],[f3036,f160])).
% 2.20/0.71  fof(f160,plain,(
% 2.20/0.71    v2_funct_1(k1_xboole_0)),
% 2.20/0.71    inference(superposition,[],[f115,f154])).
% 2.20/0.71  fof(f154,plain,(
% 2.20/0.71    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 2.20/0.71    inference(equality_resolution,[],[f150])).
% 2.20/0.71  % (4025)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.20/0.71  fof(f150,plain,(
% 2.20/0.71    ( ! [X0] : (k1_xboole_0 != X0 | k1_xboole_0 = k6_partfun1(X0)) )),
% 2.20/0.71    inference(resolution,[],[f134,f116])).
% 2.20/0.71  fof(f116,plain,(
% 2.20/0.71    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f78,f76])).
% 2.20/0.71  fof(f76,plain,(
% 2.20/0.71    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f22])).
% 2.20/0.71  fof(f22,axiom,(
% 2.20/0.71    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.20/0.71  fof(f78,plain,(
% 2.20/0.71    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f15])).
% 2.20/0.71  fof(f15,axiom,(
% 2.20/0.71    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.20/0.71  fof(f134,plain,(
% 2.20/0.71    ( ! [X0] : (~v1_relat_1(k6_partfun1(X0)) | k1_xboole_0 = k6_partfun1(X0) | k1_xboole_0 != X0) )),
% 2.20/0.71    inference(superposition,[],[f83,f118])).
% 2.20/0.71  fof(f118,plain,(
% 2.20/0.71    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 2.20/0.71    inference(definition_unfolding,[],[f80,f76])).
% 2.20/0.71  fof(f80,plain,(
% 2.20/0.71    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.20/0.71    inference(cnf_transformation,[],[f14])).
% 2.20/0.71  fof(f14,axiom,(
% 2.20/0.71    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 2.20/0.71  fof(f83,plain,(
% 2.20/0.71    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f30])).
% 2.20/0.71  fof(f30,plain,(
% 2.20/0.71    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.20/0.71    inference(flattening,[],[f29])).
% 2.20/0.71  fof(f29,plain,(
% 2.20/0.71    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.20/0.71    inference(ennf_transformation,[],[f13])).
% 2.20/0.71  fof(f13,axiom,(
% 2.20/0.71    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 2.20/0.71  fof(f115,plain,(
% 2.20/0.71    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.20/0.71    inference(definition_unfolding,[],[f79,f76])).
% 2.20/0.71  fof(f79,plain,(
% 2.20/0.71    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f15])).
% 2.20/0.71  fof(f3036,plain,(
% 2.20/0.71    ~v2_funct_1(k1_xboole_0) | (spl6_1 | ~spl6_154)),
% 2.20/0.71    inference(backward_demodulation,[],[f128,f3018])).
% 2.20/0.71  fof(f3018,plain,(
% 2.20/0.71    k1_xboole_0 = sK2 | ~spl6_154),
% 2.20/0.71    inference(avatar_component_clause,[],[f3016])).
% 2.20/0.71  fof(f3016,plain,(
% 2.20/0.71    spl6_154 <=> k1_xboole_0 = sK2),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_154])])).
% 2.20/0.71  fof(f128,plain,(
% 2.20/0.71    ~v2_funct_1(sK2) | spl6_1),
% 2.20/0.71    inference(avatar_component_clause,[],[f126])).
% 2.20/0.71  fof(f126,plain,(
% 2.20/0.71    spl6_1 <=> v2_funct_1(sK2)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 2.20/0.71  fof(f3034,plain,(
% 2.20/0.71    ~spl6_71 | spl6_154 | ~spl6_153),
% 2.20/0.71    inference(avatar_split_clause,[],[f3013,f2990,f3016,f1047])).
% 2.20/0.71  fof(f1047,plain,(
% 2.20/0.71    spl6_71 <=> v1_relat_1(sK2)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_71])])).
% 2.20/0.71  fof(f2990,plain,(
% 2.20/0.71    spl6_153 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_153])])).
% 2.20/0.71  fof(f3013,plain,(
% 2.20/0.71    k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl6_153),
% 2.20/0.71    inference(trivial_inequality_removal,[],[f3012])).
% 2.20/0.71  fof(f3012,plain,(
% 2.20/0.71    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK2 | ~v1_relat_1(sK2) | ~spl6_153),
% 2.20/0.71    inference(superposition,[],[f83,f2992])).
% 2.20/0.71  fof(f2992,plain,(
% 2.20/0.71    k1_xboole_0 = k1_relat_1(sK2) | ~spl6_153),
% 2.20/0.71    inference(avatar_component_clause,[],[f2990])).
% 2.20/0.71  fof(f3005,plain,(
% 2.20/0.71    spl6_152),
% 2.20/0.71    inference(avatar_contradiction_clause,[],[f3001])).
% 2.20/0.71  fof(f3001,plain,(
% 2.20/0.71    $false | spl6_152),
% 2.20/0.71    inference(resolution,[],[f3000,f75])).
% 2.20/0.71  fof(f75,plain,(
% 2.20/0.71    v1_xboole_0(k1_xboole_0)),
% 2.20/0.71    inference(cnf_transformation,[],[f3])).
% 2.20/0.71  fof(f3,axiom,(
% 2.20/0.71    v1_xboole_0(k1_xboole_0)),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.20/0.71  fof(f3000,plain,(
% 2.20/0.71    ~v1_xboole_0(k1_xboole_0) | spl6_152),
% 2.20/0.71    inference(resolution,[],[f2994,f88])).
% 2.20/0.71  fof(f88,plain,(
% 2.20/0.71    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f55])).
% 2.20/0.71  fof(f55,plain,(
% 2.20/0.71    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.20/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f53,f54])).
% 2.20/0.71  fof(f54,plain,(
% 2.20/0.71    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK4(X0),X0))),
% 2.20/0.71    introduced(choice_axiom,[])).
% 2.20/0.71  fof(f53,plain,(
% 2.20/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.20/0.71    inference(rectify,[],[f52])).
% 2.20/0.71  fof(f52,plain,(
% 2.20/0.71    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.20/0.71    inference(nnf_transformation,[],[f1])).
% 2.20/0.71  fof(f1,axiom,(
% 2.20/0.71    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.20/0.71  fof(f2994,plain,(
% 2.20/0.71    r2_hidden(sK5(k1_xboole_0,k1_relat_1(sK2)),k1_xboole_0) | spl6_152),
% 2.20/0.71    inference(resolution,[],[f2988,f101])).
% 2.20/0.71  fof(f101,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f64])).
% 2.20/0.71  fof(f64,plain,(
% 2.20/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.20/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f62,f63])).
% 2.20/0.71  fof(f63,plain,(
% 2.20/0.71    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 2.20/0.71    introduced(choice_axiom,[])).
% 2.20/0.71  fof(f62,plain,(
% 2.20/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.20/0.71    inference(rectify,[],[f61])).
% 2.20/0.71  fof(f61,plain,(
% 2.20/0.71    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.20/0.71    inference(nnf_transformation,[],[f39])).
% 2.20/0.71  fof(f39,plain,(
% 2.20/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.20/0.71    inference(ennf_transformation,[],[f2])).
% 2.20/0.71  fof(f2,axiom,(
% 2.20/0.71    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.20/0.71  fof(f2988,plain,(
% 2.20/0.71    ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | spl6_152),
% 2.20/0.71    inference(avatar_component_clause,[],[f2986])).
% 2.20/0.71  fof(f2986,plain,(
% 2.20/0.71    spl6_152 <=> r1_tarski(k1_xboole_0,k1_relat_1(sK2))),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).
% 2.20/0.71  fof(f2993,plain,(
% 2.20/0.71    ~spl6_152 | spl6_153 | ~spl6_71 | ~spl6_80 | ~spl6_91),
% 2.20/0.71    inference(avatar_split_clause,[],[f2981,f1468,f1202,f1047,f2990,f2986])).
% 2.20/0.71  fof(f1202,plain,(
% 2.20/0.71    spl6_80 <=> sK0 = k2_relat_1(sK3)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 2.20/0.71  fof(f1468,plain,(
% 2.20/0.71    spl6_91 <=> k1_xboole_0 = sK3),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_91])])).
% 2.20/0.71  fof(f2981,plain,(
% 2.20/0.71    ~v1_relat_1(sK2) | k1_xboole_0 = k1_relat_1(sK2) | ~r1_tarski(k1_xboole_0,k1_relat_1(sK2)) | (~spl6_80 | ~spl6_91)),
% 2.20/0.71    inference(resolution,[],[f1229,f1922])).
% 2.20/0.71  fof(f1922,plain,(
% 2.20/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl6_80 | ~spl6_91)),
% 2.20/0.71    inference(backward_demodulation,[],[f69,f1920])).
% 2.20/0.71  fof(f1920,plain,(
% 2.20/0.71    k1_xboole_0 = sK0 | (~spl6_80 | ~spl6_91)),
% 2.20/0.71    inference(forward_demodulation,[],[f1904,f158])).
% 2.20/0.71  fof(f158,plain,(
% 2.20/0.71    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.20/0.71    inference(superposition,[],[f117,f154])).
% 2.20/0.71  fof(f117,plain,(
% 2.20/0.71    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.20/0.71    inference(definition_unfolding,[],[f81,f76])).
% 2.20/0.71  fof(f81,plain,(
% 2.20/0.71    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.20/0.71    inference(cnf_transformation,[],[f14])).
% 2.20/0.71  fof(f1904,plain,(
% 2.20/0.71    sK0 = k2_relat_1(k1_xboole_0) | (~spl6_80 | ~spl6_91)),
% 2.20/0.71    inference(backward_demodulation,[],[f1204,f1470])).
% 2.20/0.71  fof(f1470,plain,(
% 2.20/0.71    k1_xboole_0 = sK3 | ~spl6_91),
% 2.20/0.71    inference(avatar_component_clause,[],[f1468])).
% 2.20/0.71  fof(f1204,plain,(
% 2.20/0.71    sK0 = k2_relat_1(sK3) | ~spl6_80),
% 2.20/0.71    inference(avatar_component_clause,[],[f1202])).
% 2.20/0.71  fof(f69,plain,(
% 2.20/0.71    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.71    inference(cnf_transformation,[],[f51])).
% 2.20/0.71  fof(f51,plain,(
% 2.20/0.71    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.20/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f50,f49])).
% 2.20/0.71  fof(f49,plain,(
% 2.20/0.71    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.20/0.71    introduced(choice_axiom,[])).
% 2.20/0.71  fof(f50,plain,(
% 2.20/0.71    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.20/0.71    introduced(choice_axiom,[])).
% 2.20/0.71  fof(f27,plain,(
% 2.20/0.71    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.20/0.71    inference(flattening,[],[f26])).
% 2.20/0.71  fof(f26,plain,(
% 2.20/0.71    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.20/0.71    inference(ennf_transformation,[],[f25])).
% 2.20/0.71  fof(f25,negated_conjecture,(
% 2.20/0.71    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.20/0.71    inference(negated_conjecture,[],[f24])).
% 2.20/0.71  fof(f24,conjecture,(
% 2.20/0.71    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).
% 2.20/0.71  fof(f1229,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~r1_tarski(X1,k1_relat_1(X0))) )),
% 2.20/0.71    inference(resolution,[],[f147,f99])).
% 2.20/0.71  fof(f99,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f60])).
% 2.20/0.71  fof(f60,plain,(
% 2.20/0.71    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.71    inference(flattening,[],[f59])).
% 2.20/0.71  fof(f59,plain,(
% 2.20/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.20/0.71    inference(nnf_transformation,[],[f4])).
% 2.20/0.71  fof(f4,axiom,(
% 2.20/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.20/0.71  fof(f147,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (r1_tarski(k1_relat_1(X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 2.20/0.71    inference(resolution,[],[f105,f91])).
% 2.20/0.71  fof(f91,plain,(
% 2.20/0.71    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f56])).
% 2.20/0.71  fof(f56,plain,(
% 2.20/0.71    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.20/0.71    inference(nnf_transformation,[],[f35])).
% 2.20/0.71  fof(f35,plain,(
% 2.20/0.71    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.71    inference(ennf_transformation,[],[f8])).
% 2.20/0.71  fof(f8,axiom,(
% 2.20/0.71    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 2.20/0.71  fof(f105,plain,(
% 2.20/0.71    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.71    inference(cnf_transformation,[],[f40])).
% 2.20/0.71  fof(f40,plain,(
% 2.20/0.71    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.71    inference(ennf_transformation,[],[f16])).
% 2.20/0.71  fof(f16,axiom,(
% 2.20/0.71    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.20/0.71  fof(f1885,plain,(
% 2.20/0.71    ~spl6_72 | spl6_91 | ~spl6_65 | ~spl6_80),
% 2.20/0.71    inference(avatar_split_clause,[],[f1852,f1202,f654,f1468,f1051])).
% 2.20/0.71  fof(f1051,plain,(
% 2.20/0.71    spl6_72 <=> v1_relat_1(sK3)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).
% 2.20/0.71  fof(f654,plain,(
% 2.20/0.71    spl6_65 <=> k1_xboole_0 = sK0),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_65])])).
% 2.20/0.71  fof(f1852,plain,(
% 2.20/0.71    k1_xboole_0 != sK0 | k1_xboole_0 = sK3 | ~v1_relat_1(sK3) | ~spl6_80),
% 2.20/0.71    inference(superposition,[],[f84,f1204])).
% 2.20/0.71  fof(f84,plain,(
% 2.20/0.71    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f30])).
% 2.20/0.71  fof(f1884,plain,(
% 2.20/0.71    ~spl6_29 | ~spl6_63 | ~spl6_30 | ~spl6_31 | ~spl6_64 | ~spl6_32 | spl6_1 | spl6_65 | ~spl6_66 | ~spl6_18),
% 2.20/0.71    inference(avatar_split_clause,[],[f1166,f276,f658,f654,f126,f371,f650,f367,f363,f646,f359])).
% 2.20/0.71  fof(f359,plain,(
% 2.20/0.71    spl6_29 <=> v1_funct_1(sK2)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 2.20/0.71  fof(f646,plain,(
% 2.20/0.71    spl6_63 <=> v1_funct_2(sK2,sK0,sK1)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 2.20/0.71  fof(f363,plain,(
% 2.20/0.71    spl6_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 2.20/0.71  fof(f367,plain,(
% 2.20/0.71    spl6_31 <=> v1_funct_1(sK3)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 2.20/0.71  fof(f650,plain,(
% 2.20/0.71    spl6_64 <=> v1_funct_2(sK3,sK1,sK0)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 2.20/0.71  fof(f371,plain,(
% 2.20/0.71    spl6_32 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 2.20/0.71  fof(f658,plain,(
% 2.20/0.71    spl6_66 <=> v2_funct_1(k6_partfun1(sK0))),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_66])])).
% 2.20/0.71  fof(f276,plain,(
% 2.20/0.71    spl6_18 <=> k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 2.20/0.71  fof(f1166,plain,(
% 2.20/0.71    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl6_18),
% 2.20/0.71    inference(superposition,[],[f107,f278])).
% 2.20/0.71  fof(f278,plain,(
% 2.20/0.71    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~spl6_18),
% 2.20/0.71    inference(avatar_component_clause,[],[f276])).
% 2.20/0.71  fof(f107,plain,(
% 2.20/0.71    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f42])).
% 2.20/0.71  fof(f42,plain,(
% 2.20/0.71    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.20/0.71    inference(flattening,[],[f41])).
% 2.20/0.71  fof(f41,plain,(
% 2.20/0.71    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.20/0.71    inference(ennf_transformation,[],[f23])).
% 2.20/0.71  fof(f23,axiom,(
% 2.20/0.71    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).
% 2.20/0.71  fof(f1882,plain,(
% 2.20/0.71    spl6_105),
% 2.20/0.71    inference(avatar_contradiction_clause,[],[f1879])).
% 2.20/0.71  fof(f1879,plain,(
% 2.20/0.71    $false | spl6_105),
% 2.20/0.71    inference(resolution,[],[f1872,f120])).
% 2.20/0.71  fof(f120,plain,(
% 2.20/0.71    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.20/0.71    inference(equality_resolution,[],[f98])).
% 2.20/0.71  fof(f98,plain,(
% 2.20/0.71    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.20/0.71    inference(cnf_transformation,[],[f60])).
% 2.20/0.71  fof(f1872,plain,(
% 2.20/0.71    ~r1_tarski(sK0,sK0) | spl6_105),
% 2.20/0.71    inference(avatar_component_clause,[],[f1870])).
% 2.20/0.71  fof(f1870,plain,(
% 2.20/0.71    spl6_105 <=> r1_tarski(sK0,sK0)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 2.20/0.71  fof(f1873,plain,(
% 2.20/0.71    ~spl6_72 | ~spl6_105 | ~spl6_80 | spl6_104),
% 2.20/0.71    inference(avatar_split_clause,[],[f1868,f1862,f1202,f1870,f1051])).
% 2.20/0.71  fof(f1862,plain,(
% 2.20/0.71    spl6_104 <=> v5_relat_1(sK3,sK0)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 2.20/0.71  fof(f1868,plain,(
% 2.20/0.71    ~r1_tarski(sK0,sK0) | ~v1_relat_1(sK3) | (~spl6_80 | spl6_104)),
% 2.20/0.71    inference(forward_demodulation,[],[f1867,f1204])).
% 2.20/0.71  fof(f1867,plain,(
% 2.20/0.71    ~r1_tarski(k2_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | spl6_104),
% 2.20/0.71    inference(resolution,[],[f1864,f94])).
% 2.20/0.71  fof(f94,plain,(
% 2.20/0.71    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f57])).
% 2.20/0.71  fof(f57,plain,(
% 2.20/0.71    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.20/0.71    inference(nnf_transformation,[],[f36])).
% 2.20/0.71  fof(f36,plain,(
% 2.20/0.71    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.20/0.71    inference(ennf_transformation,[],[f9])).
% 2.20/0.71  fof(f9,axiom,(
% 2.20/0.71    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.20/0.71    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 2.20/0.71  fof(f1864,plain,(
% 2.20/0.71    ~v5_relat_1(sK3,sK0) | spl6_104),
% 2.20/0.71    inference(avatar_component_clause,[],[f1862])).
% 2.20/0.71  fof(f1865,plain,(
% 2.20/0.71    ~spl6_72 | ~spl6_104 | spl6_2 | ~spl6_80),
% 2.20/0.71    inference(avatar_split_clause,[],[f1851,f1202,f130,f1862,f1051])).
% 2.20/0.71  fof(f130,plain,(
% 2.20/0.71    spl6_2 <=> v2_funct_2(sK3,sK0)),
% 2.20/0.71    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 2.20/0.71  fof(f1851,plain,(
% 2.20/0.71    v2_funct_2(sK3,sK0) | ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl6_80),
% 2.20/0.71    inference(superposition,[],[f119,f1204])).
% 2.20/0.71  fof(f119,plain,(
% 2.20/0.71    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.20/0.71    inference(equality_resolution,[],[f96])).
% 2.20/0.71  fof(f96,plain,(
% 2.20/0.71    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.20/0.71    inference(cnf_transformation,[],[f58])).
% 2.20/0.72  fof(f58,plain,(
% 2.20/0.72    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.72    inference(nnf_transformation,[],[f38])).
% 2.20/0.72  fof(f38,plain,(
% 2.20/0.72    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.20/0.72    inference(flattening,[],[f37])).
% 2.20/0.72  fof(f37,plain,(
% 2.20/0.72    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.20/0.72    inference(ennf_transformation,[],[f19])).
% 2.20/0.72  fof(f19,axiom,(
% 2.20/0.72    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).
% 2.20/0.72  fof(f1822,plain,(
% 2.20/0.72    ~spl6_79 | spl6_80 | ~spl6_78),
% 2.20/0.72    inference(avatar_split_clause,[],[f1770,f1189,f1202,f1198])).
% 2.20/0.72  fof(f1198,plain,(
% 2.20/0.72    spl6_79 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 2.20/0.72  fof(f1189,plain,(
% 2.20/0.72    spl6_78 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 2.20/0.72  fof(f1770,plain,(
% 2.20/0.72    sK0 = k2_relat_1(sK3) | ~r1_tarski(k2_relat_1(sK3),sK0) | ~spl6_78),
% 2.20/0.72    inference(resolution,[],[f1191,f99])).
% 2.20/0.72  fof(f1191,plain,(
% 2.20/0.72    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl6_78),
% 2.20/0.72    inference(avatar_component_clause,[],[f1189])).
% 2.20/0.72  fof(f1821,plain,(
% 2.20/0.72    ~spl6_84),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f1819])).
% 2.20/0.72  fof(f1819,plain,(
% 2.20/0.72    $false | ~spl6_84),
% 2.20/0.72    inference(resolution,[],[f1259,f72])).
% 2.20/0.72  fof(f72,plain,(
% 2.20/0.72    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f1259,plain,(
% 2.20/0.72    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | ~spl6_84),
% 2.20/0.72    inference(avatar_component_clause,[],[f1258])).
% 2.20/0.72  fof(f1258,plain,(
% 2.20/0.72    spl6_84 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 2.20/0.72  fof(f1260,plain,(
% 2.20/0.72    ~spl6_72 | spl6_84 | spl6_79),
% 2.20/0.72    inference(avatar_split_clause,[],[f1252,f1198,f1258,f1051])).
% 2.20/0.72  fof(f1252,plain,(
% 2.20/0.72    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) | ~v1_relat_1(sK3)) ) | spl6_79),
% 2.20/0.72    inference(resolution,[],[f148,f1200])).
% 2.20/0.72  fof(f1200,plain,(
% 2.20/0.72    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_79),
% 2.20/0.72    inference(avatar_component_clause,[],[f1198])).
% 2.20/0.72  fof(f148,plain,(
% 2.20/0.72    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_relat_1(X0)) )),
% 2.20/0.72    inference(resolution,[],[f106,f93])).
% 2.20/0.72  fof(f93,plain,(
% 2.20/0.72    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.20/0.72    inference(cnf_transformation,[],[f57])).
% 2.20/0.72  fof(f106,plain,(
% 2.20/0.72    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f40])).
% 2.20/0.72  fof(f1192,plain,(
% 2.20/0.72    ~spl6_71 | ~spl6_72 | spl6_78 | ~spl6_41),
% 2.20/0.72    inference(avatar_split_clause,[],[f1187,f440,f1189,f1051,f1047])).
% 2.20/0.72  fof(f440,plain,(
% 2.20/0.72    spl6_41 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 2.20/0.72  fof(f1187,plain,(
% 2.20/0.72    r1_tarski(sK0,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_41),
% 2.20/0.72    inference(forward_demodulation,[],[f1169,f117])).
% 2.20/0.72  fof(f1169,plain,(
% 2.20/0.72    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl6_41),
% 2.20/0.72    inference(superposition,[],[f85,f442])).
% 2.20/0.72  fof(f442,plain,(
% 2.20/0.72    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl6_41),
% 2.20/0.72    inference(avatar_component_clause,[],[f440])).
% 2.20/0.72  fof(f85,plain,(
% 2.20/0.72    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.20/0.72    inference(cnf_transformation,[],[f31])).
% 2.20/0.72  fof(f31,plain,(
% 2.20/0.72    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.20/0.72    inference(ennf_transformation,[],[f12])).
% 2.20/0.72  fof(f12,axiom,(
% 2.20/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).
% 2.20/0.72  fof(f1186,plain,(
% 2.20/0.72    spl6_72),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f1184])).
% 2.20/0.72  fof(f1184,plain,(
% 2.20/0.72    $false | spl6_72),
% 2.20/0.72    inference(resolution,[],[f1182,f90])).
% 2.20/0.72  fof(f90,plain,(
% 2.20/0.72    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f10])).
% 2.20/0.72  fof(f10,axiom,(
% 2.20/0.72    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.20/0.72  fof(f1182,plain,(
% 2.20/0.72    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl6_72),
% 2.20/0.72    inference(resolution,[],[f1060,f72])).
% 2.20/0.72  fof(f1060,plain,(
% 2.20/0.72    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_72),
% 2.20/0.72    inference(resolution,[],[f1053,f86])).
% 2.20/0.72  fof(f86,plain,(
% 2.20/0.72    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.20/0.72    inference(cnf_transformation,[],[f32])).
% 2.20/0.72  fof(f32,plain,(
% 2.20/0.72    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.20/0.72    inference(ennf_transformation,[],[f7])).
% 2.20/0.72  fof(f7,axiom,(
% 2.20/0.72    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.20/0.72  fof(f1053,plain,(
% 2.20/0.72    ~v1_relat_1(sK3) | spl6_72),
% 2.20/0.72    inference(avatar_component_clause,[],[f1051])).
% 2.20/0.72  fof(f1181,plain,(
% 2.20/0.72    spl6_71),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f1179])).
% 2.20/0.72  fof(f1179,plain,(
% 2.20/0.72    $false | spl6_71),
% 2.20/0.72    inference(resolution,[],[f1177,f90])).
% 2.20/0.72  fof(f1177,plain,(
% 2.20/0.72    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_71),
% 2.20/0.72    inference(resolution,[],[f1059,f69])).
% 2.20/0.72  fof(f1059,plain,(
% 2.20/0.72    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_71),
% 2.20/0.72    inference(resolution,[],[f1049,f86])).
% 2.20/0.72  fof(f1049,plain,(
% 2.20/0.72    ~v1_relat_1(sK2) | spl6_71),
% 2.20/0.72    inference(avatar_component_clause,[],[f1047])).
% 2.20/0.72  fof(f694,plain,(
% 2.20/0.72    spl6_64),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f693])).
% 2.20/0.72  fof(f693,plain,(
% 2.20/0.72    $false | spl6_64),
% 2.20/0.72    inference(resolution,[],[f652,f71])).
% 2.20/0.72  fof(f71,plain,(
% 2.20/0.72    v1_funct_2(sK3,sK1,sK0)),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f652,plain,(
% 2.20/0.72    ~v1_funct_2(sK3,sK1,sK0) | spl6_64),
% 2.20/0.72    inference(avatar_component_clause,[],[f650])).
% 2.20/0.72  fof(f692,plain,(
% 2.20/0.72    spl6_63),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f691])).
% 2.20/0.72  fof(f691,plain,(
% 2.20/0.72    $false | spl6_63),
% 2.20/0.72    inference(resolution,[],[f648,f68])).
% 2.20/0.72  fof(f68,plain,(
% 2.20/0.72    v1_funct_2(sK2,sK0,sK1)),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f648,plain,(
% 2.20/0.72    ~v1_funct_2(sK2,sK0,sK1) | spl6_63),
% 2.20/0.72    inference(avatar_component_clause,[],[f646])).
% 2.20/0.72  fof(f686,plain,(
% 2.20/0.72    spl6_66),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f685])).
% 2.20/0.72  fof(f685,plain,(
% 2.20/0.72    $false | spl6_66),
% 2.20/0.72    inference(resolution,[],[f660,f115])).
% 2.20/0.72  fof(f660,plain,(
% 2.20/0.72    ~v2_funct_1(k6_partfun1(sK0)) | spl6_66),
% 2.20/0.72    inference(avatar_component_clause,[],[f658])).
% 2.20/0.72  fof(f639,plain,(
% 2.20/0.72    ~spl6_29 | ~spl6_30 | ~spl6_31 | ~spl6_32 | spl6_41 | ~spl6_18),
% 2.20/0.72    inference(avatar_split_clause,[],[f635,f276,f440,f371,f367,f363,f359])).
% 2.20/0.72  fof(f635,plain,(
% 2.20/0.72    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl6_18),
% 2.20/0.72    inference(superposition,[],[f111,f278])).
% 2.20/0.72  fof(f111,plain,(
% 2.20/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.20/0.72    inference(cnf_transformation,[],[f46])).
% 2.20/0.72  fof(f46,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.72    inference(flattening,[],[f45])).
% 2.20/0.72  fof(f45,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.72    inference(ennf_transformation,[],[f21])).
% 2.20/0.72  fof(f21,axiom,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.20/0.72  fof(f573,plain,(
% 2.20/0.72    ~spl6_29 | ~spl6_30 | ~spl6_31 | ~spl6_32 | spl6_16),
% 2.20/0.72    inference(avatar_split_clause,[],[f570,f268,f371,f367,f363,f359])).
% 2.20/0.72  fof(f268,plain,(
% 2.20/0.72    spl6_16 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 2.20/0.72  fof(f570,plain,(
% 2.20/0.72    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl6_16),
% 2.20/0.72    inference(resolution,[],[f270,f113])).
% 2.20/0.72  fof(f113,plain,(
% 2.20/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.20/0.72    inference(cnf_transformation,[],[f48])).
% 2.20/0.72  fof(f48,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.20/0.72    inference(flattening,[],[f47])).
% 2.20/0.72  fof(f47,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.20/0.72    inference(ennf_transformation,[],[f20])).
% 2.20/0.72  fof(f20,axiom,(
% 2.20/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.20/0.72  fof(f270,plain,(
% 2.20/0.72    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_16),
% 2.20/0.72    inference(avatar_component_clause,[],[f268])).
% 2.20/0.72  fof(f404,plain,(
% 2.20/0.72    spl6_32),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f402])).
% 2.20/0.72  fof(f402,plain,(
% 2.20/0.72    $false | spl6_32),
% 2.20/0.72    inference(resolution,[],[f373,f72])).
% 2.20/0.72  fof(f373,plain,(
% 2.20/0.72    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_32),
% 2.20/0.72    inference(avatar_component_clause,[],[f371])).
% 2.20/0.72  fof(f401,plain,(
% 2.20/0.72    spl6_30),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f399])).
% 2.20/0.72  fof(f399,plain,(
% 2.20/0.72    $false | spl6_30),
% 2.20/0.72    inference(resolution,[],[f365,f69])).
% 2.20/0.72  fof(f365,plain,(
% 2.20/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl6_30),
% 2.20/0.72    inference(avatar_component_clause,[],[f363])).
% 2.20/0.72  fof(f382,plain,(
% 2.20/0.72    spl6_31),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f381])).
% 2.20/0.72  fof(f381,plain,(
% 2.20/0.72    $false | spl6_31),
% 2.20/0.72    inference(resolution,[],[f369,f70])).
% 2.20/0.72  fof(f70,plain,(
% 2.20/0.72    v1_funct_1(sK3)),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f369,plain,(
% 2.20/0.72    ~v1_funct_1(sK3) | spl6_31),
% 2.20/0.72    inference(avatar_component_clause,[],[f367])).
% 2.20/0.72  fof(f380,plain,(
% 2.20/0.72    spl6_29),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f379])).
% 2.20/0.72  fof(f379,plain,(
% 2.20/0.72    $false | spl6_29),
% 2.20/0.72    inference(resolution,[],[f361,f67])).
% 2.20/0.72  fof(f67,plain,(
% 2.20/0.72    v1_funct_1(sK2)),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f361,plain,(
% 2.20/0.72    ~v1_funct_1(sK2) | spl6_29),
% 2.20/0.72    inference(avatar_component_clause,[],[f359])).
% 2.20/0.72  fof(f308,plain,(
% 2.20/0.72    spl6_17),
% 2.20/0.72    inference(avatar_contradiction_clause,[],[f306])).
% 2.20/0.72  fof(f306,plain,(
% 2.20/0.72    $false | spl6_17),
% 2.20/0.72    inference(resolution,[],[f274,f114])).
% 2.20/0.72  fof(f114,plain,(
% 2.20/0.72    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.72    inference(definition_unfolding,[],[f77,f76])).
% 2.20/0.72  fof(f77,plain,(
% 2.20/0.72    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f18])).
% 2.20/0.72  fof(f18,axiom,(
% 2.20/0.72    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.20/0.72  fof(f274,plain,(
% 2.20/0.72    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl6_17),
% 2.20/0.72    inference(avatar_component_clause,[],[f272])).
% 2.20/0.72  fof(f272,plain,(
% 2.20/0.72    spl6_17 <=> m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.72    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 2.20/0.72  fof(f279,plain,(
% 2.20/0.72    ~spl6_16 | ~spl6_17 | spl6_18),
% 2.20/0.72    inference(avatar_split_clause,[],[f264,f276,f272,f268])).
% 2.20/0.72  fof(f264,plain,(
% 2.20/0.72    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.20/0.72    inference(resolution,[],[f109,f73])).
% 2.20/0.72  fof(f73,plain,(
% 2.20/0.72    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  fof(f109,plain,(
% 2.20/0.72    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.20/0.72    inference(cnf_transformation,[],[f66])).
% 2.20/0.72  fof(f66,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.72    inference(nnf_transformation,[],[f44])).
% 2.20/0.72  fof(f44,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.20/0.72    inference(flattening,[],[f43])).
% 2.20/0.72  fof(f43,plain,(
% 2.20/0.72    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.20/0.72    inference(ennf_transformation,[],[f17])).
% 2.20/0.72  fof(f17,axiom,(
% 2.20/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.20/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.20/0.72  fof(f133,plain,(
% 2.20/0.72    ~spl6_1 | ~spl6_2),
% 2.20/0.72    inference(avatar_split_clause,[],[f74,f130,f126])).
% 2.20/0.72  fof(f74,plain,(
% 2.20/0.72    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 2.20/0.72    inference(cnf_transformation,[],[f51])).
% 2.20/0.72  % SZS output end Proof for theBenchmark
% 2.20/0.72  % (4006)------------------------------
% 2.20/0.72  % (4006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.72  % (4006)Termination reason: Refutation
% 2.20/0.72  
% 2.20/0.72  % (4006)Memory used [KB]: 7291
% 2.20/0.72  % (4006)Time elapsed: 0.292 s
% 2.20/0.72  % (4006)------------------------------
% 2.20/0.72  % (4006)------------------------------
% 2.20/0.72  % (3993)Success in time 0.344 s
%------------------------------------------------------------------------------
