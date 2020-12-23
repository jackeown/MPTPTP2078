%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:57:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 160 expanded)
%              Number of leaves         :   23 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :  236 ( 458 expanded)
%              Number of equality atoms :   49 (  98 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f97,f110,f148,f150,f152,f162,f171,f184,f268])).

fof(f268,plain,(
    ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | ~ spl4_9 ),
    inference(trivial_inequality_removal,[],[f264])).

fof(f264,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_9 ),
    inference(superposition,[],[f197,f255])).

fof(f255,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = k2_relat_1(X0) ) ),
    inference(resolution,[],[f41,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f41,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).

fof(f197,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | ~ spl4_9 ),
    inference(backward_demodulation,[],[f167,f109])).

fof(f109,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_9
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f167,plain,(
    k1_xboole_0 != k2_relat_1(sK2) ),
    inference(superposition,[],[f33,f111])).

fof(f111,plain,(
    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f51,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r2_hidden(X3,k1_relset_1(X1,X0,X2))
                  | ~ m1_subset_1(X3,X1) )
              & k1_xboole_0 != k2_relset_1(X1,X0,X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f33,plain,(
    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f184,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f183,f61,f68,f108])).

fof(f68,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f61,plain,
    ( spl4_2
  <=> v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f183,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_2 ),
    inference(superposition,[],[f37,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f176,f40])).

fof(f176,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f62,f101])).

fof(f101,plain,(
    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f50,f32])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f62,plain,
    ( v1_xboole_0(k1_relset_1(sK1,sK0,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f171,plain,
    ( spl4_1
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f96,f165])).

fof(f165,plain,
    ( ~ r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | spl4_1 ),
    inference(resolution,[],[f163,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f163,plain,
    ( ~ m1_subset_1(sK3(k1_relat_1(sK2)),sK1)
    | spl4_1 ),
    inference(backward_demodulation,[],[f59,f101])).

fof(f59,plain,
    ( ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_1
  <=> m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f96,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl4_8
  <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f162,plain,
    ( ~ spl4_3
    | spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f161,f80,f87,f68])).

fof(f87,plain,
    ( spl4_6
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f80,plain,
    ( spl4_5
  <=> sK2 = k7_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f161,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK2))
        | r2_hidden(X2,sK1)
        | ~ v1_relat_1(sK2) )
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f81])).

fof(f81,plain,
    ( sK2 = k7_relat_1(sK2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).

fof(f152,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f151,f68,f80])).

fof(f151,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k7_relat_1(sK2,sK1) ),
    inference(resolution,[],[f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f76,plain,(
    v4_relat_1(sK2,sK1) ),
    inference(resolution,[],[f52,f32])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f150,plain,
    ( spl4_2
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f149,f58,f61])).

fof(f149,plain,
    ( ~ m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)
    | v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) ),
    inference(resolution,[],[f31,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f31,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_relset_1(sK1,sK0,sK2))
      | ~ m1_subset_1(X3,sK1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f148,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f147,f71,f68])).

fof(f71,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f147,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f110,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f106,f92,f68,f108])).

fof(f92,plain,
    ( spl4_7
  <=> v1_xboole_0(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f105])).

fof(f105,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl4_7 ),
    inference(superposition,[],[f37,f100])).

fof(f100,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(resolution,[],[f93,f40])).

fof(f93,plain,
    ( v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f97,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f90,f87,f95,f92])).

fof(f90,plain,
    ( r2_hidden(sK3(k1_relat_1(sK2)),sK1)
    | v1_xboole_0(k1_relat_1(sK2))
    | ~ spl4_6 ),
    inference(resolution,[],[f88,f42])).

fof(f88,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK2))
        | r2_hidden(X0,sK1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f75,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f74])).

fof(f74,plain,
    ( $false
    | spl4_4 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f72,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f71])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:07:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (10004)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (10005)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (10001)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (10007)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.51  % (10020)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (10021)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (10017)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (10014)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (10006)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (10018)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.51  % (10004)Refutation not found, incomplete strategy% (10004)------------------------------
% 0.22/0.51  % (10004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (10024)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (10002)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (10022)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (10012)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (10004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10004)Memory used [KB]: 10618
% 0.22/0.52  % (10015)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (10004)Time elapsed: 0.092 s
% 0.22/0.52  % (10004)------------------------------
% 0.22/0.52  % (10004)------------------------------
% 0.22/0.52  % (10016)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (10009)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (10013)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (10009)Refutation not found, incomplete strategy% (10009)------------------------------
% 0.22/0.52  % (10009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (10009)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (10009)Memory used [KB]: 10618
% 0.22/0.52  % (10009)Time elapsed: 0.106 s
% 0.22/0.52  % (10009)------------------------------
% 0.22/0.52  % (10009)------------------------------
% 0.22/0.53  % (10013)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f269,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f75,f97,f110,f148,f150,f152,f162,f171,f184,f268])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    ~spl4_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f267])).
% 0.22/0.53  fof(f267,plain,(
% 0.22/0.53    $false | ~spl4_9),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f264])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~spl4_9),
% 0.22/0.53    inference(superposition,[],[f197,f255])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.22/0.53    inference(resolution,[],[f54,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    v1_xboole_0(k1_xboole_0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_relat_1(X0)) )),
% 0.22/0.53    inference(resolution,[],[f41,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_relat_1)).
% 0.22/0.53  fof(f197,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | ~spl4_9),
% 0.22/0.53    inference(backward_demodulation,[],[f167,f109])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    k1_xboole_0 = sK2 | ~spl4_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl4_9 <=> k1_xboole_0 = sK2),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relat_1(sK2)),
% 0.22/0.53    inference(superposition,[],[f33,f111])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    k2_relset_1(sK1,sK0,sK2) = k2_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f51,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : (~r2_hidden(X3,k1_relset_1(X1,X0,X2)) | ~m1_subset_1(X3,X1)) & k1_xboole_0 != k2_relset_1(X1,X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => ~(! [X3] : (m1_subset_1(X3,X1) => ~r2_hidden(X3,k1_relset_1(X1,X0,X2))) & k1_xboole_0 != k2_relset_1(X1,X0,X2)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_relset_1)).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    k1_xboole_0 != k2_relset_1(sK1,sK0,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f184,plain,(
% 0.22/0.53    spl4_9 | ~spl4_3 | ~spl4_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f183,f61,f68,f108])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    spl4_3 <=> v1_relat_1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    spl4_2 <=> v1_xboole_0(k1_relset_1(sK1,sK0,sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.53  fof(f183,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_2),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_2),
% 0.22/0.53    inference(superposition,[],[f37,f177])).
% 0.22/0.53  fof(f177,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_2),
% 0.22/0.53    inference(resolution,[],[f176,f40])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    v1_xboole_0(k1_relat_1(sK2)) | ~spl4_2),
% 0.22/0.53    inference(forward_demodulation,[],[f62,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    k1_relset_1(sK1,sK0,sK2) = k1_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f50,f32])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    v1_xboole_0(k1_relset_1(sK1,sK0,sK2)) | ~spl4_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f61])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(flattening,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.22/0.53  fof(f171,plain,(
% 0.22/0.53    spl4_1 | ~spl4_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f169])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    $false | (spl4_1 | ~spl4_8)),
% 0.22/0.53    inference(resolution,[],[f96,f165])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~r2_hidden(sK3(k1_relat_1(sK2)),sK1) | spl4_1),
% 0.22/0.53    inference(resolution,[],[f163,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.53  fof(f163,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_relat_1(sK2)),sK1) | spl4_1),
% 0.22/0.53    inference(backward_demodulation,[],[f59,f101])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) | spl4_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f58])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    spl4_1 <=> m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    r2_hidden(sK3(k1_relat_1(sK2)),sK1) | ~spl4_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f95])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    spl4_8 <=> r2_hidden(sK3(k1_relat_1(sK2)),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    ~spl4_3 | spl4_6 | ~spl4_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f161,f80,f87,f68])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    spl4_6 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl4_5 <=> sK2 = k7_relat_1(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK2)) | r2_hidden(X2,sK1) | ~v1_relat_1(sK2)) ) | ~spl4_5),
% 0.22/0.53    inference(superposition,[],[f47,f81])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    sK2 = k7_relat_1(sK2,sK1) | ~spl4_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f80])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_relat_1)).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    spl4_5 | ~spl4_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f151,f68,f80])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | sK2 = k7_relat_1(sK2,sK1)),
% 0.22/0.53    inference(resolution,[],[f76,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.53    inference(flattening,[],[f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    v4_relat_1(sK2,sK1)),
% 0.22/0.53    inference(resolution,[],[f52,f32])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.53    inference(ennf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.22/0.53    inference(pure_predicate_removal,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    spl4_2 | ~spl4_1),
% 0.22/0.53    inference(avatar_split_clause,[],[f149,f58,f61])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(k1_relset_1(sK1,sK0,sK2)),sK1) | v1_xboole_0(k1_relset_1(sK1,sK0,sK2))),
% 0.22/0.53    inference(resolution,[],[f31,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(X3,k1_relset_1(sK1,sK0,sK2)) | ~m1_subset_1(X3,sK1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f148,plain,(
% 0.22/0.53    spl4_3 | ~spl4_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f147,f71,f68])).
% 0.22/0.53  fof(f71,plain,(
% 0.22/0.53    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.53  fof(f147,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK2)),
% 0.22/0.53    inference(resolution,[],[f32,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    spl4_9 | ~spl4_3 | ~spl4_7),
% 0.22/0.53    inference(avatar_split_clause,[],[f106,f92,f68,f108])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl4_7 <=> v1_xboole_0(k1_relat_1(sK2))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_7),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | ~spl4_7),
% 0.22/0.53    inference(superposition,[],[f37,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_7),
% 0.22/0.53    inference(resolution,[],[f93,f40])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    v1_xboole_0(k1_relat_1(sK2)) | ~spl4_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    spl4_7 | spl4_8 | ~spl4_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f90,f87,f95,f92])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    r2_hidden(sK3(k1_relat_1(sK2)),sK1) | v1_xboole_0(k1_relat_1(sK2)) | ~spl4_6),
% 0.22/0.53    inference(resolution,[],[f88,f42])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK2)) | r2_hidden(X0,sK1)) ) | ~spl4_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f87])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    spl4_4),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    $false | spl4_4),
% 0.22/0.53    inference(resolution,[],[f72,f44])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_4),
% 0.22/0.53    inference(avatar_component_clause,[],[f71])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (10013)------------------------------
% 0.22/0.53  % (10013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (10013)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (10013)Memory used [KB]: 10618
% 0.22/0.53  % (10013)Time elapsed: 0.112 s
% 0.22/0.53  % (10013)------------------------------
% 0.22/0.53  % (10013)------------------------------
% 0.22/0.53  % (10008)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (10000)Success in time 0.164 s
%------------------------------------------------------------------------------
