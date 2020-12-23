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
% DateTime   : Thu Dec  3 13:06:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 304 expanded)
%              Number of leaves         :   12 ( 104 expanded)
%              Depth                    :   14
%              Number of atoms          :  339 (2066 expanded)
%              Number of equality atoms :   38 (  82 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f152,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f54,f84,f85,f104,f134,f147])).

fof(f147,plain,(
    ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f139,f33])).

fof(f33,plain,(
    r2_relset_1(sK0,sK0,sK1,sK1) ),
    inference(resolution,[],[f30,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
    & r1_partfun1(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X1,X2)
            & r1_partfun1(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,sK1,X2)
          & r1_partfun1(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2] :
        ( ~ r2_relset_1(sK0,sK0,sK1,X2)
        & r1_partfun1(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        & v1_funct_2(X2,sK0,sK0)
        & v1_funct_1(X2) )
   => ( ~ r2_relset_1(sK0,sK0,sK1,sK2)
      & r1_partfun1(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK2,sK0,sK0)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X1,X2)
          & r1_partfun1(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( r1_partfun1(X1,X2)
             => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( r1_partfun1(X1,X2)
           => r2_relset_1(X0,X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f13])).

% (18763)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f139,plain,
    ( ~ r2_relset_1(sK0,sK0,sK1,sK1)
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f24,f97])).

fof(f97,plain,
    ( sK1 = sK2
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f24,plain,(
    ~ r2_relset_1(sK0,sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f134,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f133,f51,f40,f95])).

fof(f40,plain,
    ( spl3_1
  <=> v1_partfun1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f51,plain,
    ( spl3_3
  <=> v1_partfun1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f133,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f132,f17])).

fof(f17,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

% (18765)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
fof(f132,plain,
    ( sK1 = sK2
    | ~ v1_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f131,f23])).

fof(f23,plain,(
    r1_partfun1(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f131,plain,
    ( sK1 = sK2
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f129,f42])).

fof(f42,plain,
    ( v1_partfun1(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f129,plain,
    ( ~ v1_partfun1(sK1,sK0)
    | sK1 = sK2
    | ~ r1_partfun1(sK1,sK2)
    | ~ v1_funct_1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f126,f19])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_partfun1(X0,sK0)
        | sK2 = X0
        | ~ r1_partfun1(X0,sK2)
        | ~ v1_funct_1(X0) )
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f125,f20])).

fof(f20,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ r1_partfun1(X0,sK2)
        | ~ v1_partfun1(X0,sK0)
        | sK2 = X0
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
        | ~ v1_funct_1(X0) )
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f122,f53])).

fof(f53,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_partfun1(X0,sK2)
      | ~ v1_partfun1(sK2,sK0)
      | ~ v1_partfun1(X0,sK0)
      | sK2 = X0
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f22,f27])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f104,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f103,f82,f44,f95])).

fof(f44,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f82,plain,
    ( spl3_5
  <=> ! [X1] :
        ( ~ r1_partfun1(X1,sK2)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | sK2 = X1
        | ~ v1_partfun1(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f103,plain,
    ( sK1 = sK2
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f102,f66])).

fof(f66,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f65,f17])).

fof(f65,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f62,f55])).

fof(f55,plain,
    ( v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f18,f46])).

fof(f46,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f18,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,
    ( v1_partfun1(sK1,k1_xboole_0)
    | ~ v1_funct_2(sK1,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_partfun1(X2,k1_xboole_0)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f29])).

fof(f29,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f56,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f19,f46])).

fof(f102,plain,
    ( sK1 = sK2
    | ~ v1_partfun1(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f101,f23])).

fof(f101,plain,
    ( ~ r1_partfun1(sK1,sK2)
    | sK1 = sK2
    | ~ v1_partfun1(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f99,f17])).

fof(f99,plain,
    ( ~ v1_funct_1(sK1)
    | ~ r1_partfun1(sK1,sK2)
    | sK1 = sK2
    | ~ v1_partfun1(sK1,k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f83,f56])).

fof(f83,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK2)
        | sK2 = X1
        | ~ v1_partfun1(X1,k1_xboole_0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f85,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f71,f44,f78])).

fof(f78,plain,
    ( spl3_4
  <=> v1_partfun1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f70,f20])).

fof(f70,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f67,f57])).

fof(f57,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f21,f46])).

fof(f21,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,
    ( v1_partfun1(sK2,k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f58,f32])).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f22,f46])).

fof(f84,plain,
    ( ~ spl3_4
    | spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f76,f44,f82,f78])).

fof(f76,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK2)
        | ~ v1_partfun1(sK2,k1_xboole_0)
        | ~ v1_partfun1(X1,k1_xboole_0)
        | sK2 = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1) )
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f73,f20])).

fof(f73,plain,
    ( ! [X1] :
        ( ~ r1_partfun1(X1,sK2)
        | ~ v1_partfun1(sK2,k1_xboole_0)
        | ~ v1_partfun1(X1,k1_xboole_0)
        | sK2 = X1
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f27,f58])).

fof(f54,plain,
    ( spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f49,f44,f51])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f48,f20])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f36,f21])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK2,sK0)
    | ~ v1_funct_2(sK2,sK0,sK0)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f31,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f38,f44,f40])).

fof(f38,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f37,f17])).

fof(f37,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK1,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(subsumption_resolution,[],[f35,f18])).

fof(f35,plain,
    ( k1_xboole_0 = sK0
    | v1_partfun1(sK1,sK0)
    | ~ v1_funct_2(sK1,sK0,sK0)
    | ~ v1_funct_1(sK1) ),
    inference(resolution,[],[f31,f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:26:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.53  % (18755)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (18748)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.54  % (18744)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (18746)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.54  % (18747)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.54  % (18755)Refutation not found, incomplete strategy% (18755)------------------------------
% 0.22/0.54  % (18755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (18755)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (18755)Memory used [KB]: 6140
% 0.22/0.54  % (18755)Time elapsed: 0.113 s
% 0.22/0.54  % (18755)------------------------------
% 0.22/0.54  % (18755)------------------------------
% 0.22/0.54  % (18748)Refutation not found, incomplete strategy% (18748)------------------------------
% 0.22/0.54  % (18748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18756)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.55  % (18748)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18748)Memory used [KB]: 10490
% 0.22/0.55  % (18748)Time elapsed: 0.114 s
% 0.22/0.55  % (18748)------------------------------
% 0.22/0.55  % (18748)------------------------------
% 0.22/0.55  % (18746)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % SZS output start Proof for theBenchmark
% 0.22/0.55  fof(f152,plain,(
% 0.22/0.55    $false),
% 0.22/0.55    inference(avatar_sat_refutation,[],[f47,f54,f84,f85,f104,f134,f147])).
% 0.22/0.55  fof(f147,plain,(
% 0.22/0.55    ~spl3_7),
% 0.22/0.55    inference(avatar_contradiction_clause,[],[f146])).
% 0.22/0.55  fof(f146,plain,(
% 0.22/0.55    $false | ~spl3_7),
% 0.22/0.55    inference(subsumption_resolution,[],[f139,f33])).
% 0.22/0.55  fof(f33,plain,(
% 0.22/0.55    r2_relset_1(sK0,sK0,sK1,sK1)),
% 0.22/0.55    inference(resolution,[],[f30,f19])).
% 0.22/0.55  fof(f19,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f16,plain,(
% 0.22/0.55    (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 0.22/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f15,f14])).
% 0.22/0.55  fof(f14,plain,(
% 0.22/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f15,plain,(
% 0.22/0.55    ? [X2] : (~r2_relset_1(sK0,sK0,sK1,X2) & r1_partfun1(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) => (~r2_relset_1(sK0,sK0,sK1,sK2) & r1_partfun1(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2))),
% 0.22/0.55    introduced(choice_axiom,[])).
% 0.22/0.55  fof(f7,plain,(
% 0.22/0.55    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.22/0.55    inference(flattening,[],[f6])).
% 0.22/0.55  fof(f6,plain,(
% 0.22/0.55    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X1,X2) & r1_partfun1(X1,X2)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.22/0.55    inference(ennf_transformation,[],[f5])).
% 0.22/0.55  fof(f5,negated_conjecture,(
% 0.22/0.55    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.22/0.55    inference(negated_conjecture,[],[f4])).
% 0.22/0.55  fof(f4,conjecture,(
% 0.22/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (r1_partfun1(X1,X2) => r2_relset_1(X0,X0,X1,X2))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_funct_2)).
% 0.22/0.55  fof(f30,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.22/0.55    inference(condensation,[],[f28])).
% 0.22/0.55  fof(f28,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f13])).
% 0.22/0.55  % (18763)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.55  fof(f13,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.55    inference(flattening,[],[f12])).
% 0.22/0.55  fof(f12,plain,(
% 0.22/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.55    inference(ennf_transformation,[],[f1])).
% 0.22/0.55  fof(f1,axiom,(
% 0.22/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.22/0.55  fof(f139,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,sK1,sK1) | ~spl3_7),
% 0.22/0.55    inference(backward_demodulation,[],[f24,f97])).
% 0.22/0.55  fof(f97,plain,(
% 0.22/0.55    sK1 = sK2 | ~spl3_7),
% 0.22/0.55    inference(avatar_component_clause,[],[f95])).
% 0.22/0.55  fof(f95,plain,(
% 0.22/0.55    spl3_7 <=> sK1 = sK2),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.55  fof(f24,plain,(
% 0.22/0.55    ~r2_relset_1(sK0,sK0,sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f134,plain,(
% 0.22/0.55    spl3_7 | ~spl3_1 | ~spl3_3),
% 0.22/0.55    inference(avatar_split_clause,[],[f133,f51,f40,f95])).
% 0.22/0.55  fof(f40,plain,(
% 0.22/0.55    spl3_1 <=> v1_partfun1(sK1,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.55  fof(f51,plain,(
% 0.22/0.55    spl3_3 <=> v1_partfun1(sK2,sK0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.55  fof(f133,plain,(
% 0.22/0.55    sK1 = sK2 | (~spl3_1 | ~spl3_3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f132,f17])).
% 0.22/0.55  fof(f17,plain,(
% 0.22/0.55    v1_funct_1(sK1)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  % (18765)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.55  fof(f132,plain,(
% 0.22/0.55    sK1 = sK2 | ~v1_funct_1(sK1) | (~spl3_1 | ~spl3_3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f131,f23])).
% 0.22/0.55  fof(f23,plain,(
% 0.22/0.55    r1_partfun1(sK1,sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f131,plain,(
% 0.22/0.55    sK1 = sK2 | ~r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | (~spl3_1 | ~spl3_3)),
% 0.22/0.55    inference(subsumption_resolution,[],[f129,f42])).
% 0.22/0.55  fof(f42,plain,(
% 0.22/0.55    v1_partfun1(sK1,sK0) | ~spl3_1),
% 0.22/0.55    inference(avatar_component_clause,[],[f40])).
% 0.22/0.55  fof(f129,plain,(
% 0.22/0.55    ~v1_partfun1(sK1,sK0) | sK1 = sK2 | ~r1_partfun1(sK1,sK2) | ~v1_funct_1(sK1) | ~spl3_3),
% 0.22/0.55    inference(resolution,[],[f126,f19])).
% 0.22/0.55  fof(f126,plain,(
% 0.22/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_partfun1(X0,sK0) | sK2 = X0 | ~r1_partfun1(X0,sK2) | ~v1_funct_1(X0)) ) | ~spl3_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f125,f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    v1_funct_1(sK2)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f125,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_partfun1(X0,sK2) | ~v1_partfun1(X0,sK0) | sK2 = X0 | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(X0)) ) | ~spl3_3),
% 0.22/0.55    inference(subsumption_resolution,[],[f122,f53])).
% 0.22/0.55  fof(f53,plain,(
% 0.22/0.55    v1_partfun1(sK2,sK0) | ~spl3_3),
% 0.22/0.55    inference(avatar_component_clause,[],[f51])).
% 0.22/0.55  fof(f122,plain,(
% 0.22/0.55    ( ! [X0] : (~r1_partfun1(X0,sK2) | ~v1_partfun1(sK2,sK0) | ~v1_partfun1(X0,sK0) | sK2 = X0 | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(X0)) )),
% 0.22/0.55    inference(resolution,[],[f22,f27])).
% 0.22/0.55  fof(f27,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f11])).
% 0.22/0.55  fof(f11,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f10])).
% 0.22/0.55  fof(f10,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f3])).
% 0.22/0.55  fof(f3,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).
% 0.22/0.55  fof(f22,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f104,plain,(
% 0.22/0.55    spl3_7 | ~spl3_2 | ~spl3_5),
% 0.22/0.55    inference(avatar_split_clause,[],[f103,f82,f44,f95])).
% 0.22/0.55  fof(f44,plain,(
% 0.22/0.55    spl3_2 <=> k1_xboole_0 = sK0),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.55  fof(f82,plain,(
% 0.22/0.55    spl3_5 <=> ! [X1] : (~r1_partfun1(X1,sK2) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | sK2 = X1 | ~v1_partfun1(X1,k1_xboole_0))),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.55  fof(f103,plain,(
% 0.22/0.55    sK1 = sK2 | (~spl3_2 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f102,f66])).
% 0.22/0.55  fof(f66,plain,(
% 0.22/0.55    v1_partfun1(sK1,k1_xboole_0) | ~spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f65,f17])).
% 0.22/0.55  fof(f65,plain,(
% 0.22/0.55    v1_partfun1(sK1,k1_xboole_0) | ~v1_funct_1(sK1) | ~spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f62,f55])).
% 0.22/0.55  fof(f55,plain,(
% 0.22/0.55    v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 0.22/0.55    inference(backward_demodulation,[],[f18,f46])).
% 0.22/0.55  fof(f46,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | ~spl3_2),
% 0.22/0.55    inference(avatar_component_clause,[],[f44])).
% 0.22/0.55  fof(f18,plain,(
% 0.22/0.55    v1_funct_2(sK1,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f62,plain,(
% 0.22/0.55    v1_partfun1(sK1,k1_xboole_0) | ~v1_funct_2(sK1,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK1) | ~spl3_2),
% 0.22/0.55    inference(resolution,[],[f56,f32])).
% 0.22/0.55  fof(f32,plain,(
% 0.22/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_partfun1(X2,k1_xboole_0) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f29])).
% 0.22/0.55  fof(f29,plain,(
% 0.22/0.55    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(equality_resolution,[],[f26])).
% 0.22/0.55  fof(f26,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f9,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.55    inference(flattening,[],[f8])).
% 0.22/0.55  fof(f8,plain,(
% 0.22/0.55    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.55    inference(ennf_transformation,[],[f2])).
% 0.22/0.55  fof(f2,axiom,(
% 0.22/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 0.22/0.55  fof(f56,plain,(
% 0.22/0.55    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_2),
% 0.22/0.55    inference(backward_demodulation,[],[f19,f46])).
% 0.22/0.55  fof(f102,plain,(
% 0.22/0.55    sK1 = sK2 | ~v1_partfun1(sK1,k1_xboole_0) | (~spl3_2 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f101,f23])).
% 0.22/0.55  fof(f101,plain,(
% 0.22/0.55    ~r1_partfun1(sK1,sK2) | sK1 = sK2 | ~v1_partfun1(sK1,k1_xboole_0) | (~spl3_2 | ~spl3_5)),
% 0.22/0.55    inference(subsumption_resolution,[],[f99,f17])).
% 0.22/0.55  fof(f99,plain,(
% 0.22/0.55    ~v1_funct_1(sK1) | ~r1_partfun1(sK1,sK2) | sK1 = sK2 | ~v1_partfun1(sK1,k1_xboole_0) | (~spl3_2 | ~spl3_5)),
% 0.22/0.55    inference(resolution,[],[f83,f56])).
% 0.22/0.55  fof(f83,plain,(
% 0.22/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X1) | ~r1_partfun1(X1,sK2) | sK2 = X1 | ~v1_partfun1(X1,k1_xboole_0)) ) | ~spl3_5),
% 0.22/0.55    inference(avatar_component_clause,[],[f82])).
% 0.22/0.55  fof(f85,plain,(
% 0.22/0.55    spl3_4 | ~spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f71,f44,f78])).
% 0.22/0.55  fof(f78,plain,(
% 0.22/0.55    spl3_4 <=> v1_partfun1(sK2,k1_xboole_0)),
% 0.22/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.55  fof(f71,plain,(
% 0.22/0.55    v1_partfun1(sK2,k1_xboole_0) | ~spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f70,f20])).
% 0.22/0.55  fof(f70,plain,(
% 0.22/0.55    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f67,f57])).
% 0.22/0.55  fof(f57,plain,(
% 0.22/0.55    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl3_2),
% 0.22/0.55    inference(backward_demodulation,[],[f21,f46])).
% 0.22/0.55  fof(f21,plain,(
% 0.22/0.55    v1_funct_2(sK2,sK0,sK0)),
% 0.22/0.55    inference(cnf_transformation,[],[f16])).
% 0.22/0.55  fof(f67,plain,(
% 0.22/0.55    v1_partfun1(sK2,k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(sK2) | ~spl3_2),
% 0.22/0.55    inference(resolution,[],[f58,f32])).
% 0.22/0.55  fof(f58,plain,(
% 0.22/0.55    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl3_2),
% 0.22/0.55    inference(backward_demodulation,[],[f22,f46])).
% 0.22/0.55  fof(f84,plain,(
% 0.22/0.55    ~spl3_4 | spl3_5 | ~spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f76,f44,f82,f78])).
% 0.22/0.55  fof(f76,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_partfun1(X1,sK2) | ~v1_partfun1(sK2,k1_xboole_0) | ~v1_partfun1(X1,k1_xboole_0) | sK2 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X1)) ) | ~spl3_2),
% 0.22/0.55    inference(subsumption_resolution,[],[f73,f20])).
% 0.22/0.55  fof(f73,plain,(
% 0.22/0.55    ( ! [X1] : (~r1_partfun1(X1,sK2) | ~v1_partfun1(sK2,k1_xboole_0) | ~v1_partfun1(X1,k1_xboole_0) | sK2 = X1 | ~v1_funct_1(sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_1(X1)) ) | ~spl3_2),
% 0.22/0.55    inference(resolution,[],[f27,f58])).
% 0.22/0.55  fof(f54,plain,(
% 0.22/0.55    spl3_3 | spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f49,f44,f51])).
% 0.22/0.55  fof(f49,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK2,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f48,f20])).
% 0.22/0.55  fof(f48,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK2,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.55    inference(subsumption_resolution,[],[f36,f21])).
% 0.22/0.55  fof(f36,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK2,sK0) | ~v1_funct_2(sK2,sK0,sK0) | ~v1_funct_1(sK2)),
% 0.22/0.55    inference(resolution,[],[f31,f22])).
% 0.22/0.55  fof(f31,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(duplicate_literal_removal,[],[f25])).
% 0.22/0.55  fof(f25,plain,(
% 0.22/0.55    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.55    inference(cnf_transformation,[],[f9])).
% 0.22/0.55  fof(f47,plain,(
% 0.22/0.55    spl3_1 | spl3_2),
% 0.22/0.55    inference(avatar_split_clause,[],[f38,f44,f40])).
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK1,sK0)),
% 0.22/0.55    inference(subsumption_resolution,[],[f37,f17])).
% 0.22/0.55  fof(f37,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK1,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.55    inference(subsumption_resolution,[],[f35,f18])).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    k1_xboole_0 = sK0 | v1_partfun1(sK1,sK0) | ~v1_funct_2(sK1,sK0,sK0) | ~v1_funct_1(sK1)),
% 0.22/0.55    inference(resolution,[],[f31,f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (18746)------------------------------
% 0.22/0.55  % (18746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18746)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (18746)Memory used [KB]: 6140
% 0.22/0.55  % (18746)Time elapsed: 0.125 s
% 0.22/0.55  % (18746)------------------------------
% 0.22/0.55  % (18746)------------------------------
% 0.22/0.55  % (18764)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.56  % (18741)Success in time 0.191 s
%------------------------------------------------------------------------------
