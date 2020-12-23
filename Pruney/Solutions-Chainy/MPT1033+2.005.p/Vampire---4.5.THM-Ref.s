%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:43 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 320 expanded)
%              Number of leaves         :   27 ( 108 expanded)
%              Depth                    :   15
%              Number of atoms          :  438 (1892 expanded)
%              Number of equality atoms :   77 ( 372 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f564,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f223,f255,f370,f375,f410,f479,f505,f523,f525,f526,f561])).

fof(f561,plain,
    ( ~ spl6_22
    | ~ spl6_21
    | spl6_29 ),
    inference(avatar_split_clause,[],[f556,f434,f367,f372])).

fof(f372,plain,
    ( spl6_22
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f367,plain,
    ( spl6_21
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f434,plain,
    ( spl6_29
  <=> sK3 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f556,plain,
    ( k1_xboole_0 != sK3
    | ~ spl6_21
    | spl6_29 ),
    inference(backward_demodulation,[],[f435,f369])).

fof(f369,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f367])).

fof(f435,plain,
    ( sK3 != sK4
    | spl6_29 ),
    inference(avatar_component_clause,[],[f434])).

fof(f526,plain,(
    spl6_37 ),
    inference(avatar_split_clause,[],[f49,f520])).

fof(f520,plain,
    ( spl6_37
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f49,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
    & ( k1_xboole_0 = sK1
      | k1_xboole_0 != sK2 )
    & r1_partfun1(sK3,sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f36,f35])).

fof(f35,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK1,sK2,sK3,X3)
          & ( k1_xboole_0 = sK1
            | k1_xboole_0 != sK2 )
          & r1_partfun1(sK3,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X3,sK1,sK2)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK1,sK2,sK3,X3)
        & ( k1_xboole_0 = sK1
          | k1_xboole_0 != sK2 )
        & r1_partfun1(sK3,X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        & v1_funct_2(X3,sK1,sK2)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK1,sK2,sK3,sK4)
      & ( k1_xboole_0 = sK1
        | k1_xboole_0 != sK2 )
      & r1_partfun1(sK3,sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_relset_1(X0,X1,X2,X3)
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_relset_1(X0,X1,X2,X3)
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

fof(f525,plain,(
    spl6_36 ),
    inference(avatar_split_clause,[],[f50,f516])).

fof(f516,plain,
    ( spl6_36
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f50,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f523,plain,
    ( ~ spl6_36
    | spl6_12
    | spl6_14
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f485,f520,f227,f216,f516])).

fof(f216,plain,
    ( spl6_12
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f227,plain,
    ( spl6_14
  <=> v1_partfun1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f485,plain,
    ( ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK1)
    | v1_xboole_0(sK2)
    | ~ v1_funct_2(sK4,sK1,sK2) ),
    inference(resolution,[],[f212,f93])).

fof(f93,plain,(
    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f69,f51])).

fof(f51,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f212,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,k2_zfmisc_1(X3,X4))
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X3)
      | v1_xboole_0(X4)
      | ~ v1_funct_2(X2,X3,X4) ) ),
    inference(resolution,[],[f63,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f505,plain,(
    ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f492,f194])).

fof(f194,plain,(
    r2_relset_1(sK1,sK2,sK3,sK3) ),
    inference(resolution,[],[f82,f48])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f492,plain,
    ( ~ r2_relset_1(sK1,sK2,sK3,sK3)
    | ~ spl6_29 ),
    inference(backward_demodulation,[],[f54,f436])).

fof(f436,plain,
    ( sK3 = sK4
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f434])).

fof(f54,plain,(
    ~ r2_relset_1(sK1,sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f479,plain,
    ( spl6_29
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f478,f253,f220,f434])).

fof(f220,plain,
    ( spl6_13
  <=> v1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f253,plain,
    ( spl6_18
  <=> ! [X1] :
        ( ~ r1_partfun1(X1,sK4)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | sK4 = X1
        | ~ v1_partfun1(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f478,plain,
    ( sK3 = sK4
    | ~ spl6_13
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f477,f222])).

fof(f222,plain,
    ( v1_partfun1(sK3,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f220])).

fof(f477,plain,
    ( sK3 = sK4
    | ~ v1_partfun1(sK3,sK1)
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f476,f52])).

fof(f52,plain,(
    r1_partfun1(sK3,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f476,plain,
    ( ~ r1_partfun1(sK3,sK4)
    | sK3 = sK4
    | ~ v1_partfun1(sK3,sK1)
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f470,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f470,plain,
    ( ~ v1_funct_1(sK3)
    | ~ r1_partfun1(sK3,sK4)
    | sK3 = sK4
    | ~ v1_partfun1(sK3,sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f254,f48])).

fof(f254,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ v1_funct_1(X1)
        | ~ r1_partfun1(X1,sK4)
        | sK4 = X1
        | ~ v1_partfun1(X1,sK1) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f253])).

fof(f410,plain,
    ( ~ spl6_12
    | spl6_8 ),
    inference(avatar_split_clause,[],[f376,f155,f216])).

fof(f155,plain,
    ( spl6_8
  <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f376,plain,
    ( ~ v1_xboole_0(sK2)
    | spl6_8 ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK2)
    | spl6_8 ),
    inference(superposition,[],[f157,f291])).

fof(f291,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f290,f181])).

% (26113)Refutation not found, incomplete strategy% (26113)------------------------------
% (26113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26113)Termination reason: Refutation not found, incomplete strategy

% (26113)Memory used [KB]: 10746
% (26113)Time elapsed: 0.114 s
% (26113)------------------------------
% (26113)------------------------------
% (26123)Refutation not found, incomplete strategy% (26123)------------------------------
% (26123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26123)Termination reason: Refutation not found, incomplete strategy

% (26123)Memory used [KB]: 10618
% (26123)Time elapsed: 0.117 s
% (26123)------------------------------
% (26123)------------------------------
% (26118)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (26134)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (26118)Refutation not found, incomplete strategy% (26118)------------------------------
% (26118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26118)Termination reason: Refutation not found, incomplete strategy

% (26118)Memory used [KB]: 10618
% (26118)Time elapsed: 0.109 s
% (26118)------------------------------
% (26118)------------------------------
% (26128)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (26137)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (26112)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% (26125)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (26112)Refutation not found, incomplete strategy% (26112)------------------------------
% (26112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (26112)Termination reason: Refutation not found, incomplete strategy

% (26112)Memory used [KB]: 10618
% (26112)Time elapsed: 0.136 s
% (26112)------------------------------
% (26112)------------------------------
% (26136)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (26129)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f181,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f180,f80])).

fof(f80,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f180,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ v1_xboole_0(X0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f150,f60])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( sP0(sK5(X0),X0)
        & r2_hidden(sK5(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK5(X0),X0)
        & r2_hidden(sK5(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f20,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ! [X2,X3] :
          ( k4_tarski(X2,X3) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f150,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X4)
      | ~ r1_tarski(X6,X4) ) ),
    inference(resolution,[],[f76,f70])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f290,plain,(
    ! [X2] : k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f287,f100])).

fof(f100,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f99,f80])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f71,f70])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f287,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k2_zfmisc_1(X2,k1_xboole_0))
      | k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0) ) ),
    inference(resolution,[],[f279,f171])).

fof(f171,plain,(
    ! [X0,X1] : v5_relat_1(k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f146,f80])).

fof(f146,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(X1,k2_zfmisc_1(X3,X2))
      | v5_relat_1(X1,X2) ) ),
    inference(resolution,[],[f73,f70])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f279,plain,(
    ! [X5] :
      ( ~ v5_relat_1(X5,k1_xboole_0)
      | ~ v1_relat_1(X5)
      | k1_xboole_0 = X5 ) ),
    inference(trivial_inequality_removal,[],[f278])).

fof(f278,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | ~ v5_relat_1(X5,k1_xboole_0) ) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X5
      | ~ v1_relat_1(X5)
      | ~ v5_relat_1(X5,k1_xboole_0)
      | ~ v1_relat_1(X5) ) ),
    inference(superposition,[],[f57,f133])).

fof(f133,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | ~ v5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f109,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f109,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f68,f94])).

fof(f94,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f157,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f375,plain,
    ( spl6_22
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f184,f155,f372])).

fof(f184,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f180,f92])).

fof(f92,plain,(
    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) ),
    inference(resolution,[],[f69,f48])).

fof(f370,plain,
    ( spl6_21
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f185,f155,f367])).

fof(f185,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK1,sK2))
    | k1_xboole_0 = sK4 ),
    inference(resolution,[],[f180,f93])).

fof(f255,plain,
    ( ~ spl6_14
    | spl6_18 ),
    inference(avatar_split_clause,[],[f251,f253,f227])).

fof(f251,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK4)
      | ~ v1_partfun1(sK4,sK1)
      | ~ v1_partfun1(X1,sK1)
      | sK4 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1) ) ),
    inference(subsumption_resolution,[],[f243,f49])).

fof(f243,plain,(
    ! [X1] :
      ( ~ r1_partfun1(X1,sK4)
      | ~ v1_partfun1(sK4,sK1)
      | ~ v1_partfun1(X1,sK1)
      | sK4 = X1
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | X2 = X3
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

fof(f223,plain,
    ( spl6_12
    | spl6_13 ),
    inference(avatar_split_clause,[],[f214,f220,f216])).

fof(f214,plain,
    ( v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f213,f46])).

fof(f213,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f209,f47])).

fof(f47,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f209,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,sK1)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f63,f48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.48  % (26115)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.23/0.50  % (26124)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.51  % (26114)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.23/0.51  % (26113)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.23/0.51  % (26117)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.52  % (26117)Refutation not found, incomplete strategy% (26117)------------------------------
% 0.23/0.52  % (26117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.52  % (26117)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.52  
% 0.23/0.52  % (26117)Memory used [KB]: 6140
% 0.23/0.52  % (26117)Time elapsed: 0.091 s
% 0.23/0.52  % (26117)------------------------------
% 0.23/0.52  % (26117)------------------------------
% 0.23/0.52  % (26132)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.23/0.52  % (26135)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (26122)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.52  % (26121)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (26116)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.52  % (26126)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.53  % (26130)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.23/0.53  % (26131)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.23/0.53  % (26123)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.23/0.53  % (26116)Refutation found. Thanks to Tanya!
% 0.23/0.53  % SZS status Theorem for theBenchmark
% 0.23/0.53  % SZS output start Proof for theBenchmark
% 0.23/0.53  fof(f564,plain,(
% 0.23/0.53    $false),
% 0.23/0.53    inference(avatar_sat_refutation,[],[f223,f255,f370,f375,f410,f479,f505,f523,f525,f526,f561])).
% 0.23/0.53  fof(f561,plain,(
% 0.23/0.53    ~spl6_22 | ~spl6_21 | spl6_29),
% 0.23/0.53    inference(avatar_split_clause,[],[f556,f434,f367,f372])).
% 0.23/0.53  fof(f372,plain,(
% 0.23/0.53    spl6_22 <=> k1_xboole_0 = sK3),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.23/0.53  fof(f367,plain,(
% 0.23/0.53    spl6_21 <=> k1_xboole_0 = sK4),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.23/0.53  fof(f434,plain,(
% 0.23/0.53    spl6_29 <=> sK3 = sK4),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.23/0.53  fof(f556,plain,(
% 0.23/0.53    k1_xboole_0 != sK3 | (~spl6_21 | spl6_29)),
% 0.23/0.53    inference(backward_demodulation,[],[f435,f369])).
% 0.23/0.53  fof(f369,plain,(
% 0.23/0.53    k1_xboole_0 = sK4 | ~spl6_21),
% 0.23/0.53    inference(avatar_component_clause,[],[f367])).
% 0.23/0.53  fof(f435,plain,(
% 0.23/0.53    sK3 != sK4 | spl6_29),
% 0.23/0.53    inference(avatar_component_clause,[],[f434])).
% 0.23/0.53  fof(f526,plain,(
% 0.23/0.53    spl6_37),
% 0.23/0.53    inference(avatar_split_clause,[],[f49,f520])).
% 0.23/0.53  fof(f520,plain,(
% 0.23/0.53    spl6_37 <=> v1_funct_1(sK4)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    v1_funct_1(sK4)),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    (~r2_relset_1(sK1,sK2,sK3,sK4) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f17,f36,f35])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ? [X3] : (~r2_relset_1(sK1,sK2,sK3,X3) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X3,sK1,sK2) & v1_funct_1(X3)) => (~r2_relset_1(sK1,sK2,sK3,sK4) & (k1_xboole_0 = sK1 | k1_xboole_0 != sK2) & r1_partfun1(sK3,sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f17,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.23/0.53    inference(flattening,[],[f16])).
% 0.23/0.53  fof(f16,plain,(
% 0.23/0.53    ? [X0,X1,X2] : (? [X3] : (((~r2_relset_1(X0,X1,X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.23/0.53    inference(ennf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.23/0.53    inference(negated_conjecture,[],[f14])).
% 0.23/0.53  fof(f14,conjecture,(
% 0.23/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_relset_1(X0,X1,X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).
% 0.23/0.53  fof(f525,plain,(
% 0.23/0.53    spl6_36),
% 0.23/0.53    inference(avatar_split_clause,[],[f50,f516])).
% 0.23/0.53  fof(f516,plain,(
% 0.23/0.53    spl6_36 <=> v1_funct_2(sK4,sK1,sK2)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    v1_funct_2(sK4,sK1,sK2)),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f523,plain,(
% 0.23/0.53    ~spl6_36 | spl6_12 | spl6_14 | ~spl6_37),
% 0.23/0.53    inference(avatar_split_clause,[],[f485,f520,f227,f216,f516])).
% 0.23/0.53  fof(f216,plain,(
% 0.23/0.53    spl6_12 <=> v1_xboole_0(sK2)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.23/0.53  fof(f227,plain,(
% 0.23/0.53    spl6_14 <=> v1_partfun1(sK4,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.23/0.53  fof(f485,plain,(
% 0.23/0.53    ~v1_funct_1(sK4) | v1_partfun1(sK4,sK1) | v1_xboole_0(sK2) | ~v1_funct_2(sK4,sK1,sK2)),
% 0.23/0.53    inference(resolution,[],[f212,f93])).
% 0.23/0.53  fof(f93,plain,(
% 0.23/0.53    r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))),
% 0.23/0.53    inference(resolution,[],[f69,f51])).
% 0.23/0.53  fof(f51,plain,(
% 0.23/0.53    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f69,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f45])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.23/0.53    inference(nnf_transformation,[],[f3])).
% 0.23/0.53  fof(f3,axiom,(
% 0.23/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.53  fof(f212,plain,(
% 0.23/0.53    ( ! [X4,X2,X3] : (~r1_tarski(X2,k2_zfmisc_1(X3,X4)) | ~v1_funct_1(X2) | v1_partfun1(X2,X3) | v1_xboole_0(X4) | ~v1_funct_2(X2,X3,X4)) )),
% 0.23/0.53    inference(resolution,[],[f63,f70])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f45])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f22])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.53    inference(flattening,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.23/0.53  fof(f505,plain,(
% 0.23/0.53    ~spl6_29),
% 0.23/0.53    inference(avatar_contradiction_clause,[],[f504])).
% 0.23/0.53  fof(f504,plain,(
% 0.23/0.53    $false | ~spl6_29),
% 0.23/0.53    inference(subsumption_resolution,[],[f492,f194])).
% 0.23/0.53  fof(f194,plain,(
% 0.23/0.53    r2_relset_1(sK1,sK2,sK3,sK3)),
% 0.23/0.53    inference(resolution,[],[f82,f48])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f82,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_relset_1(X1,X2,X0,X0)) )),
% 0.23/0.53    inference(condensation,[],[f77])).
% 0.23/0.53  fof(f77,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f32])).
% 0.23/0.53  fof(f32,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.23/0.53    inference(flattening,[],[f31])).
% 0.23/0.53  fof(f31,plain,(
% 0.23/0.53    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.53    inference(ennf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.23/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.23/0.53  fof(f492,plain,(
% 0.23/0.53    ~r2_relset_1(sK1,sK2,sK3,sK3) | ~spl6_29),
% 0.23/0.53    inference(backward_demodulation,[],[f54,f436])).
% 0.23/0.53  fof(f436,plain,(
% 0.23/0.53    sK3 = sK4 | ~spl6_29),
% 0.23/0.53    inference(avatar_component_clause,[],[f434])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ~r2_relset_1(sK1,sK2,sK3,sK4)),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f479,plain,(
% 0.23/0.53    spl6_29 | ~spl6_13 | ~spl6_18),
% 0.23/0.53    inference(avatar_split_clause,[],[f478,f253,f220,f434])).
% 0.23/0.53  fof(f220,plain,(
% 0.23/0.53    spl6_13 <=> v1_partfun1(sK3,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.23/0.53  fof(f253,plain,(
% 0.23/0.53    spl6_18 <=> ! [X1] : (~r1_partfun1(X1,sK4) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | sK4 = X1 | ~v1_partfun1(X1,sK1))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.23/0.53  fof(f478,plain,(
% 0.23/0.53    sK3 = sK4 | (~spl6_13 | ~spl6_18)),
% 0.23/0.53    inference(subsumption_resolution,[],[f477,f222])).
% 0.23/0.53  fof(f222,plain,(
% 0.23/0.53    v1_partfun1(sK3,sK1) | ~spl6_13),
% 0.23/0.53    inference(avatar_component_clause,[],[f220])).
% 0.23/0.53  fof(f477,plain,(
% 0.23/0.53    sK3 = sK4 | ~v1_partfun1(sK3,sK1) | ~spl6_18),
% 0.23/0.53    inference(subsumption_resolution,[],[f476,f52])).
% 0.23/0.53  fof(f52,plain,(
% 0.23/0.53    r1_partfun1(sK3,sK4)),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f476,plain,(
% 0.23/0.53    ~r1_partfun1(sK3,sK4) | sK3 = sK4 | ~v1_partfun1(sK3,sK1) | ~spl6_18),
% 0.23/0.53    inference(subsumption_resolution,[],[f470,f46])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    v1_funct_1(sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f37])).
% 0.23/0.53  fof(f470,plain,(
% 0.23/0.53    ~v1_funct_1(sK3) | ~r1_partfun1(sK3,sK4) | sK3 = sK4 | ~v1_partfun1(sK3,sK1) | ~spl6_18),
% 0.23/0.53    inference(resolution,[],[f254,f48])).
% 0.23/0.53  fof(f254,plain,(
% 0.23/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1) | ~r1_partfun1(X1,sK4) | sK4 = X1 | ~v1_partfun1(X1,sK1)) ) | ~spl6_18),
% 0.23/0.53    inference(avatar_component_clause,[],[f253])).
% 0.23/0.53  fof(f410,plain,(
% 0.23/0.53    ~spl6_12 | spl6_8),
% 0.23/0.53    inference(avatar_split_clause,[],[f376,f155,f216])).
% 0.23/0.53  fof(f155,plain,(
% 0.23/0.53    spl6_8 <=> v1_xboole_0(k2_zfmisc_1(sK1,sK2))),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.23/0.53  fof(f376,plain,(
% 0.23/0.53    ~v1_xboole_0(sK2) | spl6_8),
% 0.23/0.53    inference(duplicate_literal_removal,[],[f336])).
% 0.23/0.53  fof(f336,plain,(
% 0.23/0.53    ~v1_xboole_0(sK2) | ~v1_xboole_0(sK2) | spl6_8),
% 0.23/0.53    inference(superposition,[],[f157,f291])).
% 0.23/0.53  fof(f291,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 0.23/0.53    inference(superposition,[],[f290,f181])).
% 0.23/0.53  % (26113)Refutation not found, incomplete strategy% (26113)------------------------------
% 0.23/0.53  % (26113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (26113)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (26113)Memory used [KB]: 10746
% 0.23/0.53  % (26113)Time elapsed: 0.114 s
% 0.23/0.53  % (26113)------------------------------
% 0.23/0.53  % (26113)------------------------------
% 0.23/0.53  % (26123)Refutation not found, incomplete strategy% (26123)------------------------------
% 0.23/0.53  % (26123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (26123)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (26123)Memory used [KB]: 10618
% 0.23/0.53  % (26123)Time elapsed: 0.117 s
% 0.23/0.53  % (26123)------------------------------
% 0.23/0.53  % (26123)------------------------------
% 0.23/0.53  % (26118)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.53  % (26134)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.53  % (26118)Refutation not found, incomplete strategy% (26118)------------------------------
% 0.23/0.53  % (26118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (26118)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.53  
% 0.23/0.53  % (26118)Memory used [KB]: 10618
% 0.23/0.53  % (26118)Time elapsed: 0.109 s
% 0.23/0.53  % (26118)------------------------------
% 0.23/0.53  % (26118)------------------------------
% 0.23/0.55  % (26128)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.55  % (26137)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.23/0.55  % (26112)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.55  % (26125)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.55  % (26112)Refutation not found, incomplete strategy% (26112)------------------------------
% 0.23/0.55  % (26112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.55  % (26112)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.55  
% 0.23/0.55  % (26112)Memory used [KB]: 10618
% 0.23/0.55  % (26112)Time elapsed: 0.136 s
% 0.23/0.55  % (26112)------------------------------
% 0.23/0.55  % (26112)------------------------------
% 0.23/0.55  % (26136)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.55  % (26129)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.23/0.56  fof(f181,plain,(
% 0.23/0.56    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.23/0.56    inference(resolution,[],[f180,f80])).
% 1.52/0.56  fof(f80,plain,(
% 1.52/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.52/0.56    inference(equality_resolution,[],[f67])).
% 1.52/0.56  fof(f67,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.52/0.56    inference(cnf_transformation,[],[f44])).
% 1.52/0.56  fof(f44,plain,(
% 1.52/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.56    inference(flattening,[],[f43])).
% 1.52/0.56  fof(f43,plain,(
% 1.52/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.52/0.56    inference(nnf_transformation,[],[f1])).
% 1.52/0.56  fof(f1,axiom,(
% 1.52/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.52/0.56  fof(f180,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~v1_xboole_0(X0) | k1_xboole_0 = X1) )),
% 1.52/0.56    inference(resolution,[],[f150,f60])).
% 1.52/0.56  fof(f60,plain,(
% 1.52/0.56    ( ! [X0] : (r2_hidden(sK5(X0),X0) | k1_xboole_0 = X0) )),
% 1.52/0.56    inference(cnf_transformation,[],[f41])).
% 1.52/0.56  fof(f41,plain,(
% 1.52/0.56    ! [X0] : ((sP0(sK5(X0),X0) & r2_hidden(sK5(X0),X0)) | k1_xboole_0 = X0)),
% 1.52/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f34,f40])).
% 1.52/0.56  fof(f40,plain,(
% 1.52/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK5(X0),X0) & r2_hidden(sK5(X0),X0)))),
% 1.52/0.56    introduced(choice_axiom,[])).
% 1.52/0.56  fof(f34,plain,(
% 1.52/0.56    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.52/0.56    inference(definition_folding,[],[f20,f33])).
% 1.52/0.56  fof(f33,plain,(
% 1.52/0.56    ! [X1,X0] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 1.52/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.52/0.56  fof(f20,plain,(
% 1.52/0.56    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.52/0.56    inference(ennf_transformation,[],[f11])).
% 1.52/0.56  fof(f11,axiom,(
% 1.52/0.56    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 1.52/0.56  fof(f150,plain,(
% 1.52/0.56    ( ! [X6,X4,X5] : (~r2_hidden(X5,X6) | ~v1_xboole_0(X4) | ~r1_tarski(X6,X4)) )),
% 1.52/0.56    inference(resolution,[],[f76,f70])).
% 1.52/0.56  fof(f76,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f30])).
% 1.52/0.56  fof(f30,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f5])).
% 1.52/0.56  fof(f5,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.52/0.56  fof(f290,plain,(
% 1.52/0.56    ( ! [X2] : (k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f287,f100])).
% 1.52/0.56  fof(f100,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.52/0.56    inference(resolution,[],[f99,f80])).
% 1.52/0.56  fof(f99,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0)) )),
% 1.52/0.56    inference(resolution,[],[f71,f70])).
% 1.52/0.56  fof(f71,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f24])).
% 1.52/0.56  fof(f24,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.56    inference(ennf_transformation,[],[f8])).
% 1.52/0.56  fof(f8,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.52/0.56  fof(f287,plain,(
% 1.52/0.56    ( ! [X2] : (~v1_relat_1(k2_zfmisc_1(X2,k1_xboole_0)) | k1_xboole_0 = k2_zfmisc_1(X2,k1_xboole_0)) )),
% 1.52/0.56    inference(resolution,[],[f279,f171])).
% 1.52/0.56  fof(f171,plain,(
% 1.52/0.56    ( ! [X0,X1] : (v5_relat_1(k2_zfmisc_1(X0,X1),X1)) )),
% 1.52/0.56    inference(resolution,[],[f146,f80])).
% 1.52/0.56  fof(f146,plain,(
% 1.52/0.56    ( ! [X2,X3,X1] : (~r1_tarski(X1,k2_zfmisc_1(X3,X2)) | v5_relat_1(X1,X2)) )),
% 1.52/0.56    inference(resolution,[],[f73,f70])).
% 1.52/0.56  fof(f73,plain,(
% 1.52/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f25])).
% 1.52/0.56  fof(f25,plain,(
% 1.52/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.52/0.56    inference(ennf_transformation,[],[f9])).
% 1.52/0.56  fof(f9,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.52/0.56  fof(f279,plain,(
% 1.52/0.56    ( ! [X5] : (~v5_relat_1(X5,k1_xboole_0) | ~v1_relat_1(X5) | k1_xboole_0 = X5) )),
% 1.52/0.56    inference(trivial_inequality_removal,[],[f278])).
% 1.52/0.56  fof(f278,plain,(
% 1.52/0.56    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v5_relat_1(X5,k1_xboole_0)) )),
% 1.52/0.56    inference(duplicate_literal_removal,[],[f277])).
% 1.52/0.56  fof(f277,plain,(
% 1.52/0.56    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = X5 | ~v1_relat_1(X5) | ~v5_relat_1(X5,k1_xboole_0) | ~v1_relat_1(X5)) )),
% 1.52/0.56    inference(superposition,[],[f57,f133])).
% 1.52/0.56  fof(f133,plain,(
% 1.52/0.56    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | ~v5_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(resolution,[],[f109,f64])).
% 1.52/0.56  fof(f64,plain,(
% 1.52/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f42])).
% 1.52/0.56  fof(f42,plain,(
% 1.52/0.56    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(nnf_transformation,[],[f23])).
% 1.52/0.56  fof(f23,plain,(
% 1.52/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.52/0.56    inference(ennf_transformation,[],[f6])).
% 1.52/0.56  fof(f6,axiom,(
% 1.52/0.56    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.52/0.56  fof(f109,plain,(
% 1.52/0.56    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 1.52/0.56    inference(resolution,[],[f68,f94])).
% 1.52/0.56  fof(f94,plain,(
% 1.52/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.52/0.56    inference(resolution,[],[f69,f55])).
% 1.52/0.56  fof(f55,plain,(
% 1.52/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.52/0.56    inference(cnf_transformation,[],[f2])).
% 1.52/0.56  fof(f2,axiom,(
% 1.52/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.52/0.56  fof(f68,plain,(
% 1.52/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f44])).
% 1.52/0.56  fof(f57,plain,(
% 1.52/0.56    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f19])).
% 1.52/0.56  fof(f19,plain,(
% 1.52/0.56    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(flattening,[],[f18])).
% 1.52/0.56  fof(f18,plain,(
% 1.52/0.56    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.52/0.56    inference(ennf_transformation,[],[f7])).
% 1.52/0.56  fof(f7,axiom,(
% 1.52/0.56    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 1.52/0.56  fof(f157,plain,(
% 1.52/0.56    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | spl6_8),
% 1.52/0.56    inference(avatar_component_clause,[],[f155])).
% 1.52/0.56  fof(f375,plain,(
% 1.52/0.56    spl6_22 | ~spl6_8),
% 1.52/0.56    inference(avatar_split_clause,[],[f184,f155,f372])).
% 1.52/0.56  fof(f184,plain,(
% 1.52/0.56    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | k1_xboole_0 = sK3),
% 1.52/0.56    inference(resolution,[],[f180,f92])).
% 1.52/0.56  fof(f92,plain,(
% 1.52/0.56    r1_tarski(sK3,k2_zfmisc_1(sK1,sK2))),
% 1.52/0.56    inference(resolution,[],[f69,f48])).
% 1.52/0.56  fof(f370,plain,(
% 1.52/0.56    spl6_21 | ~spl6_8),
% 1.52/0.56    inference(avatar_split_clause,[],[f185,f155,f367])).
% 1.52/0.56  fof(f185,plain,(
% 1.52/0.56    ~v1_xboole_0(k2_zfmisc_1(sK1,sK2)) | k1_xboole_0 = sK4),
% 1.52/0.56    inference(resolution,[],[f180,f93])).
% 1.52/0.56  fof(f255,plain,(
% 1.52/0.56    ~spl6_14 | spl6_18),
% 1.52/0.56    inference(avatar_split_clause,[],[f251,f253,f227])).
% 1.52/0.56  fof(f251,plain,(
% 1.52/0.56    ( ! [X1] : (~r1_partfun1(X1,sK4) | ~v1_partfun1(sK4,sK1) | ~v1_partfun1(X1,sK1) | sK4 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1)) )),
% 1.52/0.56    inference(subsumption_resolution,[],[f243,f49])).
% 1.52/0.56  fof(f243,plain,(
% 1.52/0.56    ( ! [X1] : (~r1_partfun1(X1,sK4) | ~v1_partfun1(sK4,sK1) | ~v1_partfun1(X1,sK1) | sK4 = X1 | ~v1_funct_1(sK4) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(X1)) )),
% 1.52/0.56    inference(resolution,[],[f74,f51])).
% 1.52/0.56  fof(f74,plain,(
% 1.52/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | X2 = X3 | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.52/0.56    inference(cnf_transformation,[],[f27])).
% 1.52/0.56  fof(f27,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.52/0.56    inference(flattening,[],[f26])).
% 1.52/0.56  fof(f26,plain,(
% 1.52/0.56    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.52/0.56    inference(ennf_transformation,[],[f13])).
% 1.52/0.56  fof(f13,axiom,(
% 1.52/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 1.52/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).
% 1.52/0.56  fof(f223,plain,(
% 1.52/0.56    spl6_12 | spl6_13),
% 1.52/0.56    inference(avatar_split_clause,[],[f214,f220,f216])).
% 1.52/0.56  fof(f214,plain,(
% 1.52/0.56    v1_partfun1(sK3,sK1) | v1_xboole_0(sK2)),
% 1.52/0.56    inference(subsumption_resolution,[],[f213,f46])).
% 1.52/0.56  fof(f213,plain,(
% 1.52/0.56    ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK2)),
% 1.52/0.56    inference(subsumption_resolution,[],[f209,f47])).
% 1.52/0.56  fof(f47,plain,(
% 1.52/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.52/0.56    inference(cnf_transformation,[],[f37])).
% 1.52/0.56  fof(f209,plain,(
% 1.52/0.56    ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | v1_partfun1(sK3,sK1) | v1_xboole_0(sK2)),
% 1.52/0.56    inference(resolution,[],[f63,f48])).
% 1.52/0.56  % SZS output end Proof for theBenchmark
% 1.52/0.56  % (26116)------------------------------
% 1.52/0.56  % (26116)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (26116)Termination reason: Refutation
% 1.52/0.56  
% 1.52/0.56  % (26116)Memory used [KB]: 6396
% 1.52/0.56  % (26116)Time elapsed: 0.111 s
% 1.52/0.56  % (26116)------------------------------
% 1.52/0.56  % (26116)------------------------------
% 1.52/0.56  % (26109)Success in time 0.187 s
%------------------------------------------------------------------------------
