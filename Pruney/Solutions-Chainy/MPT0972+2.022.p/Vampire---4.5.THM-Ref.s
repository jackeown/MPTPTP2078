%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:08 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 420 expanded)
%              Number of leaves         :   23 ( 128 expanded)
%              Depth                    :   27
%              Number of atoms          :  524 (2668 expanded)
%              Number of equality atoms :  138 ( 490 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f436,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f129,f143,f147,f165,f183,f384,f428])).

fof(f428,plain,(
    ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f427])).

fof(f427,plain,
    ( $false
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f405,f88])).

fof(f88,plain,(
    r2_relset_1(sK0,sK1,sK2,sK2) ),
    inference(resolution,[],[f45,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

% (29434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ r2_hidden(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28,f27])).

fof(f27,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ r2_hidden(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK0,sK1,sK2,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
              | ~ r2_hidden(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ r2_hidden(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ r2_hidden(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ r2_hidden(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( r2_hidden(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f405,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f50,f324])).

fof(f324,plain,
    ( sK2 = sK3
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_14
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f50,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f384,plain,
    ( ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f382,f190])).

fof(f190,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f91,f98])).

fof(f98,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f91,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f45,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f382,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(forward_demodulation,[],[f381,f328])).

fof(f328,plain,
    ( sK0 = k1_relat_1(sK3)
    | spl6_2 ),
    inference(forward_demodulation,[],[f314,f327])).

fof(f327,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f326,f101])).

fof(f101,plain,
    ( k1_xboole_0 != sK1
    | spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl6_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f326,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f312,f47])).

fof(f47,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f312,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f48,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f314,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f48,f67])).

fof(f381,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f380,f92])).

fof(f92,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f45,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f380,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f379,f43])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f379,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f378,f315])).

fof(f315,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f48,f66])).

fof(f378,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f377,f46])).

fof(f46,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f377,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f376,f323])).

fof(f323,plain,
    ( sK2 != sK3
    | spl6_14 ),
    inference(avatar_component_clause,[],[f322])).

fof(f376,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(superposition,[],[f53,f358])).

fof(f358,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(resolution,[],[f337,f49])).

fof(f49,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f337,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f336,f315])).

fof(f336,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f335,f46])).

fof(f335,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | spl6_2
    | spl6_14 ),
    inference(subsumption_resolution,[],[f334,f323])).

fof(f334,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f329])).

fof(f329,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl6_1
    | spl6_2 ),
    inference(superposition,[],[f202,f328])).

fof(f202,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f201,f92])).

fof(f201,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f197,f43])).

fof(f197,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl6_1 ),
    inference(superposition,[],[f52,f190])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
            & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X0) = k1_relat_1(X1) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f183,plain,
    ( ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_contradiction_clause,[],[f182])).

fof(f182,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f181,f177])).

fof(f177,plain,
    ( r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4 ),
    inference(forward_demodulation,[],[f88,f128])).

fof(f128,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f181,plain,
    ( ~ r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f180,f128])).

fof(f180,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,k1_xboole_0)
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f50,f142])).

fof(f142,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_6
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f165,plain,(
    spl6_5 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl6_5 ),
    inference(subsumption_resolution,[],[f163,f51])).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f163,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_5 ),
    inference(resolution,[],[f144,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f144,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0)
    | spl6_5 ),
    inference(resolution,[],[f138,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).

fof(f36,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f34])).

% (29416)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f138,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_5
  <=> r1_tarski(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f147,plain,(
    spl6_3 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl6_3 ),
    inference(subsumption_resolution,[],[f145,f51])).

fof(f145,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl6_3 ),
    inference(resolution,[],[f130,f54])).

fof(f130,plain,
    ( r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0)
    | spl6_3 ),
    inference(resolution,[],[f124,f59])).

fof(f124,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_3
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f143,plain,
    ( ~ spl6_5
    | spl6_6
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f134,f100,f140,f136])).

fof(f134,plain,
    ( k1_xboole_0 = sK3
    | ~ r1_tarski(k1_xboole_0,sK3)
    | ~ spl6_2 ),
    inference(resolution,[],[f132,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

% (29425)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f132,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ spl6_2 ),
    inference(resolution,[],[f114,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f107,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f107,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f48,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f129,plain,
    ( ~ spl6_3
    | spl6_4
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f120,f100,f126,f122])).

fof(f120,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl6_2 ),
    inference(resolution,[],[f117,f57])).

fof(f117,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl6_2 ),
    inference(forward_demodulation,[],[f112,f78])).

fof(f112,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0))
    | ~ spl6_2 ),
    inference(backward_demodulation,[],[f93,f102])).

fof(f93,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f45,f61])).

fof(f103,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f94,f100,f96])).

fof(f94,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f89,f44])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f89,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f45,f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.53  % (29414)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (29423)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (29422)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (29415)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.48/0.55  % (29430)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.48/0.55  % (29431)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.55  % (29420)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (29412)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.48/0.56  % (29426)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.48/0.56  % (29413)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.48/0.56  % (29419)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (29410)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.56/0.56  % (29411)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.56/0.57  % (29429)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.56/0.57  % (29409)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.56/0.57  % (29427)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.56/0.57  % (29428)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.56/0.57  % (29432)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.56/0.57  % (29407)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.56/0.57  % (29435)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.56/0.57  % (29424)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.56/0.57  % (29415)Refutation found. Thanks to Tanya!
% 1.56/0.57  % SZS status Theorem for theBenchmark
% 1.56/0.57  % SZS output start Proof for theBenchmark
% 1.56/0.57  fof(f436,plain,(
% 1.56/0.57    $false),
% 1.56/0.57    inference(avatar_sat_refutation,[],[f103,f129,f143,f147,f165,f183,f384,f428])).
% 1.56/0.57  fof(f428,plain,(
% 1.56/0.57    ~spl6_14),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f427])).
% 1.56/0.57  fof(f427,plain,(
% 1.56/0.57    $false | ~spl6_14),
% 1.56/0.57    inference(subsumption_resolution,[],[f405,f88])).
% 1.56/0.57  fof(f88,plain,(
% 1.56/0.57    r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.56/0.57    inference(resolution,[],[f45,f86])).
% 1.56/0.57  fof(f86,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.56/0.57    inference(duplicate_literal_removal,[],[f85])).
% 1.56/0.57  fof(f85,plain,(
% 1.56/0.57    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.57    inference(equality_resolution,[],[f75])).
% 1.56/0.57  fof(f75,plain,(
% 1.56/0.57    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.56/0.57    inference(cnf_transformation,[],[f42])).
% 1.56/0.57  fof(f42,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(nnf_transformation,[],[f26])).
% 1.56/0.57  fof(f26,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(flattening,[],[f25])).
% 1.56/0.57  fof(f25,plain,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.56/0.57    inference(ennf_transformation,[],[f10])).
% 1.56/0.57  fof(f10,axiom,(
% 1.56/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.56/0.57  % (29434)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.56/0.57  fof(f45,plain,(
% 1.56/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f29,plain,(
% 1.56/0.57    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f28,f27])).
% 1.56/0.57  fof(f27,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f28,plain,(
% 1.56/0.57    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f16,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.56/0.57    inference(flattening,[],[f15])).
% 1.56/0.57  fof(f15,plain,(
% 1.56/0.57    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.56/0.57    inference(ennf_transformation,[],[f13])).
% 1.56/0.57  fof(f13,negated_conjecture,(
% 1.56/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.56/0.57    inference(negated_conjecture,[],[f12])).
% 1.56/0.57  fof(f12,conjecture,(
% 1.56/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.56/0.57  fof(f405,plain,(
% 1.56/0.57    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl6_14),
% 1.56/0.57    inference(backward_demodulation,[],[f50,f324])).
% 1.56/0.57  fof(f324,plain,(
% 1.56/0.57    sK2 = sK3 | ~spl6_14),
% 1.56/0.57    inference(avatar_component_clause,[],[f322])).
% 1.56/0.57  fof(f322,plain,(
% 1.56/0.57    spl6_14 <=> sK2 = sK3),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.56/0.57  fof(f50,plain,(
% 1.56/0.57    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f384,plain,(
% 1.56/0.57    ~spl6_1 | spl6_2 | spl6_14),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f383])).
% 1.56/0.57  fof(f383,plain,(
% 1.56/0.57    $false | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f382,f190])).
% 1.56/0.57  fof(f190,plain,(
% 1.56/0.57    sK0 = k1_relat_1(sK2) | ~spl6_1),
% 1.56/0.57    inference(forward_demodulation,[],[f91,f98])).
% 1.56/0.57  fof(f98,plain,(
% 1.56/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_1),
% 1.56/0.57    inference(avatar_component_clause,[],[f96])).
% 1.56/0.57  fof(f96,plain,(
% 1.56/0.57    spl6_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.56/0.57  fof(f91,plain,(
% 1.56/0.57    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.56/0.57    inference(resolution,[],[f45,f67])).
% 1.56/0.57  fof(f67,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f22])).
% 1.56/0.57  fof(f22,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(ennf_transformation,[],[f9])).
% 1.56/0.57  fof(f9,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.56/0.57  fof(f382,plain,(
% 1.56/0.57    sK0 != k1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(forward_demodulation,[],[f381,f328])).
% 1.56/0.57  fof(f328,plain,(
% 1.56/0.57    sK0 = k1_relat_1(sK3) | spl6_2),
% 1.56/0.57    inference(forward_demodulation,[],[f314,f327])).
% 1.56/0.57  fof(f327,plain,(
% 1.56/0.57    sK0 = k1_relset_1(sK0,sK1,sK3) | spl6_2),
% 1.56/0.57    inference(subsumption_resolution,[],[f326,f101])).
% 1.56/0.57  fof(f101,plain,(
% 1.56/0.57    k1_xboole_0 != sK1 | spl6_2),
% 1.56/0.57    inference(avatar_component_clause,[],[f100])).
% 1.56/0.57  fof(f100,plain,(
% 1.56/0.57    spl6_2 <=> k1_xboole_0 = sK1),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.56/0.57  fof(f326,plain,(
% 1.56/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.56/0.57    inference(subsumption_resolution,[],[f312,f47])).
% 1.56/0.57  fof(f47,plain,(
% 1.56/0.57    v1_funct_2(sK3,sK0,sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f312,plain,(
% 1.56/0.57    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.56/0.57    inference(resolution,[],[f48,f68])).
% 1.56/0.57  fof(f68,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.56/0.57    inference(cnf_transformation,[],[f41])).
% 1.56/0.57  fof(f41,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(nnf_transformation,[],[f24])).
% 1.56/0.57  fof(f24,plain,(
% 1.56/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(flattening,[],[f23])).
% 1.56/0.57  fof(f23,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(ennf_transformation,[],[f11])).
% 1.56/0.57  fof(f11,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.56/0.57  fof(f48,plain,(
% 1.56/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f314,plain,(
% 1.56/0.57    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.56/0.57    inference(resolution,[],[f48,f67])).
% 1.56/0.57  fof(f381,plain,(
% 1.56/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f380,f92])).
% 1.56/0.57  fof(f92,plain,(
% 1.56/0.57    v1_relat_1(sK2)),
% 1.56/0.57    inference(resolution,[],[f45,f66])).
% 1.56/0.57  fof(f66,plain,(
% 1.56/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f21])).
% 1.56/0.57  fof(f21,plain,(
% 1.56/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.56/0.57    inference(ennf_transformation,[],[f8])).
% 1.56/0.57  fof(f8,axiom,(
% 1.56/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.56/0.57  fof(f380,plain,(
% 1.56/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f379,f43])).
% 1.56/0.57  fof(f43,plain,(
% 1.56/0.57    v1_funct_1(sK2)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f379,plain,(
% 1.56/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f378,f315])).
% 1.56/0.57  fof(f315,plain,(
% 1.56/0.57    v1_relat_1(sK3)),
% 1.56/0.57    inference(resolution,[],[f48,f66])).
% 1.56/0.57  fof(f378,plain,(
% 1.56/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f377,f46])).
% 1.56/0.57  fof(f46,plain,(
% 1.56/0.57    v1_funct_1(sK3)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f377,plain,(
% 1.56/0.57    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f376,f323])).
% 1.56/0.57  fof(f323,plain,(
% 1.56/0.57    sK2 != sK3 | spl6_14),
% 1.56/0.57    inference(avatar_component_clause,[],[f322])).
% 1.56/0.57  fof(f376,plain,(
% 1.56/0.57    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f375])).
% 1.56/0.57  fof(f375,plain,(
% 1.56/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(superposition,[],[f53,f358])).
% 1.56/0.57  fof(f358,plain,(
% 1.56/0.57    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(resolution,[],[f337,f49])).
% 1.56/0.57  fof(f49,plain,(
% 1.56/0.57    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f337,plain,(
% 1.56/0.57    r2_hidden(sK4(sK2,sK3),sK0) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f336,f315])).
% 1.56/0.57  fof(f336,plain,(
% 1.56/0.57    r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f335,f46])).
% 1.56/0.57  fof(f335,plain,(
% 1.56/0.57    r2_hidden(sK4(sK2,sK3),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl6_1 | spl6_2 | spl6_14)),
% 1.56/0.57    inference(subsumption_resolution,[],[f334,f323])).
% 1.56/0.57  fof(f334,plain,(
% 1.56/0.57    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl6_1 | spl6_2)),
% 1.56/0.57    inference(trivial_inequality_removal,[],[f329])).
% 1.56/0.57  fof(f329,plain,(
% 1.56/0.57    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl6_1 | spl6_2)),
% 1.56/0.57    inference(superposition,[],[f202,f328])).
% 1.56/0.57  fof(f202,plain,(
% 1.56/0.57    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl6_1),
% 1.56/0.57    inference(subsumption_resolution,[],[f201,f92])).
% 1.56/0.57  fof(f201,plain,(
% 1.56/0.57    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl6_1),
% 1.56/0.57    inference(subsumption_resolution,[],[f197,f43])).
% 1.56/0.57  fof(f197,plain,(
% 1.56/0.57    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl6_1),
% 1.56/0.57    inference(superposition,[],[f52,f190])).
% 1.56/0.57  fof(f52,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f31])).
% 1.56/0.57  fof(f31,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f30])).
% 1.56/0.57  fof(f30,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f18,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.56/0.57    inference(flattening,[],[f17])).
% 1.56/0.57  fof(f17,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.56/0.57    inference(ennf_transformation,[],[f7])).
% 1.56/0.57  fof(f7,axiom,(
% 1.56/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.56/0.57  fof(f53,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f31])).
% 1.56/0.57  fof(f183,plain,(
% 1.56/0.57    ~spl6_4 | ~spl6_6),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f182])).
% 1.56/0.57  fof(f182,plain,(
% 1.56/0.57    $false | (~spl6_4 | ~spl6_6)),
% 1.56/0.57    inference(subsumption_resolution,[],[f181,f177])).
% 1.56/0.57  fof(f177,plain,(
% 1.56/0.57    r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) | ~spl6_4),
% 1.56/0.57    inference(forward_demodulation,[],[f88,f128])).
% 1.56/0.57  fof(f128,plain,(
% 1.56/0.57    k1_xboole_0 = sK2 | ~spl6_4),
% 1.56/0.57    inference(avatar_component_clause,[],[f126])).
% 1.56/0.57  fof(f126,plain,(
% 1.56/0.57    spl6_4 <=> k1_xboole_0 = sK2),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.56/0.57  fof(f181,plain,(
% 1.56/0.57    ~r2_relset_1(sK0,sK1,k1_xboole_0,k1_xboole_0) | (~spl6_4 | ~spl6_6)),
% 1.56/0.57    inference(forward_demodulation,[],[f180,f128])).
% 1.56/0.57  fof(f180,plain,(
% 1.56/0.57    ~r2_relset_1(sK0,sK1,sK2,k1_xboole_0) | ~spl6_6),
% 1.56/0.57    inference(forward_demodulation,[],[f50,f142])).
% 1.56/0.57  fof(f142,plain,(
% 1.56/0.57    k1_xboole_0 = sK3 | ~spl6_6),
% 1.56/0.57    inference(avatar_component_clause,[],[f140])).
% 1.56/0.57  fof(f140,plain,(
% 1.56/0.57    spl6_6 <=> k1_xboole_0 = sK3),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.56/0.57  fof(f165,plain,(
% 1.56/0.57    spl6_5),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f164])).
% 1.56/0.57  fof(f164,plain,(
% 1.56/0.57    $false | spl6_5),
% 1.56/0.57    inference(subsumption_resolution,[],[f163,f51])).
% 1.56/0.57  fof(f51,plain,(
% 1.56/0.57    v1_xboole_0(k1_xboole_0)),
% 1.56/0.57    inference(cnf_transformation,[],[f3])).
% 1.56/0.57  fof(f3,axiom,(
% 1.56/0.57    v1_xboole_0(k1_xboole_0)),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.56/0.57  fof(f163,plain,(
% 1.56/0.57    ~v1_xboole_0(k1_xboole_0) | spl6_5),
% 1.56/0.57    inference(resolution,[],[f144,f54])).
% 1.56/0.57  fof(f54,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f19])).
% 1.56/0.57  fof(f19,plain,(
% 1.56/0.57    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.56/0.57    inference(ennf_transformation,[],[f14])).
% 1.56/0.57  fof(f14,plain,(
% 1.56/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.56/0.57  fof(f1,axiom,(
% 1.56/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.56/0.57  fof(f144,plain,(
% 1.56/0.57    r2_hidden(sK5(k1_xboole_0,sK3),k1_xboole_0) | spl6_5),
% 1.56/0.57    inference(resolution,[],[f138,f59])).
% 1.56/0.57  fof(f59,plain,(
% 1.56/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f37])).
% 1.56/0.57  fof(f37,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f35,f36])).
% 1.56/0.57  fof(f36,plain,(
% 1.56/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK5(X0,X1),X0)))),
% 1.56/0.57    introduced(choice_axiom,[])).
% 1.56/0.57  fof(f35,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(rectify,[],[f34])).
% 1.56/0.57  % (29416)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.56/0.57  fof(f34,plain,(
% 1.56/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f20])).
% 1.56/0.57  fof(f20,plain,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.56/0.57    inference(ennf_transformation,[],[f2])).
% 1.56/0.57  fof(f2,axiom,(
% 1.56/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.56/0.57  fof(f138,plain,(
% 1.56/0.57    ~r1_tarski(k1_xboole_0,sK3) | spl6_5),
% 1.56/0.57    inference(avatar_component_clause,[],[f136])).
% 1.56/0.57  fof(f136,plain,(
% 1.56/0.57    spl6_5 <=> r1_tarski(k1_xboole_0,sK3)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.56/0.57  fof(f147,plain,(
% 1.56/0.57    spl6_3),
% 1.56/0.57    inference(avatar_contradiction_clause,[],[f146])).
% 1.56/0.57  fof(f146,plain,(
% 1.56/0.57    $false | spl6_3),
% 1.56/0.57    inference(subsumption_resolution,[],[f145,f51])).
% 1.56/0.57  fof(f145,plain,(
% 1.56/0.57    ~v1_xboole_0(k1_xboole_0) | spl6_3),
% 1.56/0.57    inference(resolution,[],[f130,f54])).
% 1.56/0.57  fof(f130,plain,(
% 1.56/0.57    r2_hidden(sK5(k1_xboole_0,sK2),k1_xboole_0) | spl6_3),
% 1.56/0.57    inference(resolution,[],[f124,f59])).
% 1.56/0.57  fof(f124,plain,(
% 1.56/0.57    ~r1_tarski(k1_xboole_0,sK2) | spl6_3),
% 1.56/0.57    inference(avatar_component_clause,[],[f122])).
% 1.56/0.57  fof(f122,plain,(
% 1.56/0.57    spl6_3 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.56/0.57    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.56/0.57  fof(f143,plain,(
% 1.56/0.57    ~spl6_5 | spl6_6 | ~spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f134,f100,f140,f136])).
% 1.56/0.57  fof(f134,plain,(
% 1.56/0.57    k1_xboole_0 = sK3 | ~r1_tarski(k1_xboole_0,sK3) | ~spl6_2),
% 1.56/0.57    inference(resolution,[],[f132,f57])).
% 1.56/0.57  fof(f57,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f33])).
% 1.56/0.57  % (29425)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.56/0.57  fof(f33,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(flattening,[],[f32])).
% 1.56/0.57  fof(f32,plain,(
% 1.56/0.57    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.57    inference(nnf_transformation,[],[f4])).
% 1.56/0.57  fof(f4,axiom,(
% 1.56/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.57  fof(f132,plain,(
% 1.56/0.57    r1_tarski(sK3,k1_xboole_0) | ~spl6_2),
% 1.56/0.57    inference(resolution,[],[f114,f61])).
% 1.56/0.57  fof(f61,plain,(
% 1.56/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.56/0.57    inference(cnf_transformation,[],[f38])).
% 1.56/0.57  fof(f38,plain,(
% 1.56/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.56/0.57    inference(nnf_transformation,[],[f6])).
% 1.56/0.57  fof(f6,axiom,(
% 1.56/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.56/0.57  fof(f114,plain,(
% 1.56/0.57    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl6_2),
% 1.56/0.57    inference(forward_demodulation,[],[f107,f78])).
% 1.56/0.57  fof(f78,plain,(
% 1.56/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.56/0.57    inference(equality_resolution,[],[f65])).
% 1.56/0.57  fof(f65,plain,(
% 1.56/0.57    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 1.56/0.57    inference(cnf_transformation,[],[f40])).
% 1.56/0.57  fof(f40,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.57    inference(flattening,[],[f39])).
% 1.56/0.57  fof(f39,plain,(
% 1.56/0.57    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 1.56/0.57    inference(nnf_transformation,[],[f5])).
% 1.56/0.57  fof(f5,axiom,(
% 1.56/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.56/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.56/0.57  fof(f107,plain,(
% 1.56/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | ~spl6_2),
% 1.56/0.57    inference(backward_demodulation,[],[f48,f102])).
% 1.56/0.57  fof(f102,plain,(
% 1.56/0.57    k1_xboole_0 = sK1 | ~spl6_2),
% 1.56/0.57    inference(avatar_component_clause,[],[f100])).
% 1.56/0.57  fof(f129,plain,(
% 1.56/0.57    ~spl6_3 | spl6_4 | ~spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f120,f100,f126,f122])).
% 1.56/0.57  fof(f120,plain,(
% 1.56/0.57    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl6_2),
% 1.56/0.57    inference(resolution,[],[f117,f57])).
% 1.56/0.57  fof(f117,plain,(
% 1.56/0.57    r1_tarski(sK2,k1_xboole_0) | ~spl6_2),
% 1.56/0.57    inference(forward_demodulation,[],[f112,f78])).
% 1.56/0.57  fof(f112,plain,(
% 1.56/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) | ~spl6_2),
% 1.56/0.57    inference(backward_demodulation,[],[f93,f102])).
% 1.56/0.57  fof(f93,plain,(
% 1.56/0.57    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.56/0.57    inference(resolution,[],[f45,f61])).
% 1.56/0.57  fof(f103,plain,(
% 1.56/0.57    spl6_1 | spl6_2),
% 1.56/0.57    inference(avatar_split_clause,[],[f94,f100,f96])).
% 1.56/0.57  fof(f94,plain,(
% 1.56/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.56/0.57    inference(subsumption_resolution,[],[f89,f44])).
% 1.56/0.57  fof(f44,plain,(
% 1.56/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.56/0.57    inference(cnf_transformation,[],[f29])).
% 1.56/0.57  fof(f89,plain,(
% 1.56/0.57    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.56/0.57    inference(resolution,[],[f45,f68])).
% 1.56/0.57  % SZS output end Proof for theBenchmark
% 1.56/0.57  % (29415)------------------------------
% 1.56/0.57  % (29415)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.57  % (29415)Termination reason: Refutation
% 1.56/0.57  
% 1.56/0.57  % (29415)Memory used [KB]: 10874
% 1.56/0.57  % (29415)Time elapsed: 0.121 s
% 1.56/0.57  % (29415)------------------------------
% 1.56/0.57  % (29415)------------------------------
% 1.56/0.57  % (29436)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.56/0.57  % (29418)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.56/0.58  % (29406)Success in time 0.214 s
%------------------------------------------------------------------------------
