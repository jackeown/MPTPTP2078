%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 362 expanded)
%              Number of leaves         :   22 ( 125 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 (2103 expanded)
%              Number of equality atoms :  154 ( 514 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f156,f306,f320,f321,f366,f377,f378,f379,f386,f391])).

fof(f391,plain,
    ( ~ spl9_7
    | ~ spl9_16 ),
    inference(avatar_contradiction_clause,[],[f390])).

fof(f390,plain,
    ( $false
    | ~ spl9_7
    | ~ spl9_16 ),
    inference(subsumption_resolution,[],[f387,f81])).

fof(f81,plain,(
    ! [X1] : ~ sP0(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f387,plain,
    ( sP0(k1_xboole_0,k1_xboole_0)
    | ~ spl9_7
    | ~ spl9_16 ),
    inference(backward_demodulation,[],[f171,f365])).

fof(f365,plain,
    ( k1_xboole_0 = sK3
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl9_16
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f171,plain,
    ( sP0(sK3,k1_xboole_0)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f149,f158])).

fof(f158,plain,
    ( k1_xboole_0 = sK4
    | ~ spl9_7 ),
    inference(resolution,[],[f149,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,
    ( sP0(sK3,sK4)
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl9_7
  <=> sP0(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f386,plain,
    ( ~ spl9_18
    | spl9_10
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f383,f359,f221,f374])).

fof(f374,plain,
    ( spl9_18
  <=> k1_xboole_0 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f221,plain,
    ( spl9_10
  <=> sK5 = sK6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f359,plain,
    ( spl9_15
  <=> k1_xboole_0 = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f383,plain,
    ( k1_xboole_0 != sK6
    | spl9_10
    | ~ spl9_15 ),
    inference(backward_demodulation,[],[f222,f361])).

fof(f361,plain,
    ( k1_xboole_0 = sK5
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f359])).

fof(f222,plain,
    ( sK5 != sK6
    | spl9_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f379,plain,
    ( spl9_17
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f349,f147,f370])).

fof(f370,plain,
    ( spl9_17
  <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f349,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f339,f76])).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f339,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f51,f158])).

fof(f51,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
    & ! [X4] :
        ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
        | ~ r2_hidden(X4,sK3) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK5,sK3,sK4)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f30,f29])).

fof(f29,plain,
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
          ( ~ r2_relset_1(sK3,sK4,sK5,X3)
          & ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
              | ~ r2_hidden(X4,sK3) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_2(X3,sK3,sK4)
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK5,sK3,sK4)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK3,sK4,sK5,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK5,X4)
            | ~ r2_hidden(X4,sK3) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        & v1_funct_2(X3,sK3,sK4)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK3,sK4,sK5,sK6)
      & ! [X4] :
          ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
          | ~ r2_hidden(X4,sK3) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).

fof(f378,plain,
    ( spl9_14
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f348,f147,f355])).

fof(f355,plain,
    ( spl9_14
  <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f348,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_7 ),
    inference(forward_demodulation,[],[f337,f76])).

fof(f337,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0)))
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f48,f158])).

fof(f48,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f31])).

fof(f377,plain,
    ( ~ spl9_17
    | spl9_18
    | spl9_16
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f368,f147,f363,f374,f370])).

fof(f368,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK6
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_7 ),
    inference(resolution,[],[f338,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[],[f80,f109])).

% (6300)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f109,plain,(
    ! [X0,X1] :
      ( sP2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f72,f76])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X2,X1,X0)
        & sP1(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f21,f27,f26,f25])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ sP2(X0,k1_xboole_0,X2)
      | ~ v1_funct_2(X0,X2,k1_xboole_0)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X0 ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ v1_funct_2(X0,X2,X1)
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X0,X2,X1)
          | k1_xboole_0 != X0 )
        & ( k1_xboole_0 = X0
          | ~ v1_funct_2(X0,X2,X1) ) )
      | k1_xboole_0 = X2
      | k1_xboole_0 != X1
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_xboole_0 != X2 )
        & ( k1_xboole_0 = X2
          | ~ v1_funct_2(X2,X0,X1) ) )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP2(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f338,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f50,f158])).

fof(f50,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f366,plain,
    ( ~ spl9_14
    | spl9_15
    | spl9_16
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f353,f147,f363,f359,f355])).

fof(f353,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK5
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_7 ),
    inference(resolution,[],[f336,f127])).

fof(f336,plain,
    ( v1_funct_2(sK5,sK3,k1_xboole_0)
    | ~ spl9_7 ),
    inference(backward_demodulation,[],[f47,f158])).

fof(f47,plain,(
    v1_funct_2(sK5,sK3,sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f321,plain,
    ( spl9_6
    | spl9_7 ),
    inference(avatar_split_clause,[],[f183,f147,f143])).

fof(f143,plain,
    ( spl9_6
  <=> sK3 = k1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f183,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(subsumption_resolution,[],[f177,f47])).

fof(f177,plain,
    ( ~ v1_funct_2(sK5,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK5) ),
    inference(resolution,[],[f48,f131])).

fof(f131,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f129,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f129,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP0(X3,X4)
      | ~ sP1(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f67,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP0(X0,X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP0(X0,X1)
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f320,plain,
    ( spl9_10
    | ~ spl9_6
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f319,f153,f143,f221])).

fof(f153,plain,
    ( spl9_8
  <=> sK3 = k1_relat_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f319,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f318,f85])).

fof(f85,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f63,f48])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f318,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ v1_relat_1(sK5)
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f276,f46])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f31])).

fof(f276,plain,
    ( sK3 != k1_relat_1(sK5)
    | sK5 = sK6
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | ~ spl9_8 ),
    inference(equality_resolution,[],[f271])).

fof(f271,plain,
    ( ! [X0] :
        ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
        | k1_relat_1(X0) != sK3
        | sK6 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f270,f241])).

fof(f241,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f240,f86])).

fof(f86,plain,(
    v1_relat_1(sK6) ),
    inference(resolution,[],[f63,f51])).

fof(f240,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK6) )
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f237,f49])).

fof(f49,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f237,plain,
    ( ! [X1] :
        ( r2_hidden(sK7(sK6,X1),sK3)
        | sK6 = X1
        | k1_relat_1(X1) != sK3
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK6)
        | ~ v1_relat_1(sK6) )
    | ~ spl9_8 ),
    inference(superposition,[],[f55,f155])).

fof(f155,plain,
    ( sK3 = k1_relat_1(sK6)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f153])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
            & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) )
          | k1_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
        & r2_hidden(sK7(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).

fof(f270,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK3
        | k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
        | sK6 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ r2_hidden(sK7(sK6,X0),sK3) )
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f269,f155])).

fof(f269,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f268,f86])).

fof(f268,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK6)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(subsumption_resolution,[],[f264,f49])).

fof(f264,plain,(
    ! [X0] :
      ( k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0))
      | sK6 = X0
      | k1_relat_1(X0) != k1_relat_1(sK6)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK6)
      | ~ v1_relat_1(sK6)
      | ~ r2_hidden(sK7(sK6,X0),sK3) ) ),
    inference(superposition,[],[f56,f52])).

fof(f52,plain,(
    ! [X4] :
      ( k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4)
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f306,plain,(
    ~ spl9_10 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f294,f123])).

fof(f123,plain,(
    r2_relset_1(sK3,sK4,sK5,sK5) ),
    inference(resolution,[],[f83,f48])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f294,plain,
    ( ~ r2_relset_1(sK3,sK4,sK5,sK5)
    | ~ spl9_10 ),
    inference(backward_demodulation,[],[f53,f223])).

fof(f223,plain,
    ( sK5 = sK6
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f221])).

fof(f53,plain,(
    ~ r2_relset_1(sK3,sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f31])).

fof(f156,plain,
    ( spl9_8
    | spl9_7 ),
    inference(avatar_split_clause,[],[f151,f147,f153])).

fof(f151,plain,
    ( sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(subsumption_resolution,[],[f138,f50])).

fof(f138,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | sP0(sK3,sK4)
    | sK3 = k1_relat_1(sK6) ),
    inference(resolution,[],[f131,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:01:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (6283)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (6283)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (6290)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (6289)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f394,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f156,f306,f320,f321,f366,f377,f378,f379,f386,f391])).
% 0.21/0.54  fof(f391,plain,(
% 0.21/0.54    ~spl9_7 | ~spl9_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f390])).
% 0.21/0.54  fof(f390,plain,(
% 0.21/0.54    $false | (~spl9_7 | ~spl9_16)),
% 0.21/0.54    inference(subsumption_resolution,[],[f387,f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X1] : (~sP0(k1_xboole_0,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 != X0 | ~sP0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    sP0(k1_xboole_0,k1_xboole_0) | (~spl9_7 | ~spl9_16)),
% 0.21/0.54    inference(backward_demodulation,[],[f171,f365])).
% 0.21/0.54  fof(f365,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | ~spl9_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f363])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    spl9_16 <=> k1_xboole_0 = sK3),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    sP0(sK3,k1_xboole_0) | ~spl9_7),
% 0.21/0.54    inference(backward_demodulation,[],[f149,f158])).
% 0.21/0.54  fof(f158,plain,(
% 0.21/0.54    k1_xboole_0 = sK4 | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f149,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~sP0(X0,X1) | k1_xboole_0 = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f44])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    sP0(sK3,sK4) | ~spl9_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f147])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    spl9_7 <=> sP0(sK3,sK4)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    ~spl9_18 | spl9_10 | ~spl9_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f383,f359,f221,f374])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    spl9_18 <=> k1_xboole_0 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 0.21/0.54  fof(f221,plain,(
% 0.21/0.54    spl9_10 <=> sK5 = sK6),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    spl9_15 <=> k1_xboole_0 = sK5),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.21/0.54  fof(f383,plain,(
% 0.21/0.54    k1_xboole_0 != sK6 | (spl9_10 | ~spl9_15)),
% 0.21/0.54    inference(backward_demodulation,[],[f222,f361])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    k1_xboole_0 = sK5 | ~spl9_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f359])).
% 0.21/0.54  fof(f222,plain,(
% 0.21/0.54    sK5 != sK6 | spl9_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f221])).
% 0.21/0.54  fof(f379,plain,(
% 0.21/0.54    spl9_17 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f349,f147,f370])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    spl9_17 <=> m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | ~spl9_7),
% 0.21/0.54    inference(forward_demodulation,[],[f339,f76])).
% 0.21/0.54  fof(f76,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(flattening,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) | ~spl9_7),
% 0.21/0.54    inference(backward_demodulation,[],[f51,f158])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f14,f30,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK5,sK3,sK4) & v1_funct_1(sK5))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X3] : (~r2_relset_1(sK3,sK4,sK5,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK5,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(X3,sK3,sK4) & v1_funct_1(X3)) => (~r2_relset_1(sK3,sK4,sK5,sK6) & ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.54    inference(flattening,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.21/0.54  fof(f378,plain,(
% 0.21/0.54    spl9_14 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f348,f147,f355])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    spl9_14 <=> m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 0.21/0.54  fof(f348,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl9_7),
% 0.21/0.54    inference(forward_demodulation,[],[f337,f76])).
% 0.21/0.54  fof(f337,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) | ~spl9_7),
% 0.21/0.54    inference(backward_demodulation,[],[f48,f158])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f377,plain,(
% 0.21/0.54    ~spl9_17 | spl9_18 | spl9_16 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f368,f147,f363,f374,f370])).
% 0.21/0.54  fof(f368,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK6 | ~m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f338,f127])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v1_funct_2(X0,X1,k1_xboole_0) | k1_xboole_0 = X1 | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.54    inference(resolution,[],[f80,f109])).
% 0.21/0.54  % (6300)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    ( ! [X0,X1] : (sP2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))) )),
% 0.21/0.54    inference(superposition,[],[f72,f76])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP2(X2,X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((sP2(X2,X1,X0) & sP1(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(definition_folding,[],[f21,f27,f26,f25])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X2,X0] : (~sP2(X0,k1_xboole_0,X2) | ~v1_funct_2(X0,X2,k1_xboole_0) | k1_xboole_0 = X2 | k1_xboole_0 = X0) )),
% 0.21/0.54    inference(equality_resolution,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X0,X2,X1) | k1_xboole_0 != X0) & (k1_xboole_0 = X0 | ~v1_funct_2(X0,X2,X1))) | k1_xboole_0 = X2 | k1_xboole_0 != X1 | ~sP2(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP2(X2,X1,X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f27])).
% 0.21/0.54  fof(f338,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK3,k1_xboole_0) | ~spl9_7),
% 0.21/0.54    inference(backward_demodulation,[],[f50,f158])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    v1_funct_2(sK6,sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~spl9_14 | spl9_15 | spl9_16 | ~spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f353,f147,f363,f359,f355])).
% 0.21/0.54  fof(f353,plain,(
% 0.21/0.54    k1_xboole_0 = sK3 | k1_xboole_0 = sK5 | ~m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) | ~spl9_7),
% 0.21/0.54    inference(resolution,[],[f336,f127])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,k1_xboole_0) | ~spl9_7),
% 0.21/0.54    inference(backward_demodulation,[],[f47,f158])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    v1_funct_2(sK5,sK3,sK4)),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f321,plain,(
% 0.21/0.54    spl9_6 | spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f183,f147,f143])).
% 0.21/0.54  fof(f143,plain,(
% 0.21/0.54    spl9_6 <=> sK3 = k1_relat_1(sK5)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.21/0.54  fof(f183,plain,(
% 0.21/0.54    sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.54    inference(subsumption_resolution,[],[f177,f47])).
% 0.21/0.54  fof(f177,plain,(
% 0.21/0.54    ~v1_funct_2(sK5,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f48,f131])).
% 0.21/0.54  fof(f131,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | k1_relat_1(X5) = X3) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f129,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP1(X0,X2,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f129,plain,(
% 0.21/0.54    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP0(X3,X4) | ~sP1(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.21/0.54    inference(superposition,[],[f67,f64])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP0(X0,X2) | ~sP1(X0,X1,X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP0(X0,X2) | ~sP1(X0,X1,X2))),
% 0.21/0.54    inference(rectify,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP0(X0,X1) | ~sP1(X0,X2,X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f26])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    spl9_10 | ~spl9_6 | ~spl9_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f319,f153,f143,f221])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl9_8 <=> sK3 = k1_relat_1(sK6)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.21/0.54  fof(f319,plain,(
% 0.21/0.54    sK3 != k1_relat_1(sK5) | sK5 = sK6 | ~spl9_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f318,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    v1_relat_1(sK5)),
% 0.21/0.54    inference(resolution,[],[f63,f48])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    sK3 != k1_relat_1(sK5) | sK5 = sK6 | ~v1_relat_1(sK5) | ~spl9_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f276,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    v1_funct_1(sK5)),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f276,plain,(
% 0.21/0.54    sK3 != k1_relat_1(sK5) | sK5 = sK6 | ~v1_funct_1(sK5) | ~v1_relat_1(sK5) | ~spl9_8),
% 0.21/0.54    inference(equality_resolution,[],[f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | k1_relat_1(X0) != sK3 | sK6 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl9_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f270,f241])).
% 0.21/0.54  fof(f241,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl9_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f240,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    v1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f63,f51])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK6)) ) | ~spl9_8),
% 0.21/0.54    inference(subsumption_resolution,[],[f237,f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    v1_funct_1(sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f237,plain,(
% 0.21/0.54    ( ! [X1] : (r2_hidden(sK7(sK6,X1),sK3) | sK6 = X1 | k1_relat_1(X1) != sK3 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6)) ) | ~spl9_8),
% 0.21/0.54    inference(superposition,[],[f55,f155])).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    sK3 = k1_relat_1(sK6) | ~spl9_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),k1_relat_1(X0)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f16,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) & r2_hidden(sK7(X0,X1),k1_relat_1(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.21/0.54  fof(f270,plain,(
% 0.21/0.54    ( ! [X0] : (k1_relat_1(X0) != sK3 | k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7(sK6,X0),sK3)) ) | ~spl9_8),
% 0.21/0.54    inference(forward_demodulation,[],[f269,f155])).
% 0.21/0.54  fof(f269,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f268,f86])).
% 0.21/0.54  fof(f268,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.21/0.54    inference(subsumption_resolution,[],[f264,f49])).
% 0.21/0.54  fof(f264,plain,(
% 0.21/0.54    ( ! [X0] : (k1_funct_1(sK5,sK7(sK6,X0)) != k1_funct_1(X0,sK7(sK6,X0)) | sK6 = X0 | k1_relat_1(X0) != k1_relat_1(sK6) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK6) | ~v1_relat_1(sK6) | ~r2_hidden(sK7(sK6,X0),sK3)) )),
% 0.21/0.54    inference(superposition,[],[f56,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X4] : (k1_funct_1(sK5,X4) = k1_funct_1(sK6,X4) | ~r2_hidden(X4,sK3)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_funct_1(X0,sK7(X0,X1)) != k1_funct_1(X1,sK7(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f33])).
% 0.21/0.54  fof(f306,plain,(
% 0.21/0.54    ~spl9_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f305])).
% 0.21/0.54  fof(f305,plain,(
% 0.21/0.54    $false | ~spl9_10),
% 0.21/0.54    inference(subsumption_resolution,[],[f294,f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    r2_relset_1(sK3,sK4,sK5,sK5)),
% 0.21/0.54    inference(resolution,[],[f83,f48])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(nnf_transformation,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.54    inference(flattening,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.54  fof(f294,plain,(
% 0.21/0.54    ~r2_relset_1(sK3,sK4,sK5,sK5) | ~spl9_10),
% 0.21/0.54    inference(backward_demodulation,[],[f53,f223])).
% 0.21/0.54  fof(f223,plain,(
% 0.21/0.54    sK5 = sK6 | ~spl9_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f221])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~r2_relset_1(sK3,sK4,sK5,sK6)),
% 0.21/0.54    inference(cnf_transformation,[],[f31])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    spl9_8 | spl9_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f151,f147,f153])).
% 0.21/0.54  fof(f151,plain,(
% 0.21/0.54    sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.54    inference(subsumption_resolution,[],[f138,f50])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ~v1_funct_2(sK6,sK3,sK4) | sP0(sK3,sK4) | sK3 = k1_relat_1(sK6)),
% 0.21/0.54    inference(resolution,[],[f131,f51])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (6283)------------------------------
% 0.21/0.54  % (6283)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6283)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (6283)Memory used [KB]: 6268
% 0.21/0.54  % (6283)Time elapsed: 0.103 s
% 0.21/0.54  % (6283)------------------------------
% 0.21/0.54  % (6283)------------------------------
% 0.21/0.54  % (6284)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (6278)Success in time 0.184 s
%------------------------------------------------------------------------------
