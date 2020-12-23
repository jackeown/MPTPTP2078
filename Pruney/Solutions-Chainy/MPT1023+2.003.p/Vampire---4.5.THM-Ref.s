%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.40s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 415 expanded)
%              Number of leaves         :   28 ( 136 expanded)
%              Depth                    :   26
%              Number of atoms          :  513 (2611 expanded)
%              Number of equality atoms :  115 ( 416 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f154,f156,f230,f249,f274,f367,f390,f391,f392,f441])).

% (25949)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% (25946)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
fof(f441,plain,
    ( ~ spl7_2
    | spl7_8
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f440])).

fof(f440,plain,
    ( $false
    | ~ spl7_2
    | spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f439,f224])).

fof(f224,plain,
    ( sK2 != sK3
    | spl7_8 ),
    inference(avatar_component_clause,[],[f223])).

fof(f223,plain,
    ( spl7_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f439,plain,
    ( sK2 = sK3
    | ~ spl7_2
    | ~ spl7_10 ),
    inference(resolution,[],[f395,f234])).

fof(f234,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl7_10
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = X0 )
    | ~ spl7_2 ),
    inference(resolution,[],[f106,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f106,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl7_2
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f392,plain,
    ( ~ spl7_1
    | spl7_10 ),
    inference(avatar_split_clause,[],[f264,f232,f100])).

fof(f100,plain,
    ( spl7_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f264,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f55,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
    & ! [X4] :
        ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
        | ~ m1_subset_1(X4,sK0) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).

fof(f40,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
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
              | ~ m1_subset_1(X4,sK0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          & v1_funct_2(X3,sK0,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ~ r2_relset_1(sK0,sK1,sK2,X3)
        & ! [X4] :
            ( k1_funct_1(X3,X4) = k1_funct_1(sK2,X4)
            | ~ m1_subset_1(X4,sK0) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        & v1_funct_2(X3,sK0,sK1)
        & v1_funct_1(X3) )
   => ( ~ r2_relset_1(sK0,sK1,sK2,sK3)
      & ! [X4] :
          ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
          | ~ m1_subset_1(X4,sK0) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).

% (25948)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f391,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f357,f104,f100])).

fof(f357,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f52,f64])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f390,plain,
    ( ~ spl7_3
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f389])).

fof(f389,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f388,f193])).

fof(f193,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_3 ),
    inference(forward_demodulation,[],[f93,f112])).

fof(f112,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl7_3
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f93,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f52,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

% (25930)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f388,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f387,f202])).

fof(f202,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f131,f141])).

fof(f141,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl7_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f131,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f55,f72])).

fof(f387,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ spl7_3
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f386,f92])).

fof(f92,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f52,f71])).

% (25934)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f386,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f385,f50])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f385,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f384,f130])).

fof(f130,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f71])).

fof(f384,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f383,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f383,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f382,f224])).

fof(f382,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(superposition,[],[f61,f374])).

fof(f374,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f371,f56])).

fof(f56,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f371,plain,
    ( m1_subset_1(sK4(sK2,sK3),sK0)
    | ~ spl7_3
    | ~ spl7_9 ),
    inference(resolution,[],[f229,f212])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | m1_subset_1(X0,sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f194,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f194,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl7_3 ),
    inference(backward_demodulation,[],[f182,f193])).

fof(f182,plain,(
    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f181,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f181,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f180,f92])).

fof(f180,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f63,f128])).

fof(f128,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f127,f92])).

fof(f127,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f94,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f94,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f52,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

% (25929)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

% (25931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% (25933)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (25940)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f229,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl7_9
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

% (25942)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f61,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f367,plain,
    ( spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f366,f114,f110])).

fof(f114,plain,
    ( spl7_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f366,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f361,f51])).

fof(f51,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f361,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f274,plain,
    ( spl7_7
    | spl7_4 ),
    inference(avatar_split_clause,[],[f273,f114,f139])).

fof(f273,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f268,f54])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f268,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f55,f74])).

fof(f249,plain,
    ( ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f242,f125])).

fof(f125,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl7_6
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f242,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f57,f225])).

fof(f225,plain,
    ( sK2 = sK3
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f223])).

fof(f57,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f230,plain,
    ( spl7_8
    | spl7_9
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f221,f139,f110,f227,f223])).

fof(f221,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f220,f130])).

fof(f220,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f219,f53])).

fof(f219,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_3
    | ~ spl7_7 ),
    inference(superposition,[],[f201,f202])).

fof(f201,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f200,f92])).

fof(f200,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f197,f50])).

fof(f197,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_3 ),
    inference(superposition,[],[f60,f193])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f156,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f155])).

fof(f155,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f121,f97])).

fof(f97,plain,(
    ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f52,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP6(X1,X0) ) ),
    inference(general_splitting,[],[f81,f89_D])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f89_D])).

fof(f89_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f121,plain,
    ( sP6(sK1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl7_5
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f154,plain,
    ( spl7_1
    | ~ spl7_4 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl7_1
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f150,f58])).

fof(f58,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f150,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_1
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f102,f116])).

fof(f116,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f102,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f126,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f96,f123,f119])).

fof(f96,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP6(sK1,sK0) ),
    inference(resolution,[],[f52,f89])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:57:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (25935)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.50  % (25927)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.50  % (25939)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.51  % (25928)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.52  % (25932)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (25947)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (25928)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.53  % (25941)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.25/0.53  % (25937)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.25/0.53  % (25936)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.25/0.53  % SZS output start Proof for theBenchmark
% 1.25/0.53  fof(f442,plain,(
% 1.25/0.53    $false),
% 1.25/0.53    inference(avatar_sat_refutation,[],[f126,f154,f156,f230,f249,f274,f367,f390,f391,f392,f441])).
% 1.25/0.53  % (25949)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.25/0.53  % (25946)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.25/0.54  fof(f441,plain,(
% 1.25/0.54    ~spl7_2 | spl7_8 | ~spl7_10),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f440])).
% 1.25/0.54  fof(f440,plain,(
% 1.25/0.54    $false | (~spl7_2 | spl7_8 | ~spl7_10)),
% 1.25/0.54    inference(subsumption_resolution,[],[f439,f224])).
% 1.25/0.54  fof(f224,plain,(
% 1.25/0.54    sK2 != sK3 | spl7_8),
% 1.25/0.54    inference(avatar_component_clause,[],[f223])).
% 1.25/0.54  fof(f223,plain,(
% 1.25/0.54    spl7_8 <=> sK2 = sK3),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.25/0.54  fof(f439,plain,(
% 1.25/0.54    sK2 = sK3 | (~spl7_2 | ~spl7_10)),
% 1.25/0.54    inference(resolution,[],[f395,f234])).
% 1.25/0.54  fof(f234,plain,(
% 1.25/0.54    v1_xboole_0(sK3) | ~spl7_10),
% 1.25/0.54    inference(avatar_component_clause,[],[f232])).
% 1.25/0.54  fof(f232,plain,(
% 1.25/0.54    spl7_10 <=> v1_xboole_0(sK3)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.25/0.54  fof(f395,plain,(
% 1.25/0.54    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) ) | ~spl7_2),
% 1.25/0.54    inference(resolution,[],[f106,f70])).
% 1.25/0.54  fof(f70,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f30])).
% 1.25/0.54  fof(f30,plain,(
% 1.25/0.54    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f2])).
% 1.25/0.54  fof(f2,axiom,(
% 1.25/0.54    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 1.25/0.54  fof(f106,plain,(
% 1.25/0.54    v1_xboole_0(sK2) | ~spl7_2),
% 1.25/0.54    inference(avatar_component_clause,[],[f104])).
% 1.25/0.54  fof(f104,plain,(
% 1.25/0.54    spl7_2 <=> v1_xboole_0(sK2)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.25/0.54  fof(f392,plain,(
% 1.25/0.54    ~spl7_1 | spl7_10),
% 1.25/0.54    inference(avatar_split_clause,[],[f264,f232,f100])).
% 1.25/0.54  fof(f100,plain,(
% 1.25/0.54    spl7_1 <=> v1_xboole_0(sK1)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.25/0.54  fof(f264,plain,(
% 1.25/0.54    v1_xboole_0(sK3) | ~v1_xboole_0(sK1)),
% 1.25/0.54    inference(resolution,[],[f55,f64])).
% 1.25/0.54  fof(f64,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f26])).
% 1.25/0.54  fof(f26,plain,(
% 1.25/0.54    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 1.25/0.54    inference(ennf_transformation,[],[f13])).
% 1.25/0.54  fof(f13,axiom,(
% 1.25/0.54    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 1.25/0.54  fof(f55,plain,(
% 1.25/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.25/0.54    inference(cnf_transformation,[],[f42])).
% 1.25/0.54  fof(f42,plain,(
% 1.25/0.54    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.25/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f41,f40])).
% 1.25/0.54  fof(f40,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f41,plain,(
% 1.25/0.54    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.25/0.54    introduced(choice_axiom,[])).
% 1.25/0.54  fof(f22,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.25/0.54    inference(flattening,[],[f21])).
% 1.25/0.54  fof(f21,plain,(
% 1.25/0.54    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.25/0.54    inference(ennf_transformation,[],[f18])).
% 1.25/0.54  fof(f18,negated_conjecture,(
% 1.25/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.25/0.54    inference(negated_conjecture,[],[f17])).
% 1.25/0.54  fof(f17,conjecture,(
% 1.25/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_funct_2)).
% 1.25/0.54  % (25948)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.25/0.54  fof(f391,plain,(
% 1.25/0.54    ~spl7_1 | spl7_2),
% 1.25/0.54    inference(avatar_split_clause,[],[f357,f104,f100])).
% 1.25/0.54  fof(f357,plain,(
% 1.25/0.54    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 1.25/0.54    inference(resolution,[],[f52,f64])).
% 1.25/0.54  fof(f52,plain,(
% 1.25/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.25/0.54    inference(cnf_transformation,[],[f42])).
% 1.25/0.54  fof(f390,plain,(
% 1.25/0.54    ~spl7_3 | ~spl7_7 | spl7_8 | ~spl7_9),
% 1.25/0.54    inference(avatar_contradiction_clause,[],[f389])).
% 1.25/0.54  fof(f389,plain,(
% 1.25/0.54    $false | (~spl7_3 | ~spl7_7 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f388,f193])).
% 1.25/0.54  fof(f193,plain,(
% 1.25/0.54    sK0 = k1_relat_1(sK2) | ~spl7_3),
% 1.25/0.54    inference(forward_demodulation,[],[f93,f112])).
% 1.25/0.54  fof(f112,plain,(
% 1.25/0.54    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_3),
% 1.25/0.54    inference(avatar_component_clause,[],[f110])).
% 1.25/0.54  fof(f110,plain,(
% 1.25/0.54    spl7_3 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.25/0.54  fof(f93,plain,(
% 1.25/0.54    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 1.25/0.54    inference(resolution,[],[f52,f72])).
% 1.25/0.54  fof(f72,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f32])).
% 1.25/0.54  % (25930)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.25/0.54  fof(f32,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.54    inference(ennf_transformation,[],[f14])).
% 1.25/0.54  fof(f14,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.25/0.54  fof(f388,plain,(
% 1.25/0.54    sK0 != k1_relat_1(sK2) | (~spl7_3 | ~spl7_7 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(forward_demodulation,[],[f387,f202])).
% 1.25/0.54  fof(f202,plain,(
% 1.25/0.54    sK0 = k1_relat_1(sK3) | ~spl7_7),
% 1.25/0.54    inference(forward_demodulation,[],[f131,f141])).
% 1.25/0.54  fof(f141,plain,(
% 1.25/0.54    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_7),
% 1.25/0.54    inference(avatar_component_clause,[],[f139])).
% 1.25/0.54  fof(f139,plain,(
% 1.25/0.54    spl7_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.25/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.25/0.54  fof(f131,plain,(
% 1.25/0.54    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 1.25/0.54    inference(resolution,[],[f55,f72])).
% 1.25/0.54  fof(f387,plain,(
% 1.25/0.54    k1_relat_1(sK2) != k1_relat_1(sK3) | (~spl7_3 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f386,f92])).
% 1.25/0.54  fof(f92,plain,(
% 1.25/0.54    v1_relat_1(sK2)),
% 1.25/0.54    inference(resolution,[],[f52,f71])).
% 1.25/0.54  % (25934)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.25/0.54  fof(f71,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f31])).
% 1.25/0.54  fof(f31,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.54    inference(ennf_transformation,[],[f11])).
% 1.25/0.54  fof(f11,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.25/0.54  fof(f386,plain,(
% 1.25/0.54    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f385,f50])).
% 1.25/0.54  fof(f50,plain,(
% 1.25/0.54    v1_funct_1(sK2)),
% 1.25/0.54    inference(cnf_transformation,[],[f42])).
% 1.25/0.54  fof(f385,plain,(
% 1.25/0.54    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f384,f130])).
% 1.25/0.54  fof(f130,plain,(
% 1.25/0.54    v1_relat_1(sK3)),
% 1.25/0.54    inference(resolution,[],[f55,f71])).
% 1.25/0.54  fof(f384,plain,(
% 1.25/0.54    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f383,f53])).
% 1.25/0.54  fof(f53,plain,(
% 1.25/0.54    v1_funct_1(sK3)),
% 1.25/0.54    inference(cnf_transformation,[],[f42])).
% 1.25/0.54  fof(f383,plain,(
% 1.25/0.54    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | spl7_8 | ~spl7_9)),
% 1.25/0.54    inference(subsumption_resolution,[],[f382,f224])).
% 1.25/0.54  fof(f382,plain,(
% 1.25/0.54    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | ~spl7_9)),
% 1.25/0.54    inference(trivial_inequality_removal,[],[f381])).
% 1.25/0.54  fof(f381,plain,(
% 1.25/0.54    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl7_3 | ~spl7_9)),
% 1.25/0.54    inference(superposition,[],[f61,f374])).
% 1.25/0.54  fof(f374,plain,(
% 1.25/0.54    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | (~spl7_3 | ~spl7_9)),
% 1.25/0.54    inference(resolution,[],[f371,f56])).
% 1.25/0.54  fof(f56,plain,(
% 1.25/0.54    ( ! [X4] : (~m1_subset_1(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f42])).
% 1.25/0.54  fof(f371,plain,(
% 1.25/0.54    m1_subset_1(sK4(sK2,sK3),sK0) | (~spl7_3 | ~spl7_9)),
% 1.25/0.54    inference(resolution,[],[f229,f212])).
% 1.25/0.54  fof(f212,plain,(
% 1.25/0.54    ( ! [X0] : (~r2_hidden(X0,sK0) | m1_subset_1(X0,sK0)) ) | ~spl7_3),
% 1.25/0.54    inference(resolution,[],[f194,f80])).
% 1.25/0.54  fof(f80,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f37])).
% 1.25/0.54  fof(f37,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.25/0.54    inference(flattening,[],[f36])).
% 1.25/0.54  fof(f36,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.25/0.54    inference(ennf_transformation,[],[f7])).
% 1.25/0.54  fof(f7,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.25/0.54  fof(f194,plain,(
% 1.25/0.54    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl7_3),
% 1.25/0.54    inference(backward_demodulation,[],[f182,f193])).
% 1.25/0.54  fof(f182,plain,(
% 1.25/0.54    m1_subset_1(k1_relat_1(sK2),k1_zfmisc_1(sK0))),
% 1.25/0.54    inference(resolution,[],[f181,f66])).
% 1.25/0.54  fof(f66,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.25/0.54    inference(cnf_transformation,[],[f29])).
% 1.25/0.54  fof(f29,plain,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.25/0.54    inference(ennf_transformation,[],[f19])).
% 1.25/0.54  fof(f19,plain,(
% 1.25/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 1.25/0.54    inference(unused_predicate_definition_removal,[],[f6])).
% 1.25/0.54  fof(f6,axiom,(
% 1.25/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.25/0.54  fof(f181,plain,(
% 1.25/0.54    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.25/0.54    inference(subsumption_resolution,[],[f180,f92])).
% 1.25/0.54  fof(f180,plain,(
% 1.25/0.54    r1_tarski(k1_relat_1(sK2),sK0) | ~v1_relat_1(sK2)),
% 1.25/0.54    inference(superposition,[],[f63,f128])).
% 1.25/0.54  fof(f128,plain,(
% 1.25/0.54    sK2 = k7_relat_1(sK2,sK0)),
% 1.25/0.54    inference(subsumption_resolution,[],[f127,f92])).
% 1.25/0.54  fof(f127,plain,(
% 1.25/0.54    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 1.25/0.54    inference(resolution,[],[f94,f65])).
% 1.25/0.54  fof(f65,plain,(
% 1.25/0.54    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f28])).
% 1.25/0.54  fof(f28,plain,(
% 1.25/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.25/0.54    inference(flattening,[],[f27])).
% 1.25/0.54  fof(f27,plain,(
% 1.25/0.54    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.25/0.54    inference(ennf_transformation,[],[f8])).
% 1.25/0.54  fof(f8,axiom,(
% 1.25/0.54    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.25/0.54  fof(f94,plain,(
% 1.25/0.54    v4_relat_1(sK2,sK0)),
% 1.25/0.54    inference(resolution,[],[f52,f73])).
% 1.25/0.54  fof(f73,plain,(
% 1.25/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f33])).
% 1.25/0.54  fof(f33,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.25/0.54    inference(ennf_transformation,[],[f20])).
% 1.25/0.54  fof(f20,plain,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.25/0.54    inference(pure_predicate_removal,[],[f12])).
% 1.25/0.54  fof(f12,axiom,(
% 1.25/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.25/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.25/0.54  % (25929)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.25/0.54  fof(f63,plain,(
% 1.25/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 1.25/0.54    inference(cnf_transformation,[],[f25])).
% 1.25/0.54  % (25931)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.40/0.55  % (25933)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.40/0.55  % (25940)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.40/0.55  fof(f25,plain,(
% 1.40/0.55    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 1.40/0.55    inference(ennf_transformation,[],[f9])).
% 1.40/0.55  fof(f9,axiom,(
% 1.40/0.55    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 1.40/0.55  fof(f229,plain,(
% 1.40/0.55    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_9),
% 1.40/0.55    inference(avatar_component_clause,[],[f227])).
% 1.40/0.55  fof(f227,plain,(
% 1.40/0.55    spl7_9 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.40/0.55  % (25942)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.40/0.55  fof(f61,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f44,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f43])).
% 1.40/0.55  fof(f43,plain,(
% 1.40/0.55    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 1.40/0.55    introduced(choice_axiom,[])).
% 1.40/0.55  fof(f24,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.40/0.55    inference(flattening,[],[f23])).
% 1.40/0.55  fof(f23,plain,(
% 1.40/0.55    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.40/0.55    inference(ennf_transformation,[],[f10])).
% 1.40/0.55  fof(f10,axiom,(
% 1.40/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.40/0.55  fof(f367,plain,(
% 1.40/0.55    spl7_3 | spl7_4),
% 1.40/0.55    inference(avatar_split_clause,[],[f366,f114,f110])).
% 1.40/0.55  fof(f114,plain,(
% 1.40/0.55    spl7_4 <=> k1_xboole_0 = sK1),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.40/0.55  fof(f366,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    inference(subsumption_resolution,[],[f361,f51])).
% 1.40/0.55  fof(f51,plain,(
% 1.40/0.55    v1_funct_2(sK2,sK0,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f42])).
% 1.40/0.55  fof(f361,plain,(
% 1.40/0.55    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.40/0.55    inference(resolution,[],[f52,f74])).
% 1.40/0.55  fof(f74,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.40/0.55    inference(cnf_transformation,[],[f49])).
% 1.40/0.55  fof(f49,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(nnf_transformation,[],[f35])).
% 1.40/0.55  fof(f35,plain,(
% 1.40/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f34])).
% 1.40/0.55  fof(f34,plain,(
% 1.40/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(ennf_transformation,[],[f16])).
% 1.40/0.55  fof(f16,axiom,(
% 1.40/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.40/0.55  fof(f274,plain,(
% 1.40/0.55    spl7_7 | spl7_4),
% 1.40/0.55    inference(avatar_split_clause,[],[f273,f114,f139])).
% 1.40/0.55  fof(f273,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.40/0.55    inference(subsumption_resolution,[],[f268,f54])).
% 1.40/0.55  fof(f54,plain,(
% 1.40/0.55    v1_funct_2(sK3,sK0,sK1)),
% 1.40/0.55    inference(cnf_transformation,[],[f42])).
% 1.40/0.55  fof(f268,plain,(
% 1.40/0.55    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.40/0.55    inference(resolution,[],[f55,f74])).
% 1.40/0.55  fof(f249,plain,(
% 1.40/0.55    ~spl7_6 | ~spl7_8),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f248])).
% 1.40/0.55  fof(f248,plain,(
% 1.40/0.55    $false | (~spl7_6 | ~spl7_8)),
% 1.40/0.55    inference(subsumption_resolution,[],[f242,f125])).
% 1.40/0.55  fof(f125,plain,(
% 1.40/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_6),
% 1.40/0.55    inference(avatar_component_clause,[],[f123])).
% 1.40/0.55  fof(f123,plain,(
% 1.40/0.55    spl7_6 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.40/0.55  fof(f242,plain,(
% 1.40/0.55    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_8),
% 1.40/0.55    inference(backward_demodulation,[],[f57,f225])).
% 1.40/0.55  fof(f225,plain,(
% 1.40/0.55    sK2 = sK3 | ~spl7_8),
% 1.40/0.55    inference(avatar_component_clause,[],[f223])).
% 1.40/0.55  fof(f57,plain,(
% 1.40/0.55    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.40/0.55    inference(cnf_transformation,[],[f42])).
% 1.40/0.55  fof(f230,plain,(
% 1.40/0.55    spl7_8 | spl7_9 | ~spl7_3 | ~spl7_7),
% 1.40/0.55    inference(avatar_split_clause,[],[f221,f139,f110,f227,f223])).
% 1.40/0.55  fof(f221,plain,(
% 1.40/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | (~spl7_3 | ~spl7_7)),
% 1.40/0.55    inference(subsumption_resolution,[],[f220,f130])).
% 1.40/0.55  fof(f220,plain,(
% 1.40/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_7)),
% 1.40/0.55    inference(subsumption_resolution,[],[f219,f53])).
% 1.40/0.55  fof(f219,plain,(
% 1.40/0.55    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_7)),
% 1.40/0.55    inference(trivial_inequality_removal,[],[f218])).
% 1.40/0.55  fof(f218,plain,(
% 1.40/0.55    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_3 | ~spl7_7)),
% 1.40/0.55    inference(superposition,[],[f201,f202])).
% 1.40/0.55  fof(f201,plain,(
% 1.40/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl7_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f200,f92])).
% 1.40/0.55  fof(f200,plain,(
% 1.40/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 1.40/0.55    inference(subsumption_resolution,[],[f197,f50])).
% 1.40/0.55  fof(f197,plain,(
% 1.40/0.55    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_3),
% 1.40/0.55    inference(superposition,[],[f60,f193])).
% 1.40/0.55  fof(f60,plain,(
% 1.40/0.55    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f44])).
% 1.40/0.55  fof(f156,plain,(
% 1.40/0.55    ~spl7_5),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f155])).
% 1.40/0.55  fof(f155,plain,(
% 1.40/0.55    $false | ~spl7_5),
% 1.40/0.55    inference(subsumption_resolution,[],[f121,f97])).
% 1.40/0.55  fof(f97,plain,(
% 1.40/0.55    ~sP6(sK1,sK0)),
% 1.40/0.55    inference(resolution,[],[f52,f90])).
% 1.40/0.55  fof(f90,plain,(
% 1.40/0.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP6(X1,X0)) )),
% 1.40/0.55    inference(general_splitting,[],[f81,f89_D])).
% 1.40/0.55  fof(f89,plain,(
% 1.40/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP6(X1,X0)) )),
% 1.40/0.55    inference(cnf_transformation,[],[f89_D])).
% 1.40/0.55  fof(f89_D,plain,(
% 1.40/0.55    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP6(X1,X0)) )),
% 1.40/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.40/0.55  fof(f81,plain,(
% 1.40/0.55    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.40/0.55    inference(cnf_transformation,[],[f39])).
% 1.40/0.55  fof(f39,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.40/0.55    inference(flattening,[],[f38])).
% 1.40/0.55  fof(f38,plain,(
% 1.40/0.55    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.40/0.55    inference(ennf_transformation,[],[f15])).
% 1.40/0.55  fof(f15,axiom,(
% 1.40/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 1.40/0.55  fof(f121,plain,(
% 1.40/0.55    sP6(sK1,sK0) | ~spl7_5),
% 1.40/0.55    inference(avatar_component_clause,[],[f119])).
% 1.40/0.55  fof(f119,plain,(
% 1.40/0.55    spl7_5 <=> sP6(sK1,sK0)),
% 1.40/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.40/0.55  fof(f154,plain,(
% 1.40/0.55    spl7_1 | ~spl7_4),
% 1.40/0.55    inference(avatar_contradiction_clause,[],[f153])).
% 1.40/0.55  fof(f153,plain,(
% 1.40/0.55    $false | (spl7_1 | ~spl7_4)),
% 1.40/0.55    inference(subsumption_resolution,[],[f150,f58])).
% 1.40/0.55  fof(f58,plain,(
% 1.40/0.55    v1_xboole_0(k1_xboole_0)),
% 1.40/0.55    inference(cnf_transformation,[],[f1])).
% 1.40/0.55  fof(f1,axiom,(
% 1.40/0.55    v1_xboole_0(k1_xboole_0)),
% 1.40/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.40/0.55  fof(f150,plain,(
% 1.40/0.55    ~v1_xboole_0(k1_xboole_0) | (spl7_1 | ~spl7_4)),
% 1.40/0.55    inference(backward_demodulation,[],[f102,f116])).
% 1.40/0.55  fof(f116,plain,(
% 1.40/0.55    k1_xboole_0 = sK1 | ~spl7_4),
% 1.40/0.55    inference(avatar_component_clause,[],[f114])).
% 1.40/0.55  fof(f102,plain,(
% 1.40/0.55    ~v1_xboole_0(sK1) | spl7_1),
% 1.40/0.55    inference(avatar_component_clause,[],[f100])).
% 1.40/0.55  fof(f126,plain,(
% 1.40/0.55    spl7_5 | spl7_6),
% 1.40/0.55    inference(avatar_split_clause,[],[f96,f123,f119])).
% 1.40/0.55  fof(f96,plain,(
% 1.40/0.55    r2_relset_1(sK0,sK1,sK2,sK2) | sP6(sK1,sK0)),
% 1.40/0.55    inference(resolution,[],[f52,f89])).
% 1.40/0.55  % SZS output end Proof for theBenchmark
% 1.40/0.55  % (25928)------------------------------
% 1.40/0.55  % (25928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (25928)Termination reason: Refutation
% 1.40/0.55  
% 1.40/0.55  % (25928)Memory used [KB]: 10746
% 1.40/0.55  % (25928)Time elapsed: 0.104 s
% 1.40/0.55  % (25928)------------------------------
% 1.40/0.55  % (25928)------------------------------
% 1.40/0.55  % (25951)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.55  % (25924)Success in time 0.181 s
%------------------------------------------------------------------------------
