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
% DateTime   : Thu Dec  3 13:01:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 360 expanded)
%              Number of leaves         :   23 ( 121 expanded)
%              Depth                    :   17
%              Number of atoms          :  449 (2254 expanded)
%              Number of equality atoms :  112 ( 379 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f373,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f140,f142,f151,f194,f205,f211,f233,f282,f286,f372])).

fof(f372,plain,
    ( ~ spl7_1
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f370,f165])).

fof(f165,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(forward_demodulation,[],[f82,f92])).

fof(f92,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl7_1
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f82,plain,(
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f43,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f370,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl7_7
    | spl7_8
    | ~ spl7_9 ),
    inference(forward_demodulation,[],[f369,f172])).

fof(f172,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_7 ),
    inference(forward_demodulation,[],[f117,f127])).

fof(f127,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl7_7
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f117,plain,(
    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f46,f63])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f33])).

fof(f369,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f368,f83])).

fof(f83,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f43,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f368,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f367,f41])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f367,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f366,f118])).

fof(f118,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f46,f62])).

fof(f366,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f365,f44])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f365,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f364,f188])).

fof(f188,plain,
    ( sK2 != sK3
    | spl7_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl7_8
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f364,plain,
    ( sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f363])).

% (9524)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (9522)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f363,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | k1_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl7_9 ),
    inference(superposition,[],[f52,f362])).

fof(f362,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_9 ),
    inference(resolution,[],[f47,f193])).

fof(f193,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_9
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f47,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
        & r2_hidden(sK4(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f286,plain,
    ( ~ spl7_4
    | spl7_8
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | ~ spl7_4
    | spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f283,f250])).

fof(f250,plain,
    ( k1_xboole_0 != sK3
    | ~ spl7_4
    | spl7_8 ),
    inference(backward_demodulation,[],[f188,f236])).

fof(f236,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_4 ),
    inference(resolution,[],[f213,f49])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f213,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | sK2 = X0 )
    | ~ spl7_4 ),
    inference(resolution,[],[f105,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f105,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_4
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f283,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_4
    | ~ spl7_10 ),
    inference(resolution,[],[f209,f251])).

fof(f251,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_4 ),
    inference(backward_demodulation,[],[f213,f236])).

fof(f209,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl7_10
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f282,plain,
    ( ~ spl7_3
    | spl7_10 ),
    inference(avatar_split_clause,[],[f228,f207,f99])).

fof(f99,plain,
    ( spl7_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f228,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f46,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f233,plain,
    ( spl7_7
    | spl7_2 ),
    inference(avatar_split_clause,[],[f232,f94,f125])).

fof(f94,plain,
    ( spl7_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f232,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(subsumption_resolution,[],[f225,f45])).

fof(f45,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f225,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3) ),
    inference(resolution,[],[f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f211,plain,
    ( ~ spl7_3
    | spl7_4 ),
    inference(avatar_split_clause,[],[f146,f103,f99])).

fof(f146,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[],[f43,f53])).

fof(f205,plain,
    ( ~ spl7_6
    | ~ spl7_8 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8 ),
    inference(subsumption_resolution,[],[f198,f114])).

fof(f114,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl7_6
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f198,plain,
    ( ~ r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_8 ),
    inference(backward_demodulation,[],[f48,f189])).

fof(f189,plain,
    ( sK2 = sK3
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f187])).

fof(f48,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f194,plain,
    ( spl7_8
    | spl7_9
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f185,f125,f90,f191,f187])).

fof(f185,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f184,f118])).

fof(f184,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f183,f44])).

fof(f183,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(trivial_inequality_removal,[],[f182])).

fof(f182,plain,
    ( sK0 != sK0
    | r2_hidden(sK4(sK2,sK3),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_1
    | ~ spl7_7 ),
    inference(superposition,[],[f171,f172])).

fof(f171,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f170,f83])).

fof(f170,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f167,f41])).

fof(f167,plain,
    ( ! [X1] :
        ( k1_relat_1(X1) != sK0
        | r2_hidden(sK4(sK2,X1),sK0)
        | sK2 = X1
        | ~ v1_funct_1(X1)
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl7_1 ),
    inference(superposition,[],[f51,f165])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f151,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f150,f94,f90])).

fof(f150,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f143,f42])).

fof(f42,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f143,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f43,f64])).

fof(f142,plain,(
    ~ spl7_5 ),
    inference(avatar_contradiction_clause,[],[f141])).

fof(f141,plain,
    ( $false
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f110,f86])).

fof(f86,plain,(
    ~ sP6(sK1,sK0) ),
    inference(resolution,[],[f43,f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ sP6(X1,X0) ) ),
    inference(general_splitting,[],[f71,f79_D])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X2,X2)
      | sP6(X1,X0) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | r2_relset_1(X0,X1,X2,X2) )
    <=> ~ sP6(X1,X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f110,plain,
    ( sP6(sK1,sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl7_5
  <=> sP6(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f140,plain,
    ( ~ spl7_2
    | spl7_3 ),
    inference(avatar_contradiction_clause,[],[f139])).

fof(f139,plain,
    ( $false
    | ~ spl7_2
    | spl7_3 ),
    inference(subsumption_resolution,[],[f136,f49])).

fof(f136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_2
    | spl7_3 ),
    inference(backward_demodulation,[],[f101,f96])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK1)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f115,plain,
    ( spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f85,f112,f108])).

fof(f85,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | sP6(sK1,sK0) ),
    inference(resolution,[],[f43,f79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.45  % (9508)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.46  % (9507)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.47  % (9508)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f115,f140,f142,f151,f194,f205,f211,f233,f282,f286,f372])).
% 0.20/0.47  fof(f372,plain,(
% 0.20/0.47    ~spl7_1 | ~spl7_7 | spl7_8 | ~spl7_9),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f371])).
% 0.20/0.47  fof(f371,plain,(
% 0.20/0.47    $false | (~spl7_1 | ~spl7_7 | spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f370,f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK2) | ~spl7_1),
% 0.20/0.47    inference(forward_demodulation,[],[f82,f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl7_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl7_1 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f43,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f32,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ? [X3] : (~r2_relset_1(sK0,sK1,sK2,X3) & ! [X4] : (k1_funct_1(X3,X4) = k1_funct_1(sK2,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(X3,sK0,sK1) & v1_funct_1(X3)) => (~r2_relset_1(sK0,sK1,sK2,sK3) & ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~r2_hidden(X4,sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.47    inference(negated_conjecture,[],[f13])).
% 0.20/0.47  fof(f13,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    sK0 != k1_relat_1(sK2) | (~spl7_7 | spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(forward_demodulation,[],[f369,f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    sK0 = k1_relat_1(sK3) | ~spl7_7),
% 0.20/0.47    inference(forward_demodulation,[],[f117,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl7_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f125])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    spl7_7 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f46,f63])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK3) | (spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f368,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    v1_relat_1(sK2)),
% 0.20/0.47    inference(resolution,[],[f43,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f367,f41])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f367,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f366,f118])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    v1_relat_1(sK3)),
% 0.20/0.47    inference(resolution,[],[f46,f62])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f365,f44])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    v1_funct_1(sK3)),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f365,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl7_8 | ~spl7_9)),
% 0.20/0.47    inference(subsumption_resolution,[],[f364,f188])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    sK2 != sK3 | spl7_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f187])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    spl7_8 <=> sK2 = sK3),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.47  fof(f364,plain,(
% 0.20/0.47    sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_9),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f363])).
% 0.20/0.48  % (9524)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.48  % (9522)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.48  fof(f363,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | k1_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl7_9),
% 0.20/0.48    inference(superposition,[],[f52,f362])).
% 0.20/0.48  fof(f362,plain,(
% 0.20/0.48    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_9),
% 0.20/0.48    inference(resolution,[],[f47,f193])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_9),
% 0.20/0.48    inference(avatar_component_clause,[],[f191])).
% 0.20/0.48  fof(f191,plain,(
% 0.20/0.48    spl7_9 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1 | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (X0 = X1 | (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f20,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X1,X0] : (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) & r2_hidden(sK4(X0,X1),k1_relat_1(X0))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    ~spl7_4 | spl7_8 | ~spl7_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f285])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    $false | (~spl7_4 | spl7_8 | ~spl7_10)),
% 0.20/0.48    inference(subsumption_resolution,[],[f283,f250])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    k1_xboole_0 != sK3 | (~spl7_4 | spl7_8)),
% 0.20/0.48    inference(backward_demodulation,[],[f188,f236])).
% 0.20/0.48  fof(f236,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f213,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f213,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | sK2 = X0) ) | ~spl7_4),
% 0.20/0.48    inference(resolution,[],[f105,f57])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    v1_xboole_0(sK2) | ~spl7_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f103])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl7_4 <=> v1_xboole_0(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    k1_xboole_0 = sK3 | (~spl7_4 | ~spl7_10)),
% 0.20/0.48    inference(resolution,[],[f209,f251])).
% 0.20/0.48  fof(f251,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl7_4),
% 0.20/0.48    inference(backward_demodulation,[],[f213,f236])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | ~spl7_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f207])).
% 0.20/0.48  fof(f207,plain,(
% 0.20/0.48    spl7_10 <=> v1_xboole_0(sK3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    ~spl7_3 | spl7_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f228,f207,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl7_3 <=> v1_xboole_0(sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.48  fof(f228,plain,(
% 0.20/0.48    v1_xboole_0(sK3) | ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f46,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 0.20/0.48  fof(f233,plain,(
% 0.20/0.48    spl7_7 | spl7_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f232,f94,f125])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl7_2 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.48  fof(f232,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.48    inference(subsumption_resolution,[],[f225,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f225,plain,(
% 0.20/0.48    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.20/0.48    inference(resolution,[],[f46,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    ~spl7_3 | spl7_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f146,f103,f99])).
% 0.20/0.48  fof(f146,plain,(
% 0.20/0.48    v1_xboole_0(sK2) | ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(resolution,[],[f43,f53])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ~spl7_6 | ~spl7_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f204])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    $false | (~spl7_6 | ~spl7_8)),
% 0.20/0.48    inference(subsumption_resolution,[],[f198,f114])).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    spl7_6 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_8),
% 0.20/0.48    inference(backward_demodulation,[],[f48,f189])).
% 0.20/0.48  fof(f189,plain,(
% 0.20/0.48    sK2 = sK3 | ~spl7_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f187])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    spl7_8 | spl7_9 | ~spl7_1 | ~spl7_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f185,f125,f90,f191,f187])).
% 0.20/0.48  fof(f185,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | (~spl7_1 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f184,f118])).
% 0.20/0.48  fof(f184,plain,(
% 0.20/0.48    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_7)),
% 0.20/0.48    inference(subsumption_resolution,[],[f183,f44])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f182])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    sK0 != sK0 | r2_hidden(sK4(sK2,sK3),sK0) | sK2 = sK3 | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl7_1 | ~spl7_7)),
% 0.20/0.49    inference(superposition,[],[f171,f172])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) ) | ~spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f170,f83])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f167,f41])).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ( ! [X1] : (k1_relat_1(X1) != sK0 | r2_hidden(sK4(sK2,X1),sK0) | sK2 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl7_1),
% 0.20/0.49    inference(superposition,[],[f51,f165])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    spl7_1 | spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f150,f94,f90])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f143,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f33])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ~v1_funct_2(sK2,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.49    inference(resolution,[],[f43,f64])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ~spl7_5),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    $false | ~spl7_5),
% 0.20/0.49    inference(subsumption_resolution,[],[f110,f86])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    ~sP6(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f43,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~sP6(X1,X0)) )),
% 0.20/0.49    inference(general_splitting,[],[f71,f79_D])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2) | sP6(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f79_D])).
% 0.20/0.49  fof(f79_D,plain,(
% 0.20/0.49    ( ! [X0,X1] : (( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X2,X2)) ) <=> ~sP6(X1,X0)) )),
% 0.20/0.49    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1,X2,X3] : (r2_relset_1(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => r2_relset_1(X0,X1,X2,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    sP6(sK1,sK0) | ~spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    spl7_5 <=> sP6(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ~spl7_2 | spl7_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f139])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    $false | (~spl7_2 | spl7_3)),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f49])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ~v1_xboole_0(k1_xboole_0) | (~spl7_2 | spl7_3)),
% 0.20/0.49    inference(backward_demodulation,[],[f101,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    k1_xboole_0 = sK1 | ~spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1) | spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl7_5 | spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f112,f108])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    r2_relset_1(sK0,sK1,sK2,sK2) | sP6(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f43,f79])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (9508)------------------------------
% 0.20/0.49  % (9508)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (9508)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (9508)Memory used [KB]: 10746
% 0.20/0.49  % (9508)Time elapsed: 0.082 s
% 0.20/0.49  % (9508)------------------------------
% 0.20/0.49  % (9508)------------------------------
% 0.20/0.49  % (9506)Success in time 0.134 s
%------------------------------------------------------------------------------
