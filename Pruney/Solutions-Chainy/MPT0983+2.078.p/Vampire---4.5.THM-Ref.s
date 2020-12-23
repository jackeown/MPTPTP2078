%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:45 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 278 expanded)
%              Number of leaves         :   39 (  92 expanded)
%              Depth                    :    8
%              Number of atoms          :  465 (1165 expanded)
%              Number of equality atoms :   43 (  53 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f163,f167,f191,f209,f235,f238,f247,f250,f284,f286,f288,f292,f320,f325,f331,f338,f352,f365,f369,f374])).

fof(f374,plain,(
    spl7_28 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | spl7_28 ),
    inference(subsumption_resolution,[],[f112,f364])).

fof(f364,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl7_28 ),
    inference(avatar_component_clause,[],[f362])).

fof(f362,plain,
    ( spl7_28
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f112,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f369,plain,(
    spl7_8 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl7_8 ),
    inference(subsumption_resolution,[],[f106,f149])).

fof(f149,plain,
    ( ~ v1_relat_1(sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f106,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f70,f47])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f365,plain,
    ( spl7_1
    | ~ spl7_8
    | ~ spl7_28
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f355,f348,f362,f147,f90])).

fof(f90,plain,
    ( spl7_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f348,plain,
    ( spl7_26
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f355,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | v2_funct_2(sK3,sK0)
    | ~ spl7_26 ),
    inference(superposition,[],[f85,f350])).

fof(f350,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f348])).

fof(f85,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f352,plain,
    ( ~ spl7_15
    | spl7_26
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f346,f335,f348,f218])).

fof(f218,plain,
    ( spl7_15
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f335,plain,
    ( spl7_24
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f346,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl7_24 ),
    inference(superposition,[],[f71,f337])).

fof(f337,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f335])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f338,plain,
    ( spl7_24
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f332,f273,f218,f214,f277,f226,f222,f335])).

fof(f222,plain,
    ( spl7_16
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f226,plain,
    ( spl7_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f277,plain,
    ( spl7_21
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f214,plain,
    ( spl7_14
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f273,plain,
    ( spl7_20
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f332,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f331,plain,(
    spl7_23 ),
    inference(avatar_contradiction_clause,[],[f328])).

fof(f328,plain,
    ( $false
    | spl7_23 ),
    inference(unit_resulting_resolution,[],[f103,f319,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f319,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl7_23
  <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f103,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f101,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f101,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f69,f52])).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f325,plain,
    ( ~ spl7_6
    | spl7_10 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl7_6
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f158,f132,f64])).

fof(f132,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_6
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f158,plain,
    ( ~ v1_xboole_0(sK2)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl7_10
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f320,plain,
    ( spl7_6
    | ~ spl7_23
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f315,f269,f317,f131])).

fof(f269,plain,
    ( spl7_19
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl7_19 ),
    inference(forward_demodulation,[],[f258,f271])).

fof(f271,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f269])).

fof(f258,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK2)
      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ) ),
    inference(resolution,[],[f51,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f292,plain,(
    spl7_22 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl7_22 ),
    inference(unit_resulting_resolution,[],[f83,f283])).

fof(f283,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl7_22 ),
    inference(avatar_component_clause,[],[f281])).

fof(f281,plain,
    ( spl7_22
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f56,f53])).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f288,plain,(
    spl7_21 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | spl7_21 ),
    inference(subsumption_resolution,[],[f50,f279])).

fof(f279,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f277])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f286,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl7_20 ),
    inference(subsumption_resolution,[],[f46,f275])).

fof(f275,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl7_20 ),
    inference(avatar_component_clause,[],[f273])).

fof(f46,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f284,plain,
    ( spl7_2
    | spl7_19
    | ~ spl7_14
    | ~ spl7_15
    | ~ spl7_20
    | ~ spl7_16
    | ~ spl7_17
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f267,f188,f281,f277,f226,f222,f273,f218,f214,f269,f94])).

fof(f94,plain,
    ( spl7_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f188,plain,
    ( spl7_13
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f267,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl7_13 ),
    inference(superposition,[],[f76,f190])).

fof(f190,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f188])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f250,plain,(
    spl7_17 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl7_17 ),
    inference(subsumption_resolution,[],[f51,f228])).

fof(f228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f226])).

fof(f247,plain,(
    spl7_16 ),
    inference(avatar_contradiction_clause,[],[f246])).

% (15150)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
fof(f246,plain,
    ( $false
    | spl7_16 ),
    inference(subsumption_resolution,[],[f45,f224])).

fof(f224,plain,
    ( ~ v1_funct_1(sK3)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f238,plain,(
    spl7_15 ),
    inference(avatar_contradiction_clause,[],[f237])).

fof(f237,plain,
    ( $false
    | spl7_15 ),
    inference(subsumption_resolution,[],[f47,f220])).

fof(f220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl7_15 ),
    inference(avatar_component_clause,[],[f218])).

fof(f235,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | spl7_14 ),
    inference(subsumption_resolution,[],[f49,f216])).

fof(f216,plain,
    ( ~ v1_funct_1(sK2)
    | spl7_14 ),
    inference(avatar_component_clause,[],[f214])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f209,plain,(
    spl7_12 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl7_12 ),
    inference(unit_resulting_resolution,[],[f49,f45,f47,f51,f186,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f186,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl7_12
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f191,plain,
    ( ~ spl7_12
    | spl7_13 ),
    inference(avatar_split_clause,[],[f181,f188,f184])).

fof(f181,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f178,f48])).

fof(f178,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f79,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f54,f53])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

% (15170)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f167,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl7_11 ),
    inference(subsumption_resolution,[],[f107,f162])).

fof(f162,plain,
    ( ~ v1_relat_1(sK2)
    | spl7_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl7_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f107,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f70,f51])).

fof(f163,plain,
    ( ~ spl7_10
    | ~ spl7_11
    | spl7_2 ),
    inference(avatar_split_clause,[],[f141,f94,f160,f156])).

fof(f141,plain,
    ( v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_xboole_0(sK2) ),
    inference(resolution,[],[f139,f49])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f138,f58])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f138,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f60,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).

fof(f97,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f44,f94,f90])).

fof(f44,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:55:19 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.51  % (15161)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.18/0.52  % (15177)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.18/0.52  % (15169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.18/0.53  % (15149)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.18/0.54  % (15156)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.18/0.54  % (15161)Refutation found. Thanks to Tanya!
% 0.18/0.54  % SZS status Theorem for theBenchmark
% 0.18/0.54  % SZS output start Proof for theBenchmark
% 0.18/0.54  fof(f375,plain,(
% 0.18/0.54    $false),
% 0.18/0.54    inference(avatar_sat_refutation,[],[f97,f163,f167,f191,f209,f235,f238,f247,f250,f284,f286,f288,f292,f320,f325,f331,f338,f352,f365,f369,f374])).
% 0.18/0.54  fof(f374,plain,(
% 0.18/0.54    spl7_28),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f371])).
% 0.18/0.54  fof(f371,plain,(
% 0.18/0.54    $false | spl7_28),
% 0.18/0.54    inference(subsumption_resolution,[],[f112,f364])).
% 0.18/0.54  fof(f364,plain,(
% 0.18/0.54    ~v5_relat_1(sK3,sK0) | spl7_28),
% 0.18/0.54    inference(avatar_component_clause,[],[f362])).
% 0.18/0.54  fof(f362,plain,(
% 0.18/0.54    spl7_28 <=> v5_relat_1(sK3,sK0)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.18/0.54  fof(f112,plain,(
% 0.18/0.54    v5_relat_1(sK3,sK0)),
% 0.18/0.54    inference(resolution,[],[f73,f47])).
% 0.18/0.54  fof(f47,plain,(
% 0.18/0.54    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f23,plain,(
% 0.18/0.54    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.18/0.54    inference(flattening,[],[f22])).
% 0.18/0.54  fof(f22,plain,(
% 0.18/0.54    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.18/0.54    inference(ennf_transformation,[],[f21])).
% 0.18/0.54  fof(f21,negated_conjecture,(
% 0.18/0.54    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.18/0.54    inference(negated_conjecture,[],[f20])).
% 0.18/0.54  fof(f20,conjecture,(
% 0.18/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 0.18/0.54  fof(f73,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f34])).
% 0.18/0.54  fof(f34,plain,(
% 0.18/0.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f11])).
% 0.18/0.54  fof(f11,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.18/0.54  fof(f369,plain,(
% 0.18/0.54    spl7_8),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f366])).
% 0.18/0.54  fof(f366,plain,(
% 0.18/0.54    $false | spl7_8),
% 0.18/0.54    inference(subsumption_resolution,[],[f106,f149])).
% 0.18/0.54  fof(f149,plain,(
% 0.18/0.54    ~v1_relat_1(sK3) | spl7_8),
% 0.18/0.54    inference(avatar_component_clause,[],[f147])).
% 0.18/0.54  fof(f147,plain,(
% 0.18/0.54    spl7_8 <=> v1_relat_1(sK3)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.18/0.54  fof(f106,plain,(
% 0.18/0.54    v1_relat_1(sK3)),
% 0.18/0.54    inference(resolution,[],[f70,f47])).
% 0.18/0.54  fof(f70,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f32])).
% 0.18/0.54  fof(f32,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f10])).
% 0.18/0.54  fof(f10,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.18/0.54  fof(f365,plain,(
% 0.18/0.54    spl7_1 | ~spl7_8 | ~spl7_28 | ~spl7_26),
% 0.18/0.54    inference(avatar_split_clause,[],[f355,f348,f362,f147,f90])).
% 0.18/0.54  fof(f90,plain,(
% 0.18/0.54    spl7_1 <=> v2_funct_2(sK3,sK0)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.18/0.54  fof(f348,plain,(
% 0.18/0.54    spl7_26 <=> sK0 = k2_relat_1(sK3)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.18/0.54  fof(f355,plain,(
% 0.18/0.54    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | v2_funct_2(sK3,sK0) | ~spl7_26),
% 0.18/0.54    inference(superposition,[],[f85,f350])).
% 0.18/0.54  fof(f350,plain,(
% 0.18/0.54    sK0 = k2_relat_1(sK3) | ~spl7_26),
% 0.18/0.54    inference(avatar_component_clause,[],[f348])).
% 0.18/0.54  fof(f85,plain,(
% 0.18/0.54    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 0.18/0.54    inference(equality_resolution,[],[f67])).
% 0.18/0.54  fof(f67,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f30])).
% 0.18/0.54  fof(f30,plain,(
% 0.18/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.18/0.54    inference(flattening,[],[f29])).
% 0.18/0.54  fof(f29,plain,(
% 0.18/0.54    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.18/0.54    inference(ennf_transformation,[],[f15])).
% 0.18/0.54  fof(f15,axiom,(
% 0.18/0.54    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 0.18/0.54  fof(f352,plain,(
% 0.18/0.54    ~spl7_15 | spl7_26 | ~spl7_24),
% 0.18/0.54    inference(avatar_split_clause,[],[f346,f335,f348,f218])).
% 0.18/0.54  fof(f218,plain,(
% 0.18/0.54    spl7_15 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.18/0.54  fof(f335,plain,(
% 0.18/0.54    spl7_24 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.18/0.54  fof(f346,plain,(
% 0.18/0.54    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl7_24),
% 0.18/0.54    inference(superposition,[],[f71,f337])).
% 0.18/0.54  fof(f337,plain,(
% 0.18/0.54    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl7_24),
% 0.18/0.54    inference(avatar_component_clause,[],[f335])).
% 0.18/0.54  fof(f71,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f33])).
% 0.18/0.54  fof(f33,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(ennf_transformation,[],[f12])).
% 0.18/0.54  fof(f12,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.18/0.54  fof(f338,plain,(
% 0.18/0.54    spl7_24 | ~spl7_16 | ~spl7_17 | ~spl7_21 | ~spl7_14 | ~spl7_15 | ~spl7_20),
% 0.18/0.54    inference(avatar_split_clause,[],[f332,f273,f218,f214,f277,f226,f222,f335])).
% 0.18/0.54  fof(f222,plain,(
% 0.18/0.54    spl7_16 <=> v1_funct_1(sK3)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.18/0.54  fof(f226,plain,(
% 0.18/0.54    spl7_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.18/0.54  fof(f277,plain,(
% 0.18/0.54    spl7_21 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.18/0.54  fof(f214,plain,(
% 0.18/0.54    spl7_14 <=> v1_funct_1(sK2)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.18/0.54  fof(f273,plain,(
% 0.18/0.54    spl7_20 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.18/0.54  fof(f332,plain,(
% 0.18/0.54    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.18/0.54    inference(resolution,[],[f74,f48])).
% 0.18/0.54  fof(f48,plain,(
% 0.18/0.54    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f74,plain,(
% 0.18/0.54    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.18/0.54    inference(cnf_transformation,[],[f36])).
% 0.18/0.54  fof(f36,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.18/0.54    inference(flattening,[],[f35])).
% 0.18/0.54  fof(f35,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.18/0.54    inference(ennf_transformation,[],[f18])).
% 0.18/0.54  fof(f18,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.18/0.54  fof(f331,plain,(
% 0.18/0.54    spl7_23),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f328])).
% 0.18/0.54  fof(f328,plain,(
% 0.18/0.54    $false | spl7_23),
% 0.18/0.54    inference(unit_resulting_resolution,[],[f103,f319,f66])).
% 0.18/0.54  fof(f66,plain,(
% 0.18/0.54    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f28])).
% 0.18/0.54  fof(f28,plain,(
% 0.18/0.54    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.18/0.54    inference(ennf_transformation,[],[f4])).
% 0.18/0.54  fof(f4,axiom,(
% 0.18/0.54    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.18/0.54  fof(f319,plain,(
% 0.18/0.54    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | spl7_23),
% 0.18/0.54    inference(avatar_component_clause,[],[f317])).
% 0.18/0.54  fof(f317,plain,(
% 0.18/0.54    spl7_23 <=> v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.18/0.54  fof(f103,plain,(
% 0.18/0.54    v1_xboole_0(k1_xboole_0)),
% 0.18/0.54    inference(resolution,[],[f101,f64])).
% 0.18/0.54  fof(f64,plain,(
% 0.18/0.54    ( ! [X0] : (r2_hidden(sK6(X0),X0) | v1_xboole_0(X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f1])).
% 0.18/0.54  fof(f1,axiom,(
% 0.18/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.54  fof(f101,plain,(
% 0.18/0.54    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.18/0.54    inference(resolution,[],[f69,f52])).
% 0.18/0.54  fof(f52,plain,(
% 0.18/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f3])).
% 0.18/0.54  fof(f3,axiom,(
% 0.18/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.18/0.54  fof(f69,plain,(
% 0.18/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f31])).
% 0.18/0.54  fof(f31,plain,(
% 0.18/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.18/0.54    inference(ennf_transformation,[],[f9])).
% 0.18/0.54  fof(f9,axiom,(
% 0.18/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.18/0.54  fof(f325,plain,(
% 0.18/0.54    ~spl7_6 | spl7_10),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f323])).
% 0.18/0.54  fof(f323,plain,(
% 0.18/0.54    $false | (~spl7_6 | spl7_10)),
% 0.18/0.54    inference(unit_resulting_resolution,[],[f158,f132,f64])).
% 0.18/0.54  fof(f132,plain,(
% 0.18/0.54    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl7_6),
% 0.18/0.54    inference(avatar_component_clause,[],[f131])).
% 0.18/0.54  fof(f131,plain,(
% 0.18/0.54    spl7_6 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.18/0.54  fof(f158,plain,(
% 0.18/0.54    ~v1_xboole_0(sK2) | spl7_10),
% 0.18/0.54    inference(avatar_component_clause,[],[f156])).
% 0.18/0.54  fof(f156,plain,(
% 0.18/0.54    spl7_10 <=> v1_xboole_0(sK2)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.18/0.54  fof(f320,plain,(
% 0.18/0.54    spl7_6 | ~spl7_23 | ~spl7_19),
% 0.18/0.54    inference(avatar_split_clause,[],[f315,f269,f317,f131])).
% 0.18/0.54  fof(f269,plain,(
% 0.18/0.54    spl7_19 <=> k1_xboole_0 = sK0),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.18/0.54  fof(f315,plain,(
% 0.18/0.54    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | ~r2_hidden(X1,sK2)) ) | ~spl7_19),
% 0.18/0.54    inference(forward_demodulation,[],[f258,f271])).
% 0.18/0.54  fof(f271,plain,(
% 0.18/0.54    k1_xboole_0 = sK0 | ~spl7_19),
% 0.18/0.54    inference(avatar_component_clause,[],[f269])).
% 0.18/0.54  fof(f258,plain,(
% 0.18/0.54    ( ! [X1] : (~r2_hidden(X1,sK2) | ~v1_xboole_0(k2_zfmisc_1(sK0,sK1))) )),
% 0.18/0.54    inference(resolution,[],[f51,f75])).
% 0.18/0.54  fof(f75,plain,(
% 0.18/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | ~v1_xboole_0(X2)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f37])).
% 0.18/0.54  fof(f37,plain,(
% 0.18/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.18/0.54    inference(ennf_transformation,[],[f5])).
% 0.18/0.54  fof(f5,axiom,(
% 0.18/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.18/0.54  fof(f51,plain,(
% 0.18/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f292,plain,(
% 0.18/0.54    spl7_22),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f289])).
% 0.18/0.54  fof(f289,plain,(
% 0.18/0.54    $false | spl7_22),
% 0.18/0.54    inference(unit_resulting_resolution,[],[f83,f283])).
% 0.18/0.54  fof(f283,plain,(
% 0.18/0.54    ~v2_funct_1(k6_partfun1(sK0)) | spl7_22),
% 0.18/0.54    inference(avatar_component_clause,[],[f281])).
% 0.18/0.54  fof(f281,plain,(
% 0.18/0.54    spl7_22 <=> v2_funct_1(k6_partfun1(sK0))),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.18/0.54  fof(f83,plain,(
% 0.18/0.54    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.18/0.54    inference(definition_unfolding,[],[f56,f53])).
% 0.18/0.54  fof(f53,plain,(
% 0.18/0.54    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f17])).
% 0.18/0.54  fof(f17,axiom,(
% 0.18/0.54    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.18/0.54  fof(f56,plain,(
% 0.18/0.54    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f8])).
% 0.18/0.54  fof(f8,axiom,(
% 0.18/0.54    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.18/0.54  fof(f288,plain,(
% 0.18/0.54    spl7_21),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f287])).
% 0.18/0.54  fof(f287,plain,(
% 0.18/0.54    $false | spl7_21),
% 0.18/0.54    inference(subsumption_resolution,[],[f50,f279])).
% 0.18/0.54  fof(f279,plain,(
% 0.18/0.54    ~v1_funct_2(sK2,sK0,sK1) | spl7_21),
% 0.18/0.54    inference(avatar_component_clause,[],[f277])).
% 0.18/0.54  fof(f50,plain,(
% 0.18/0.54    v1_funct_2(sK2,sK0,sK1)),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f286,plain,(
% 0.18/0.54    spl7_20),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f285])).
% 0.18/0.54  fof(f285,plain,(
% 0.18/0.54    $false | spl7_20),
% 0.18/0.54    inference(subsumption_resolution,[],[f46,f275])).
% 0.18/0.54  fof(f275,plain,(
% 0.18/0.54    ~v1_funct_2(sK3,sK1,sK0) | spl7_20),
% 0.18/0.54    inference(avatar_component_clause,[],[f273])).
% 0.18/0.54  fof(f46,plain,(
% 0.18/0.54    v1_funct_2(sK3,sK1,sK0)),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f284,plain,(
% 0.18/0.54    spl7_2 | spl7_19 | ~spl7_14 | ~spl7_15 | ~spl7_20 | ~spl7_16 | ~spl7_17 | ~spl7_21 | ~spl7_22 | ~spl7_13),
% 0.18/0.54    inference(avatar_split_clause,[],[f267,f188,f281,f277,f226,f222,f273,f218,f214,f269,f94])).
% 0.18/0.54  fof(f94,plain,(
% 0.18/0.54    spl7_2 <=> v2_funct_1(sK2)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.18/0.54  fof(f188,plain,(
% 0.18/0.54    spl7_13 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.18/0.54  fof(f267,plain,(
% 0.18/0.54    ~v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~spl7_13),
% 0.18/0.54    inference(superposition,[],[f76,f190])).
% 0.18/0.54  fof(f190,plain,(
% 0.18/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl7_13),
% 0.18/0.54    inference(avatar_component_clause,[],[f188])).
% 0.18/0.54  fof(f76,plain,(
% 0.18/0.54    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X3)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f39])).
% 0.18/0.54  fof(f39,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.18/0.54    inference(flattening,[],[f38])).
% 0.18/0.54  fof(f38,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.18/0.54    inference(ennf_transformation,[],[f19])).
% 0.18/0.54  fof(f19,axiom,(
% 0.18/0.54    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 0.18/0.54  fof(f250,plain,(
% 0.18/0.54    spl7_17),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f249])).
% 0.18/0.54  fof(f249,plain,(
% 0.18/0.54    $false | spl7_17),
% 0.18/0.54    inference(subsumption_resolution,[],[f51,f228])).
% 0.18/0.54  fof(f228,plain,(
% 0.18/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl7_17),
% 0.18/0.54    inference(avatar_component_clause,[],[f226])).
% 0.18/0.54  fof(f247,plain,(
% 0.18/0.54    spl7_16),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f246])).
% 0.18/0.54  % (15150)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.18/0.54  fof(f246,plain,(
% 0.18/0.54    $false | spl7_16),
% 0.18/0.54    inference(subsumption_resolution,[],[f45,f224])).
% 0.18/0.54  fof(f224,plain,(
% 0.18/0.54    ~v1_funct_1(sK3) | spl7_16),
% 0.18/0.54    inference(avatar_component_clause,[],[f222])).
% 0.18/0.54  fof(f45,plain,(
% 0.18/0.54    v1_funct_1(sK3)),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f238,plain,(
% 0.18/0.54    spl7_15),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f237])).
% 0.18/0.54  fof(f237,plain,(
% 0.18/0.54    $false | spl7_15),
% 0.18/0.54    inference(subsumption_resolution,[],[f47,f220])).
% 0.18/0.54  fof(f220,plain,(
% 0.18/0.54    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl7_15),
% 0.18/0.54    inference(avatar_component_clause,[],[f218])).
% 0.18/0.54  fof(f235,plain,(
% 0.18/0.54    spl7_14),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f234])).
% 0.18/0.54  fof(f234,plain,(
% 0.18/0.54    $false | spl7_14),
% 0.18/0.54    inference(subsumption_resolution,[],[f49,f216])).
% 0.18/0.54  fof(f216,plain,(
% 0.18/0.54    ~v1_funct_1(sK2) | spl7_14),
% 0.18/0.54    inference(avatar_component_clause,[],[f214])).
% 0.18/0.54  fof(f49,plain,(
% 0.18/0.54    v1_funct_1(sK2)),
% 0.18/0.54    inference(cnf_transformation,[],[f23])).
% 0.18/0.54  fof(f209,plain,(
% 0.18/0.54    spl7_12),
% 0.18/0.54    inference(avatar_contradiction_clause,[],[f199])).
% 0.18/0.54  fof(f199,plain,(
% 0.18/0.54    $false | spl7_12),
% 0.18/0.54    inference(unit_resulting_resolution,[],[f49,f45,f47,f51,f186,f81])).
% 0.18/0.54  fof(f81,plain,(
% 0.18/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f43])).
% 0.18/0.54  fof(f43,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.18/0.54    inference(flattening,[],[f42])).
% 0.18/0.54  fof(f42,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.18/0.54    inference(ennf_transformation,[],[f16])).
% 0.18/0.54  fof(f16,axiom,(
% 0.18/0.54    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.18/0.54  fof(f186,plain,(
% 0.18/0.54    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_12),
% 0.18/0.54    inference(avatar_component_clause,[],[f184])).
% 0.18/0.54  fof(f184,plain,(
% 0.18/0.54    spl7_12 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.18/0.54  fof(f191,plain,(
% 0.18/0.54    ~spl7_12 | spl7_13),
% 0.18/0.54    inference(avatar_split_clause,[],[f181,f188,f184])).
% 0.18/0.54  fof(f181,plain,(
% 0.18/0.54    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.18/0.54    inference(resolution,[],[f178,f48])).
% 0.18/0.54  fof(f178,plain,(
% 0.18/0.54    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 0.18/0.54    inference(resolution,[],[f79,f82])).
% 0.18/0.54  fof(f82,plain,(
% 0.18/0.54    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.54    inference(definition_unfolding,[],[f54,f53])).
% 0.18/0.54  fof(f54,plain,(
% 0.18/0.54    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.18/0.54    inference(cnf_transformation,[],[f14])).
% 0.18/0.54  fof(f14,axiom,(
% 0.18/0.54    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.18/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 0.18/0.54  fof(f79,plain,(
% 0.18/0.54    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 0.18/0.54    inference(cnf_transformation,[],[f41])).
% 0.18/0.54  fof(f41,plain,(
% 0.18/0.54    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.18/0.54    inference(flattening,[],[f40])).
% 0.18/0.55  % (15170)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.18/0.55  fof(f40,plain,(
% 0.18/0.55    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.18/0.55    inference(ennf_transformation,[],[f13])).
% 0.18/0.55  fof(f13,axiom,(
% 0.18/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.18/0.55  fof(f167,plain,(
% 0.18/0.55    spl7_11),
% 0.18/0.55    inference(avatar_contradiction_clause,[],[f164])).
% 0.18/0.55  fof(f164,plain,(
% 0.18/0.55    $false | spl7_11),
% 0.18/0.55    inference(subsumption_resolution,[],[f107,f162])).
% 0.18/0.55  fof(f162,plain,(
% 0.18/0.55    ~v1_relat_1(sK2) | spl7_11),
% 0.18/0.55    inference(avatar_component_clause,[],[f160])).
% 0.18/0.55  fof(f160,plain,(
% 0.18/0.55    spl7_11 <=> v1_relat_1(sK2)),
% 0.18/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.18/0.55  fof(f107,plain,(
% 0.18/0.55    v1_relat_1(sK2)),
% 0.18/0.55    inference(resolution,[],[f70,f51])).
% 0.18/0.55  fof(f163,plain,(
% 0.18/0.55    ~spl7_10 | ~spl7_11 | spl7_2),
% 0.18/0.55    inference(avatar_split_clause,[],[f141,f94,f160,f156])).
% 0.18/0.55  fof(f141,plain,(
% 0.18/0.55    v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_xboole_0(sK2)),
% 0.18/0.55    inference(resolution,[],[f139,f49])).
% 0.18/0.55  fof(f139,plain,(
% 0.18/0.55    ( ! [X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.55    inference(resolution,[],[f138,f58])).
% 0.18/0.55  fof(f58,plain,(
% 0.18/0.55    ( ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f25])).
% 0.18/0.55  fof(f25,plain,(
% 0.18/0.55    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 0.18/0.55    inference(ennf_transformation,[],[f6])).
% 0.18/0.55  fof(f6,axiom,(
% 0.18/0.55    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).
% 0.18/0.55  fof(f138,plain,(
% 0.18/0.55    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v2_funct_1(X0) | ~v1_funct_1(X0)) )),
% 0.18/0.55    inference(resolution,[],[f60,f65])).
% 0.18/0.55  fof(f65,plain,(
% 0.18/0.55    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f1])).
% 0.18/0.55  fof(f60,plain,(
% 0.18/0.55    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.18/0.55    inference(cnf_transformation,[],[f27])).
% 0.18/0.55  fof(f27,plain,(
% 0.18/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.18/0.55    inference(flattening,[],[f26])).
% 0.18/0.55  fof(f26,plain,(
% 0.18/0.55    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.18/0.55    inference(ennf_transformation,[],[f7])).
% 0.18/0.55  fof(f7,axiom,(
% 0.18/0.55    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.18/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_funct_1)).
% 0.18/0.55  fof(f97,plain,(
% 0.18/0.55    ~spl7_1 | ~spl7_2),
% 0.18/0.55    inference(avatar_split_clause,[],[f44,f94,f90])).
% 0.18/0.55  fof(f44,plain,(
% 0.18/0.55    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 0.18/0.55    inference(cnf_transformation,[],[f23])).
% 0.18/0.55  % SZS output end Proof for theBenchmark
% 0.18/0.55  % (15161)------------------------------
% 0.18/0.55  % (15161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.55  % (15161)Termination reason: Refutation
% 0.18/0.55  
% 0.18/0.55  % (15161)Memory used [KB]: 6524
% 0.18/0.55  % (15161)Time elapsed: 0.145 s
% 0.18/0.55  % (15161)------------------------------
% 0.18/0.55  % (15161)------------------------------
% 0.18/0.55  % (15162)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.18/0.55  % (15147)Success in time 0.209 s
%------------------------------------------------------------------------------
