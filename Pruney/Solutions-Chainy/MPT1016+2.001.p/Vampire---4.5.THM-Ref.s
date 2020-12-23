%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 268 expanded)
%              Number of leaves         :   19 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  297 (1200 expanded)
%              Number of equality atoms :   47 ( 248 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f442,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f71,f76,f87,f105,f280,f337,f385,f441])).

fof(f441,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f437])).

fof(f437,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f75,f434])).

fof(f434,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(backward_demodulation,[],[f433,f426])).

fof(f426,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f29,f59,f64,f324,f30,f320,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f320,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl7_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f30,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).

fof(f324,plain,
    ( k1_xboole_0 != sK0
    | spl7_15 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f64,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f59,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f29,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f433,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(forward_demodulation,[],[f427,f86])).

fof(f86,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_5
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f427,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f29,f59,f70,f324,f30,f320,f46])).

fof(f70,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f75,plain,
    ( sK2 != sK3
    | spl7_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl7_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f385,plain,
    ( ~ spl7_2
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f54,f348])).

fof(f348,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f112,f325])).

fof(f325,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f323])).

fof(f112,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f106,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f49,f64,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f54,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f337,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f332])).

fof(f332,plain,
    ( $false
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f80,f321,f44])).

fof(f321,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f319])).

fof(f80,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f280,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | spl7_1
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f211,f197,f196,f104])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_6
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,sK0)
        | X2 = X3
        | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | ~ r2_hidden(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f196,plain,
    ( k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f79,f29,f60,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).

fof(f60,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f79,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f31,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f197,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f29,f79,f60,f39])).

fof(f39,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f211,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f95,f195,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f195,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f29,f79,f60,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f79,f77,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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

fof(f77,plain,(
    v4_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f31,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f202,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f95,f194,f40])).

fof(f194,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f29,f79,f60,f36])).

fof(f36,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f28,f103,f58])).

fof(f28,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f87,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f26,f84,f58])).

fof(f26,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f27,f73,f58])).

fof(f27,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f25,f68,f58])).

fof(f25,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f65,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f24,f62,f58])).

fof(f24,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.50  % (8821)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (8847)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (8839)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.51  % (8840)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (8823)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (8830)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (8832)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (8828)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (8818)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.52  % (8821)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f442,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f65,f71,f76,f87,f105,f280,f337,f385,f441])).
% 0.20/0.52  fof(f441,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_14 | spl7_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f437])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f75,f434])).
% 0.20/0.52  fof(f434,plain,(
% 0.20/0.52    sK2 = sK3 | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f433,f426])).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_14 | spl7_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f29,f59,f64,f324,f30,f320,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 0.20/0.52  fof(f320,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f319])).
% 0.20/0.52  fof(f319,plain,(
% 0.20/0.52    spl7_14 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    v1_funct_2(sK1,sK0,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 0.20/0.52  fof(f324,plain,(
% 0.20/0.52    k1_xboole_0 != sK0 | spl7_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f323])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    spl7_15 <=> k1_xboole_0 = sK0),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0) | ~spl7_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    spl7_2 <=> r2_hidden(sK2,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    v2_funct_1(sK1) | ~spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    spl7_1 <=> v2_funct_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v1_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f433,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 0.20/0.52    inference(forward_demodulation,[],[f427,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    spl7_5 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.52  fof(f427,plain,(
% 0.20/0.52    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_1 | ~spl7_3 | ~spl7_14 | spl7_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f29,f59,f70,f324,f30,f320,f46])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    r2_hidden(sK3,sK0) | ~spl7_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    spl7_3 <=> r2_hidden(sK3,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    sK2 != sK3 | spl7_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    spl7_4 <=> sK2 = sK3),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.52  fof(f385,plain,(
% 0.20/0.52    ~spl7_2 | ~spl7_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f377])).
% 0.20/0.52  fof(f377,plain,(
% 0.20/0.52    $false | (~spl7_2 | ~spl7_15)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f54,f348])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl7_2 | ~spl7_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f112,f325])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    k1_xboole_0 = sK0 | ~spl7_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f323])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    ~r1_tarski(sK0,k1_xboole_0) | ~spl7_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f106,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(k1_xboole_0)) | ~spl7_2),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f49,f64,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f337,plain,(
% 0.20/0.52    spl7_14),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f332])).
% 0.20/0.52  fof(f332,plain,(
% 0.20/0.52    $false | spl7_14),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f80,f321,f44])).
% 0.20/0.52  fof(f321,plain,(
% 0.20/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f319])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    spl7_1 | ~spl7_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f270])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    $false | (spl7_1 | ~spl7_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f202,f211,f197,f196,f104])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0)) ) | ~spl7_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f103])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl7_6 <=> ! [X3,X2] : (~r2_hidden(X2,sK0) | X2 = X3 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f79,f29,f60,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(flattening,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~v2_funct_1(sK1) | spl7_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f58])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    sK4(sK1) != sK5(sK1) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f29,f79,f60,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0] : (sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f211,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),sK0) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f95,f195,f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f29,f79,f60,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    r1_tarski(k1_relat_1(sK1),sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f79,f77,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    v4_relat_1(sK1,sK0)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f31,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.52  fof(f202,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),sK0) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f95,f194,f40])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | spl7_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f29,f79,f60,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl7_1 | spl7_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f28,f103,f58])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ~spl7_1 | spl7_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f26,f84,f58])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ~spl7_1 | ~spl7_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f73,f58])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    sK2 != sK3 | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ~spl7_1 | spl7_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f25,f68,f58])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    ~spl7_1 | spl7_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f24,f62,f58])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (8821)------------------------------
% 0.20/0.52  % (8821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8821)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (8821)Memory used [KB]: 6396
% 0.20/0.52  % (8821)Time elapsed: 0.116 s
% 0.20/0.52  % (8821)------------------------------
% 0.20/0.52  % (8821)------------------------------
% 0.20/0.52  % (8831)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (8828)Refutation not found, incomplete strategy% (8828)------------------------------
% 0.20/0.52  % (8828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (8828)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (8828)Memory used [KB]: 10618
% 0.20/0.52  % (8828)Time elapsed: 0.064 s
% 0.20/0.52  % (8828)------------------------------
% 0.20/0.52  % (8828)------------------------------
% 0.20/0.53  % (8822)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (8817)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (8820)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (8844)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (8824)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (8835)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (8836)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (8843)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (8809)Success in time 0.19 s
%------------------------------------------------------------------------------
