%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:05:30 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 332 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   11
%              Number of atoms          :  344 (1432 expanded)
%              Number of equality atoms :   60 ( 303 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f509,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f66,f71,f84,f101,f134,f142,f278,f349,f439,f508])).

fof(f508,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(avatar_contradiction_clause,[],[f504])).

fof(f504,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f70,f497])).

fof(f497,plain,
    ( sK2 = sK3
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(backward_demodulation,[],[f496,f490])).

fof(f490,plain,
    ( sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_2
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f27,f54,f59,f336,f28,f332,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X3)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X1
      | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).

fof(f332,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl7_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f28,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f336,plain,
    ( k1_xboole_0 != sK0
    | spl7_15 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl7_15
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f59,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f54,plain,
    ( v2_funct_1(sK1)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl7_1
  <=> v2_funct_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f27,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f496,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_14
    | spl7_15 ),
    inference(forward_demodulation,[],[f491,f83])).

fof(f83,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl7_5
  <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f491,plain,
    ( sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3))
    | ~ spl7_1
    | ~ spl7_3
    | ~ spl7_14
    | spl7_15 ),
    inference(unit_resulting_resolution,[],[f27,f54,f65,f336,f28,f332,f43])).

fof(f65,plain,
    ( r2_hidden(sK3,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl7_3
  <=> r2_hidden(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f70,plain,
    ( sK2 != sK3
    | spl7_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl7_4
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f439,plain,
    ( ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_contradiction_clause,[],[f438])).

fof(f438,plain,
    ( $false
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(trivial_inequality_removal,[],[f437])).

fof(f437,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK2)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(forward_demodulation,[],[f415,f421])).

fof(f421,plain,
    ( sK2 = sK3
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f387,f83,f390,f129])).

fof(f129,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | X3 = X4
        | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK1)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl7_9
  <=> ! [X3,X4] :
        ( ~ r2_hidden(X3,k1_relat_1(sK1))
        | X3 = X4
        | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
        | ~ r2_hidden(X4,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f390,plain,
    ( ! [X0] : r2_hidden(sK3,X0)
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f44,f353,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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

fof(f353,plain,
    ( r2_hidden(sK3,k1_xboole_0)
    | ~ spl7_3
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f65,f337])).

fof(f337,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f335])).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f387,plain,
    ( ! [X0] : r2_hidden(sK2,X0)
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f44,f352,f38])).

fof(f352,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl7_2
    | ~ spl7_15 ),
    inference(backward_demodulation,[],[f59,f337])).

fof(f415,plain,
    ( k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | spl7_4
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(unit_resulting_resolution,[],[f70,f387,f390,f129])).

fof(f349,plain,(
    spl7_14 ),
    inference(avatar_contradiction_clause,[],[f344])).

% (27189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f344,plain,
    ( $false
    | spl7_14 ),
    inference(unit_resulting_resolution,[],[f75,f333,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f333,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f331])).

fof(f75,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f278,plain,
    ( spl7_1
    | ~ spl7_6 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl7_1
    | ~ spl7_6 ),
    inference(unit_resulting_resolution,[],[f202,f208,f197,f196,f100])).

fof(f100,plain,
    ( ! [X2,X3] :
        ( k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
        | X2 = X3
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X3,sK0) )
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
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
    inference(unit_resulting_resolution,[],[f73,f27,f55,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f55,plain,
    ( ~ v2_funct_1(sK1)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f73,plain,(
    v1_relat_1(sK1) ),
    inference(unit_resulting_resolution,[],[f29,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f197,plain,
    ( sK4(sK1) != sK5(sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f27,f73,f55,f37])).

fof(f37,plain,(
    ! [X0] :
      ( sK4(X0) != sK5(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f208,plain,
    ( r2_hidden(sK5(sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f91,f195,f38])).

fof(f195,plain,
    ( r2_hidden(sK5(sK1),k1_relat_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f27,f73,f55,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f78,f42])).

fof(f78,plain,(
    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0)) ),
    inference(forward_demodulation,[],[f72,f74])).

fof(f74,plain,(
    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f45])).

fof(f45,plain,(
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

fof(f72,plain,(
    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(unit_resulting_resolution,[],[f29,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f202,plain,
    ( r2_hidden(sK4(sK1),sK0)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f91,f194,f38])).

fof(f194,plain,
    ( r2_hidden(sK4(sK1),k1_relat_1(sK1))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f27,f73,f55,f34])).

fof(f34,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f142,plain,(
    spl7_10 ),
    inference(avatar_contradiction_clause,[],[f137])).

fof(f137,plain,
    ( $false
    | spl7_10 ),
    inference(unit_resulting_resolution,[],[f29,f133,f46])).

fof(f133,plain,
    ( ~ v1_relat_1(sK1)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl7_10
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f134,plain,
    ( ~ spl7_1
    | spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f51,f131,f128,f53])).

fof(f51,plain,(
    ! [X4,X3] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(X3,k1_relat_1(sK1))
      | ~ r2_hidden(X4,k1_relat_1(sK1))
      | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4)
      | X3 = X4
      | ~ v2_funct_1(sK1) ) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ r2_hidden(X2,k1_relat_1(X0))
      | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
      | X1 = X2
      | ~ v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( spl7_1
    | spl7_6 ),
    inference(avatar_split_clause,[],[f26,f99,f53])).

fof(f26,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,sK0)
      | ~ r2_hidden(X3,sK0)
      | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3)
      | X2 = X3
      | v2_funct_1(sK1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( ~ spl7_1
    | spl7_5 ),
    inference(avatar_split_clause,[],[f24,f81,f53])).

fof(f24,plain,
    ( k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f71,plain,
    ( ~ spl7_1
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f25,f68,f53])).

fof(f25,plain,
    ( sK2 != sK3
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f66,plain,
    ( ~ spl7_1
    | spl7_3 ),
    inference(avatar_split_clause,[],[f23,f63,f53])).

fof(f23,plain,
    ( r2_hidden(sK3,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f60,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f22,f57,f53])).

fof(f22,plain,
    ( r2_hidden(sK2,sK0)
    | ~ v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:06:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.51/0.56  % (27166)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.51/0.58  % (27173)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.51/0.58  % (27182)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.51/0.58  % (27186)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.58  % (27179)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.51/0.59  % (27184)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.51/0.59  % (27174)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.59  % (27190)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.51/0.59  % (27169)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.51/0.59  % (27179)Refutation not found, incomplete strategy% (27179)------------------------------
% 1.51/0.59  % (27179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.59  % (27179)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.59  
% 1.51/0.59  % (27179)Memory used [KB]: 10618
% 1.51/0.59  % (27179)Time elapsed: 0.092 s
% 1.51/0.59  % (27179)------------------------------
% 1.51/0.59  % (27179)------------------------------
% 1.51/0.60  % (27165)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.51/0.60  % (27167)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.51/0.60  % (27164)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.51/0.60  % (27163)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.51/0.60  % (27191)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.51/0.60  % (27168)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.51/0.61  % (27172)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.51/0.61  % (27162)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.51/0.61  % (27172)Refutation not found, incomplete strategy% (27172)------------------------------
% 1.51/0.61  % (27172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.61  % (27172)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.61  
% 1.51/0.61  % (27172)Memory used [KB]: 10618
% 1.51/0.61  % (27172)Time elapsed: 0.165 s
% 1.51/0.61  % (27172)------------------------------
% 1.51/0.61  % (27172)------------------------------
% 1.51/0.61  % (27166)Refutation found. Thanks to Tanya!
% 1.51/0.61  % SZS status Theorem for theBenchmark
% 1.51/0.61  % SZS output start Proof for theBenchmark
% 1.51/0.61  fof(f509,plain,(
% 1.51/0.61    $false),
% 1.51/0.61    inference(avatar_sat_refutation,[],[f60,f66,f71,f84,f101,f134,f142,f278,f349,f439,f508])).
% 1.51/0.61  fof(f508,plain,(
% 1.51/0.61    ~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_14 | spl7_15),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f504])).
% 1.51/0.61  fof(f504,plain,(
% 1.51/0.61    $false | (~spl7_1 | ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f70,f497])).
% 1.51/0.61  fof(f497,plain,(
% 1.51/0.61    sK2 = sK3 | (~spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 1.51/0.61    inference(backward_demodulation,[],[f496,f490])).
% 1.51/0.61  fof(f490,plain,(
% 1.51/0.61    sK2 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_2 | ~spl7_14 | spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f27,f54,f59,f336,f28,f332,f43])).
% 1.51/0.61  fof(f43,plain,(
% 1.51/0.61    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X3) | ~r2_hidden(X2,X0) | k1_xboole_0 = X1 | k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2) )),
% 1.51/0.61    inference(cnf_transformation,[],[f18])).
% 1.51/0.61  fof(f18,plain,(
% 1.51/0.61    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.51/0.61    inference(flattening,[],[f17])).
% 1.51/0.61  fof(f17,plain,(
% 1.51/0.61    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.51/0.61    inference(ennf_transformation,[],[f9])).
% 1.51/0.61  fof(f9,axiom,(
% 1.51/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_funct_2)).
% 1.51/0.61  fof(f332,plain,(
% 1.51/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl7_14),
% 1.51/0.61    inference(avatar_component_clause,[],[f331])).
% 1.51/0.61  fof(f331,plain,(
% 1.51/0.61    spl7_14 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 1.51/0.61  fof(f28,plain,(
% 1.51/0.61    v1_funct_2(sK1,sK0,sK0)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f13,plain,(
% 1.51/0.61    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 1.51/0.61    inference(flattening,[],[f12])).
% 1.51/0.61  fof(f12,plain,(
% 1.51/0.61    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 1.51/0.61    inference(ennf_transformation,[],[f11])).
% 1.51/0.61  fof(f11,negated_conjecture,(
% 1.51/0.61    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.51/0.61    inference(negated_conjecture,[],[f10])).
% 1.51/0.61  fof(f10,conjecture,(
% 1.51/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_funct_2)).
% 1.51/0.61  fof(f336,plain,(
% 1.51/0.61    k1_xboole_0 != sK0 | spl7_15),
% 1.51/0.61    inference(avatar_component_clause,[],[f335])).
% 1.51/0.61  fof(f335,plain,(
% 1.51/0.61    spl7_15 <=> k1_xboole_0 = sK0),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.51/0.61  fof(f59,plain,(
% 1.51/0.61    r2_hidden(sK2,sK0) | ~spl7_2),
% 1.51/0.61    inference(avatar_component_clause,[],[f57])).
% 1.51/0.61  fof(f57,plain,(
% 1.51/0.61    spl7_2 <=> r2_hidden(sK2,sK0)),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.51/0.61  fof(f54,plain,(
% 1.51/0.61    v2_funct_1(sK1) | ~spl7_1),
% 1.51/0.61    inference(avatar_component_clause,[],[f53])).
% 1.51/0.61  fof(f53,plain,(
% 1.51/0.61    spl7_1 <=> v2_funct_1(sK1)),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.51/0.61  fof(f27,plain,(
% 1.51/0.61    v1_funct_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f496,plain,(
% 1.51/0.61    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK2)) | (~spl7_1 | ~spl7_3 | ~spl7_5 | ~spl7_14 | spl7_15)),
% 1.51/0.61    inference(forward_demodulation,[],[f491,f83])).
% 1.51/0.61  fof(f83,plain,(
% 1.51/0.61    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~spl7_5),
% 1.51/0.61    inference(avatar_component_clause,[],[f81])).
% 1.51/0.61  fof(f81,plain,(
% 1.51/0.61    spl7_5 <=> k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3)),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.51/0.61  fof(f491,plain,(
% 1.51/0.61    sK3 = k1_funct_1(k2_funct_1(sK1),k1_funct_1(sK1,sK3)) | (~spl7_1 | ~spl7_3 | ~spl7_14 | spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f27,f54,f65,f336,f28,f332,f43])).
% 1.51/0.61  fof(f65,plain,(
% 1.51/0.61    r2_hidden(sK3,sK0) | ~spl7_3),
% 1.51/0.61    inference(avatar_component_clause,[],[f63])).
% 1.51/0.61  fof(f63,plain,(
% 1.51/0.61    spl7_3 <=> r2_hidden(sK3,sK0)),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.51/0.61  fof(f70,plain,(
% 1.51/0.61    sK2 != sK3 | spl7_4),
% 1.51/0.61    inference(avatar_component_clause,[],[f68])).
% 1.51/0.61  fof(f68,plain,(
% 1.51/0.61    spl7_4 <=> sK2 = sK3),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.51/0.61  fof(f439,plain,(
% 1.51/0.61    ~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_15),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f438])).
% 1.51/0.61  fof(f438,plain,(
% 1.51/0.61    $false | (~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_15)),
% 1.51/0.61    inference(trivial_inequality_removal,[],[f437])).
% 1.51/0.61  fof(f437,plain,(
% 1.51/0.61    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK2) | (~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_15)),
% 1.51/0.61    inference(forward_demodulation,[],[f415,f421])).
% 1.51/0.61  fof(f421,plain,(
% 1.51/0.61    sK2 = sK3 | (~spl7_2 | ~spl7_3 | ~spl7_5 | ~spl7_9 | ~spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f387,f83,f390,f129])).
% 1.51/0.61  fof(f129,plain,(
% 1.51/0.61    ( ! [X4,X3] : (~r2_hidden(X3,k1_relat_1(sK1)) | X3 = X4 | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relat_1(sK1))) ) | ~spl7_9),
% 1.51/0.61    inference(avatar_component_clause,[],[f128])).
% 1.51/0.61  fof(f128,plain,(
% 1.51/0.61    spl7_9 <=> ! [X3,X4] : (~r2_hidden(X3,k1_relat_1(sK1)) | X3 = X4 | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | ~r2_hidden(X4,k1_relat_1(sK1)))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.51/0.61  fof(f390,plain,(
% 1.51/0.61    ( ! [X0] : (r2_hidden(sK3,X0)) ) | (~spl7_3 | ~spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f44,f353,f38])).
% 1.51/0.61  fof(f38,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f16])).
% 1.51/0.61  fof(f16,plain,(
% 1.51/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f1])).
% 1.51/0.61  fof(f1,axiom,(
% 1.51/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.51/0.61  fof(f353,plain,(
% 1.51/0.61    r2_hidden(sK3,k1_xboole_0) | (~spl7_3 | ~spl7_15)),
% 1.51/0.61    inference(backward_demodulation,[],[f65,f337])).
% 1.51/0.61  fof(f337,plain,(
% 1.51/0.61    k1_xboole_0 = sK0 | ~spl7_15),
% 1.51/0.61    inference(avatar_component_clause,[],[f335])).
% 1.51/0.61  fof(f44,plain,(
% 1.51/0.61    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f3])).
% 1.51/0.61  fof(f3,axiom,(
% 1.51/0.61    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.51/0.61  fof(f387,plain,(
% 1.51/0.61    ( ! [X0] : (r2_hidden(sK2,X0)) ) | (~spl7_2 | ~spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f44,f352,f38])).
% 1.51/0.61  fof(f352,plain,(
% 1.51/0.61    r2_hidden(sK2,k1_xboole_0) | (~spl7_2 | ~spl7_15)),
% 1.51/0.61    inference(backward_demodulation,[],[f59,f337])).
% 1.51/0.61  fof(f415,plain,(
% 1.51/0.61    k1_funct_1(sK1,sK2) != k1_funct_1(sK1,sK3) | (~spl7_2 | ~spl7_3 | spl7_4 | ~spl7_9 | ~spl7_15)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f70,f387,f390,f129])).
% 1.51/0.61  fof(f349,plain,(
% 1.51/0.61    spl7_14),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f344])).
% 1.51/0.61  % (27189)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.51/0.61  fof(f344,plain,(
% 1.51/0.61    $false | spl7_14),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f75,f333,f41])).
% 1.51/0.61  fof(f41,plain,(
% 1.51/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f4])).
% 1.51/0.61  fof(f4,axiom,(
% 1.51/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.51/0.61  fof(f333,plain,(
% 1.51/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl7_14),
% 1.51/0.61    inference(avatar_component_clause,[],[f331])).
% 1.51/0.61  fof(f75,plain,(
% 1.51/0.61    r1_tarski(sK1,k2_zfmisc_1(sK0,sK0))),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f29,f42])).
% 1.51/0.61  fof(f42,plain,(
% 1.51/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f4])).
% 1.51/0.61  fof(f29,plain,(
% 1.51/0.61    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f278,plain,(
% 1.51/0.61    spl7_1 | ~spl7_6),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f268])).
% 1.51/0.61  fof(f268,plain,(
% 1.51/0.61    $false | (spl7_1 | ~spl7_6)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f202,f208,f197,f196,f100])).
% 1.51/0.61  fof(f100,plain,(
% 1.51/0.61    ( ! [X2,X3] : (k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | ~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0)) ) | ~spl7_6),
% 1.51/0.61    inference(avatar_component_clause,[],[f99])).
% 1.51/0.61  fof(f99,plain,(
% 1.51/0.61    spl7_6 <=> ! [X3,X2] : (~r2_hidden(X2,sK0) | X2 = X3 | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | ~r2_hidden(X3,sK0))),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.51/0.61  fof(f196,plain,(
% 1.51/0.61    k1_funct_1(sK1,sK4(sK1)) = k1_funct_1(sK1,sK5(sK1)) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f73,f27,f55,f36])).
% 1.51/0.61  fof(f36,plain,(
% 1.51/0.61    ( ! [X0] : (v2_funct_1(X0) | ~v1_funct_1(X0) | k1_funct_1(X0,sK4(X0)) = k1_funct_1(X0,sK5(X0)) | ~v1_relat_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f15,plain,(
% 1.51/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.61    inference(flattening,[],[f14])).
% 1.51/0.61  fof(f14,plain,(
% 1.51/0.61    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.61    inference(ennf_transformation,[],[f5])).
% 1.51/0.61  fof(f5,axiom,(
% 1.51/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_funct_1)).
% 1.51/0.61  fof(f55,plain,(
% 1.51/0.61    ~v2_funct_1(sK1) | spl7_1),
% 1.51/0.61    inference(avatar_component_clause,[],[f53])).
% 1.51/0.61  fof(f73,plain,(
% 1.51/0.61    v1_relat_1(sK1)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f29,f46])).
% 1.51/0.61  fof(f46,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.61    inference(cnf_transformation,[],[f20])).
% 1.51/0.61  fof(f20,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.61    inference(ennf_transformation,[],[f6])).
% 1.51/0.61  fof(f6,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.51/0.61  fof(f197,plain,(
% 1.51/0.61    sK4(sK1) != sK5(sK1) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f27,f73,f55,f37])).
% 1.51/0.61  fof(f37,plain,(
% 1.51/0.61    ( ! [X0] : (sK4(X0) != sK5(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f208,plain,(
% 1.51/0.61    r2_hidden(sK5(sK1),sK0) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f91,f195,f38])).
% 1.51/0.61  fof(f195,plain,(
% 1.51/0.61    r2_hidden(sK5(sK1),k1_relat_1(sK1)) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f27,f73,f55,f35])).
% 1.51/0.61  fof(f35,plain,(
% 1.51/0.61    ( ! [X0] : (r2_hidden(sK5(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f91,plain,(
% 1.51/0.61    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f78,f42])).
% 1.51/0.61  fof(f78,plain,(
% 1.51/0.61    m1_subset_1(k1_relat_1(sK1),k1_zfmisc_1(sK0))),
% 1.51/0.61    inference(forward_demodulation,[],[f72,f74])).
% 1.51/0.61  fof(f74,plain,(
% 1.51/0.61    k1_relat_1(sK1) = k1_relset_1(sK0,sK0,sK1)),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f29,f45])).
% 1.51/0.61  fof(f45,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.61    inference(cnf_transformation,[],[f19])).
% 1.51/0.61  fof(f19,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.61    inference(ennf_transformation,[],[f8])).
% 1.51/0.61  fof(f8,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.61  fof(f72,plain,(
% 1.51/0.61    m1_subset_1(k1_relset_1(sK0,sK0,sK1),k1_zfmisc_1(sK0))),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f29,f47])).
% 1.51/0.61  fof(f47,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 1.51/0.61    inference(cnf_transformation,[],[f21])).
% 1.51/0.61  fof(f21,plain,(
% 1.51/0.61    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.61    inference(ennf_transformation,[],[f7])).
% 1.51/0.61  fof(f7,axiom,(
% 1.51/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.51/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 1.51/0.61  fof(f202,plain,(
% 1.51/0.61    r2_hidden(sK4(sK1),sK0) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f91,f194,f38])).
% 1.51/0.61  fof(f194,plain,(
% 1.51/0.61    r2_hidden(sK4(sK1),k1_relat_1(sK1)) | spl7_1),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f27,f73,f55,f34])).
% 1.51/0.61  fof(f34,plain,(
% 1.51/0.61    ( ! [X0] : (r2_hidden(sK4(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f142,plain,(
% 1.51/0.61    spl7_10),
% 1.51/0.61    inference(avatar_contradiction_clause,[],[f137])).
% 1.51/0.61  fof(f137,plain,(
% 1.51/0.61    $false | spl7_10),
% 1.51/0.61    inference(unit_resulting_resolution,[],[f29,f133,f46])).
% 1.51/0.61  fof(f133,plain,(
% 1.51/0.61    ~v1_relat_1(sK1) | spl7_10),
% 1.51/0.61    inference(avatar_component_clause,[],[f131])).
% 1.51/0.61  fof(f131,plain,(
% 1.51/0.61    spl7_10 <=> v1_relat_1(sK1)),
% 1.51/0.61    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.51/0.61  fof(f134,plain,(
% 1.51/0.61    ~spl7_1 | spl7_9 | ~spl7_10),
% 1.51/0.61    inference(avatar_split_clause,[],[f51,f131,f128,f53])).
% 1.51/0.61  fof(f51,plain,(
% 1.51/0.61    ( ! [X4,X3] : (~v1_relat_1(sK1) | ~r2_hidden(X3,k1_relat_1(sK1)) | ~r2_hidden(X4,k1_relat_1(sK1)) | k1_funct_1(sK1,X3) != k1_funct_1(sK1,X4) | X3 = X4 | ~v2_funct_1(sK1)) )),
% 1.51/0.61    inference(resolution,[],[f27,f33])).
% 1.51/0.61  fof(f33,plain,(
% 1.51/0.61    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | ~r2_hidden(X2,k1_relat_1(X0)) | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | X1 = X2 | ~v2_funct_1(X0)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f15])).
% 1.51/0.61  fof(f101,plain,(
% 1.51/0.61    spl7_1 | spl7_6),
% 1.51/0.61    inference(avatar_split_clause,[],[f26,f99,f53])).
% 1.51/0.61  fof(f26,plain,(
% 1.51/0.61    ( ! [X2,X3] : (~r2_hidden(X2,sK0) | ~r2_hidden(X3,sK0) | k1_funct_1(sK1,X2) != k1_funct_1(sK1,X3) | X2 = X3 | v2_funct_1(sK1)) )),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f84,plain,(
% 1.51/0.61    ~spl7_1 | spl7_5),
% 1.51/0.61    inference(avatar_split_clause,[],[f24,f81,f53])).
% 1.51/0.61  fof(f24,plain,(
% 1.51/0.61    k1_funct_1(sK1,sK2) = k1_funct_1(sK1,sK3) | ~v2_funct_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f71,plain,(
% 1.51/0.61    ~spl7_1 | ~spl7_4),
% 1.51/0.61    inference(avatar_split_clause,[],[f25,f68,f53])).
% 1.51/0.61  fof(f25,plain,(
% 1.51/0.61    sK2 != sK3 | ~v2_funct_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f66,plain,(
% 1.51/0.61    ~spl7_1 | spl7_3),
% 1.51/0.61    inference(avatar_split_clause,[],[f23,f63,f53])).
% 1.51/0.61  fof(f23,plain,(
% 1.51/0.61    r2_hidden(sK3,sK0) | ~v2_funct_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  fof(f60,plain,(
% 1.51/0.61    ~spl7_1 | spl7_2),
% 1.51/0.61    inference(avatar_split_clause,[],[f22,f57,f53])).
% 1.51/0.61  fof(f22,plain,(
% 1.51/0.61    r2_hidden(sK2,sK0) | ~v2_funct_1(sK1)),
% 1.51/0.61    inference(cnf_transformation,[],[f13])).
% 1.51/0.61  % SZS output end Proof for theBenchmark
% 1.51/0.61  % (27166)------------------------------
% 1.51/0.61  % (27166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.61  % (27166)Termination reason: Refutation
% 1.51/0.61  
% 1.51/0.61  % (27166)Memory used [KB]: 6396
% 1.51/0.61  % (27166)Time elapsed: 0.180 s
% 1.51/0.61  % (27166)------------------------------
% 1.51/0.61  % (27166)------------------------------
% 1.51/0.61  % (27161)Success in time 0.238 s
%------------------------------------------------------------------------------
