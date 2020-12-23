%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:38 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.48s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 383 expanded)
%              Number of leaves         :   52 ( 157 expanded)
%              Depth                    :   13
%              Number of atoms          :  565 (1091 expanded)
%              Number of equality atoms :  133 ( 260 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (27825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f977,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f104,f118,f128,f133,f141,f153,f208,f248,f254,f278,f311,f366,f413,f448,f518,f670,f677,f688,f721,f722,f724,f739,f756,f766,f794,f818,f828,f850,f976])).

fof(f976,plain,
    ( ~ spl7_18
    | ~ spl7_28
    | ~ spl7_31
    | spl7_61 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_31
    | spl7_61 ),
    inference(trivial_inequality_removal,[],[f974])).

fof(f974,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_31
    | spl7_61 ),
    inference(superposition,[],[f630,f973])).

fof(f973,plain,
    ( ! [X4] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)
    | ~ spl7_18
    | ~ spl7_28
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f972,f277])).

fof(f277,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f275])).

fof(f275,plain,
    ( spl7_28
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f972,plain,
    ( ! [X4] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X4)
    | ~ spl7_18
    | ~ spl7_31 ),
    inference(forward_demodulation,[],[f282,f310])).

fof(f310,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f309])).

fof(f309,plain,
    ( spl7_31
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f282,plain,
    ( ! [X4] : k2_relat_1(k7_relat_1(k1_xboole_0,X4)) = k9_relat_1(k1_xboole_0,X4)
    | ~ spl7_18 ),
    inference(resolution,[],[f56,f206])).

fof(f206,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f204])).

% (27815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f204,plain,
    ( spl7_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f630,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3)
    | spl7_61 ),
    inference(avatar_component_clause,[],[f628])).

fof(f628,plain,
    ( spl7_61
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f850,plain,
    ( spl7_52
    | spl7_53
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f849,f213,f544,f541])).

fof(f541,plain,
    ( spl7_52
  <=> ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 != k9_relat_1(X1,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f544,plain,
    ( spl7_53
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f213,plain,
    ( spl7_19
  <=> sP5(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f849,plain,
    ( ! [X1] :
        ( k1_xboole_0 = sK3
        | ~ v1_relat_1(X1)
        | k1_xboole_0 != k9_relat_1(X1,sK3) )
    | ~ spl7_19 ),
    inference(resolution,[],[f830,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

fof(f830,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl7_19 ),
    inference(resolution,[],[f215,f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f60,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP5(X1) ) ),
    inference(general_splitting,[],[f77,f86_D])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP5(X1) ) ),
    inference(cnf_transformation,[],[f86_D])).

fof(f86_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP5(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

% (27825)Refutation not found, incomplete strategy% (27825)------------------------------
% (27825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (27825)Termination reason: Refutation not found, incomplete strategy

% (27825)Memory used [KB]: 1791
% (27825)Time elapsed: 0.150 s
% (27825)------------------------------
% (27825)------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f215,plain,
    ( sP5(sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f213])).

fof(f828,plain,
    ( spl7_19
    | ~ spl7_9
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f826,f427,f130,f213])).

fof(f130,plain,
    ( spl7_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f427,plain,
    ( spl7_40
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f826,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | sP5(sK3)
    | ~ spl7_40 ),
    inference(resolution,[],[f429,f86])).

fof(f429,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f427])).

fof(f818,plain,
    ( ~ spl7_61
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f621,f541,f204,f628])).

fof(f621,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3)
    | ~ spl7_18
    | ~ spl7_52 ),
    inference(resolution,[],[f542,f206])).

fof(f542,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(X1)
        | k1_xboole_0 != k9_relat_1(X1,sK3) )
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f541])).

fof(f794,plain,
    ( spl7_40
    | ~ spl7_7
    | ~ spl7_68 ),
    inference(avatar_split_clause,[],[f793,f763,f121,f427])).

fof(f121,plain,
    ( spl7_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f763,plain,
    ( spl7_68
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f793,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl7_7
    | ~ spl7_68 ),
    inference(forward_demodulation,[],[f787,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f787,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl7_7
    | ~ spl7_68 ),
    inference(backward_demodulation,[],[f122,f765])).

fof(f765,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_68 ),
    inference(avatar_component_clause,[],[f763])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f121])).

fof(f766,plain,
    ( spl7_8
    | ~ spl7_66
    | spl7_68
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f746,f121,f763,f753,f125])).

fof(f125,plain,
    ( spl7_8
  <=> v1_funct_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f753,plain,
    ( spl7_66
  <=> sK0 = k1_relset_1(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).

fof(f746,plain,
    ( k1_xboole_0 = sK2
    | sK0 != k1_relset_1(sK0,sK2,sK3)
    | v1_funct_2(sK3,sK0,sK2)
    | ~ spl7_7 ),
    inference(resolution,[],[f122,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f756,plain,
    ( spl7_66
    | ~ spl7_7
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f751,f410,f121,f753])).

fof(f410,plain,
    ( spl7_39
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f751,plain,
    ( sK0 = k1_relset_1(sK0,sK2,sK3)
    | ~ spl7_7
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f743,f412])).

fof(f412,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f410])).

fof(f743,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3)
    | ~ spl7_7 ),
    inference(resolution,[],[f122,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f739,plain,
    ( spl7_7
    | ~ spl7_24
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f737,f363,f245,f121])).

fof(f245,plain,
    ( spl7_24
  <=> sP6(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f363,plain,
    ( spl7_37
  <=> r1_tarski(k2_relat_1(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f737,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl7_24
    | ~ spl7_37 ),
    inference(resolution,[],[f367,f247])).

fof(f247,plain,
    ( sP6(sK3,sK0)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f245])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ sP6(sK3,X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2))) )
    | ~ spl7_37 ),
    inference(resolution,[],[f365,f89])).

fof(f89,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ sP6(X3,X2) ) ),
    inference(general_splitting,[],[f78,f88_D])).

fof(f88,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | sP6(X3,X2) ) ),
    inference(cnf_transformation,[],[f88_D])).

fof(f88_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    <=> ~ sP6(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

fof(f365,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f363])).

fof(f724,plain,
    ( spl7_19
    | ~ spl7_20
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f719,f96,f217,f213])).

fof(f217,plain,
    ( spl7_20
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f96,plain,
    ( spl7_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f719,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | sP5(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f86])).

fof(f98,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f722,plain,
    ( spl7_32
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f714,f96,f323])).

fof(f323,plain,
    ( spl7_32
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f714,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f721,plain,
    ( spl7_30
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f713,f96,f303])).

fof(f303,plain,
    ( spl7_30
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f713,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_2 ),
    inference(resolution,[],[f98,f68])).

fof(f688,plain,
    ( k1_xboole_0 != sK3
    | sK0 != k1_relat_1(sK3)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f677,plain,
    ( ~ spl7_12
    | ~ spl7_25
    | spl7_63 ),
    inference(avatar_contradiction_clause,[],[f676])).

fof(f676,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_25
    | spl7_63 ),
    inference(resolution,[],[f669,f378])).

fof(f378,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(trivial_inequality_removal,[],[f377])).

fof(f377,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f375,f301])).

fof(f301,plain,
    ( ! [X2,X3] : k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_25 ),
    inference(forward_demodulation,[],[f297,f152])).

fof(f152,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_12
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f297,plain,
    ( ! [X2,X3] : k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)
    | ~ spl7_25 ),
    inference(resolution,[],[f68,f279])).

fof(f279,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl7_25 ),
    inference(resolution,[],[f267,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f267,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_25 ),
    inference(resolution,[],[f253,f187])).

fof(f253,plain,
    ( sP5(k1_xboole_0)
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl7_25
  <=> sP5(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f375,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0)
      | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ) ),
    inference(resolution,[],[f374,f134])).

fof(f134,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f50])).

fof(f50,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f374,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f82,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f73])).

% (27829)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f669,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl7_63 ),
    inference(avatar_component_clause,[],[f667])).

fof(f667,plain,
    ( spl7_63
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).

fof(f670,plain,
    ( ~ spl7_63
    | spl7_42
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f645,f544,f437,f667])).

fof(f437,plain,
    ( spl7_42
  <=> v1_funct_2(sK3,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f645,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)
    | spl7_42
    | ~ spl7_53 ),
    inference(backward_demodulation,[],[f439,f546])).

fof(f546,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f544])).

fof(f439,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f437])).

fof(f518,plain,
    ( ~ spl7_42
    | ~ spl7_5
    | spl7_8 ),
    inference(avatar_split_clause,[],[f512,f125,f111,f437])).

fof(f111,plain,
    ( spl7_5
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f512,plain,
    ( ~ v1_funct_2(sK3,k1_xboole_0,sK2)
    | ~ spl7_5
    | spl7_8 ),
    inference(backward_demodulation,[],[f127,f113])).

fof(f113,plain,
    ( k1_xboole_0 = sK0
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f127,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f125])).

fof(f448,plain,
    ( ~ spl7_9
    | ~ spl7_5
    | spl7_20 ),
    inference(avatar_split_clause,[],[f447,f217,f111,f130])).

fof(f447,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_5
    | spl7_20 ),
    inference(forward_demodulation,[],[f418,f80])).

fof(f418,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1))
    | ~ spl7_5
    | spl7_20 ),
    inference(backward_demodulation,[],[f219,f113])).

fof(f219,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f217])).

fof(f413,plain,
    ( ~ spl7_3
    | spl7_6
    | spl7_39
    | ~ spl7_2
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f408,f303,f96,f410,f115,f101])).

fof(f101,plain,
    ( spl7_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f115,plain,
    ( spl7_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f408,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2
    | ~ spl7_30 ),
    inference(forward_demodulation,[],[f404,f305])).

fof(f305,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f303])).

fof(f404,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_2 ),
    inference(resolution,[],[f76,f98])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f366,plain,
    ( spl7_37
    | ~ spl7_1
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f356,f323,f91,f363])).

fof(f91,plain,
    ( spl7_1
  <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f356,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ spl7_1
    | ~ spl7_32 ),
    inference(backward_demodulation,[],[f93,f325])).

fof(f325,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f323])).

fof(f93,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f311,plain,
    ( spl7_31
    | ~ spl7_18
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f307,f251,f204,f309])).

fof(f307,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_xboole_0)
        | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) )
    | ~ spl7_25 ),
    inference(resolution,[],[f292,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f292,plain,
    ( ! [X3] : v4_relat_1(k1_xboole_0,X3)
    | ~ spl7_25 ),
    inference(resolution,[],[f279,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f278,plain,
    ( spl7_28
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f273,f204,f150,f275])).

fof(f273,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(trivial_inequality_removal,[],[f272])).

fof(f272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f270,f152])).

fof(f270,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl7_18 ),
    inference(resolution,[],[f53,f206])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f254,plain,
    ( spl7_25
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f249,f130,f251])).

fof(f249,plain,
    ( sP5(k1_xboole_0)
    | ~ spl7_9 ),
    inference(resolution,[],[f209,f132])).

fof(f132,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f209,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | sP5(X0) ) ),
    inference(resolution,[],[f86,f134])).

fof(f248,plain,
    ( spl7_24
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f241,f96,f245])).

fof(f241,plain,
    ( sP6(sK3,sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f88,f98])).

fof(f208,plain,(
    spl7_18 ),
    inference(avatar_split_clause,[],[f202,f204])).

fof(f202,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f192,f80])).

fof(f192,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f67,f134])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f153,plain,
    ( spl7_12
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f143,f138,f150])).

fof(f138,plain,
    ( spl7_10
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f143,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl7_10 ),
    inference(resolution,[],[f140,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f140,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f141,plain,
    ( spl7_10
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f136,f130,f138])).

fof(f136,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl7_9 ),
    inference(resolution,[],[f55,f132])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

fof(f133,plain,(
    spl7_9 ),
    inference(avatar_split_clause,[],[f49,f130])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f128,plain,
    ( ~ spl7_7
    | ~ spl7_8 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(global_subsumption,[],[f45,f43])).

fof(f43,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

fof(f45,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f118,plain,
    ( spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f44,f115,f111])).

fof(f44,plain,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f46,f101])).

fof(f46,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f94,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f48,f91])).

fof(f48,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (27812)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.50  % (27818)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (27828)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.19/0.50  % (27810)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.50  % (27808)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.51  % (27820)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (27826)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.51  % (27812)Refutation not found, incomplete strategy% (27812)------------------------------
% 0.19/0.51  % (27812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (27812)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (27812)Memory used [KB]: 10746
% 0.19/0.51  % (27812)Time elapsed: 0.112 s
% 0.19/0.51  % (27812)------------------------------
% 0.19/0.51  % (27812)------------------------------
% 0.19/0.52  % (27816)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (27805)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.52  % (27806)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (27807)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (27804)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (27806)Refutation not found, incomplete strategy% (27806)------------------------------
% 0.19/0.53  % (27806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (27806)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (27806)Memory used [KB]: 10746
% 0.19/0.53  % (27806)Time elapsed: 0.125 s
% 0.19/0.53  % (27806)------------------------------
% 0.19/0.53  % (27806)------------------------------
% 0.19/0.53  % (27809)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.41/0.53  % (27830)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.53  % (27832)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.53  % (27817)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.41/0.54  % (27819)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.41/0.54  % (27831)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.41/0.54  % (27821)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.54  % (27822)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.54  % (27821)Refutation not found, incomplete strategy% (27821)------------------------------
% 1.41/0.54  % (27821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (27821)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (27821)Memory used [KB]: 10746
% 1.41/0.54  % (27821)Time elapsed: 0.137 s
% 1.41/0.54  % (27821)------------------------------
% 1.41/0.54  % (27821)------------------------------
% 1.41/0.54  % (27824)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.54  % (27811)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.41/0.54  % (27833)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.41/0.54  % (27823)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.41/0.54  % (27824)Refutation not found, incomplete strategy% (27824)------------------------------
% 1.41/0.54  % (27824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (27824)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (27824)Memory used [KB]: 10874
% 1.41/0.54  % (27824)Time elapsed: 0.151 s
% 1.41/0.54  % (27824)------------------------------
% 1.41/0.54  % (27824)------------------------------
% 1.41/0.54  % (27813)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (27814)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.41/0.55  % (27827)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.41/0.55  % (27820)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  % (27825)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.41/0.55  fof(f977,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f94,f99,f104,f118,f128,f133,f141,f153,f208,f248,f254,f278,f311,f366,f413,f448,f518,f670,f677,f688,f721,f722,f724,f739,f756,f766,f794,f818,f828,f850,f976])).
% 1.41/0.55  fof(f976,plain,(
% 1.41/0.55    ~spl7_18 | ~spl7_28 | ~spl7_31 | spl7_61),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f975])).
% 1.41/0.55  fof(f975,plain,(
% 1.41/0.55    $false | (~spl7_18 | ~spl7_28 | ~spl7_31 | spl7_61)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f974])).
% 1.41/0.55  fof(f974,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | (~spl7_18 | ~spl7_28 | ~spl7_31 | spl7_61)),
% 1.41/0.55    inference(superposition,[],[f630,f973])).
% 1.41/0.55  fof(f973,plain,(
% 1.41/0.55    ( ! [X4] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X4)) ) | (~spl7_18 | ~spl7_28 | ~spl7_31)),
% 1.41/0.55    inference(forward_demodulation,[],[f972,f277])).
% 1.41/0.55  fof(f277,plain,(
% 1.41/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl7_28),
% 1.41/0.55    inference(avatar_component_clause,[],[f275])).
% 1.41/0.55  fof(f275,plain,(
% 1.41/0.55    spl7_28 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.41/0.55  fof(f972,plain,(
% 1.41/0.55    ( ! [X4] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X4)) ) | (~spl7_18 | ~spl7_31)),
% 1.41/0.55    inference(forward_demodulation,[],[f282,f310])).
% 1.41/0.55  fof(f310,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl7_31),
% 1.41/0.55    inference(avatar_component_clause,[],[f309])).
% 1.41/0.55  fof(f309,plain,(
% 1.41/0.55    spl7_31 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 1.41/0.55  fof(f282,plain,(
% 1.41/0.55    ( ! [X4] : (k2_relat_1(k7_relat_1(k1_xboole_0,X4)) = k9_relat_1(k1_xboole_0,X4)) ) | ~spl7_18),
% 1.41/0.55    inference(resolution,[],[f56,f206])).
% 1.41/0.55  fof(f206,plain,(
% 1.41/0.55    v1_relat_1(k1_xboole_0) | ~spl7_18),
% 1.41/0.55    inference(avatar_component_clause,[],[f204])).
% 1.41/0.55  % (27815)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.55  fof(f204,plain,(
% 1.41/0.55    spl7_18 <=> v1_relat_1(k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 1.41/0.55  fof(f630,plain,(
% 1.41/0.55    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3) | spl7_61),
% 1.41/0.55    inference(avatar_component_clause,[],[f628])).
% 1.41/0.55  fof(f628,plain,(
% 1.41/0.55    spl7_61 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 1.41/0.55  fof(f850,plain,(
% 1.41/0.55    spl7_52 | spl7_53 | ~spl7_19),
% 1.41/0.55    inference(avatar_split_clause,[],[f849,f213,f544,f541])).
% 1.41/0.55  fof(f541,plain,(
% 1.41/0.55    spl7_52 <=> ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,sK3))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 1.41/0.55  fof(f544,plain,(
% 1.41/0.55    spl7_53 <=> k1_xboole_0 = sK3),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 1.41/0.55  fof(f213,plain,(
% 1.41/0.55    spl7_19 <=> sP5(sK3)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.41/0.55  fof(f849,plain,(
% 1.41/0.55    ( ! [X1] : (k1_xboole_0 = sK3 | ~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,sK3)) ) | ~spl7_19),
% 1.41/0.55    inference(resolution,[],[f830,f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f30])).
% 1.41/0.55  fof(f30,plain,(
% 1.41/0.55    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.41/0.55    inference(flattening,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f11])).
% 1.41/0.55  fof(f11,axiom,(
% 1.41/0.55    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).
% 1.41/0.55  fof(f830,plain,(
% 1.41/0.55    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl7_19),
% 1.41/0.55    inference(resolution,[],[f215,f187])).
% 1.48/0.55  fof(f187,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~sP5(X0) | r1_tarski(X0,X1)) )),
% 1.48/0.55    inference(resolution,[],[f60,f87])).
% 1.48/0.55  fof(f87,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP5(X1)) )),
% 1.48/0.55    inference(general_splitting,[],[f77,f86_D])).
% 1.48/0.55  fof(f86,plain,(
% 1.48/0.55    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP5(X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f86_D])).
% 1.48/0.55  fof(f86_D,plain,(
% 1.48/0.55    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP5(X1)) )),
% 1.48/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP5])])).
% 1.48/0.55  fof(f77,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f40])).
% 1.48/0.55  fof(f40,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.48/0.55    inference(ennf_transformation,[],[f8])).
% 1.48/0.55  fof(f8,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.48/0.55  fof(f60,plain,(
% 1.48/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f33])).
% 1.48/0.55  fof(f33,plain,(
% 1.48/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.48/0.55    inference(ennf_transformation,[],[f1])).
% 1.48/0.55  % (27825)Refutation not found, incomplete strategy% (27825)------------------------------
% 1.48/0.55  % (27825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.55  % (27825)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.55  
% 1.48/0.55  % (27825)Memory used [KB]: 1791
% 1.48/0.55  % (27825)Time elapsed: 0.150 s
% 1.48/0.55  % (27825)------------------------------
% 1.48/0.55  % (27825)------------------------------
% 1.48/0.55  fof(f1,axiom,(
% 1.48/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.48/0.55  fof(f215,plain,(
% 1.48/0.55    sP5(sK3) | ~spl7_19),
% 1.48/0.55    inference(avatar_component_clause,[],[f213])).
% 1.48/0.55  fof(f828,plain,(
% 1.48/0.55    spl7_19 | ~spl7_9 | ~spl7_40),
% 1.48/0.55    inference(avatar_split_clause,[],[f826,f427,f130,f213])).
% 1.48/0.55  fof(f130,plain,(
% 1.48/0.55    spl7_9 <=> v1_xboole_0(k1_xboole_0)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.48/0.55  fof(f427,plain,(
% 1.48/0.55    spl7_40 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.48/0.55  fof(f826,plain,(
% 1.48/0.55    ~v1_xboole_0(k1_xboole_0) | sP5(sK3) | ~spl7_40),
% 1.48/0.55    inference(resolution,[],[f429,f86])).
% 1.48/0.55  fof(f429,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl7_40),
% 1.48/0.55    inference(avatar_component_clause,[],[f427])).
% 1.48/0.55  fof(f818,plain,(
% 1.48/0.55    ~spl7_61 | ~spl7_18 | ~spl7_52),
% 1.48/0.55    inference(avatar_split_clause,[],[f621,f541,f204,f628])).
% 1.48/0.55  fof(f621,plain,(
% 1.48/0.55    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK3) | (~spl7_18 | ~spl7_52)),
% 1.48/0.55    inference(resolution,[],[f542,f206])).
% 1.48/0.55  fof(f542,plain,(
% 1.48/0.55    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 != k9_relat_1(X1,sK3)) ) | ~spl7_52),
% 1.48/0.55    inference(avatar_component_clause,[],[f541])).
% 1.48/0.55  fof(f794,plain,(
% 1.48/0.55    spl7_40 | ~spl7_7 | ~spl7_68),
% 1.48/0.55    inference(avatar_split_clause,[],[f793,f763,f121,f427])).
% 1.48/0.55  fof(f121,plain,(
% 1.48/0.55    spl7_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.48/0.55  fof(f763,plain,(
% 1.48/0.55    spl7_68 <=> k1_xboole_0 = sK2),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 1.48/0.55  fof(f793,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl7_7 | ~spl7_68)),
% 1.48/0.55    inference(forward_demodulation,[],[f787,f79])).
% 1.48/0.55  fof(f79,plain,(
% 1.48/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.48/0.55    inference(equality_resolution,[],[f66])).
% 1.48/0.55  fof(f66,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f4])).
% 1.48/0.55  fof(f4,axiom,(
% 1.48/0.55    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.48/0.55  fof(f787,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl7_7 | ~spl7_68)),
% 1.48/0.55    inference(backward_demodulation,[],[f122,f765])).
% 1.48/0.55  fof(f765,plain,(
% 1.48/0.55    k1_xboole_0 = sK2 | ~spl7_68),
% 1.48/0.55    inference(avatar_component_clause,[],[f763])).
% 1.48/0.55  fof(f122,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl7_7),
% 1.48/0.55    inference(avatar_component_clause,[],[f121])).
% 1.48/0.55  fof(f766,plain,(
% 1.48/0.55    spl7_8 | ~spl7_66 | spl7_68 | ~spl7_7),
% 1.48/0.55    inference(avatar_split_clause,[],[f746,f121,f763,f753,f125])).
% 1.48/0.55  fof(f125,plain,(
% 1.48/0.55    spl7_8 <=> v1_funct_2(sK3,sK0,sK2)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.48/0.55  fof(f753,plain,(
% 1.48/0.55    spl7_66 <=> sK0 = k1_relset_1(sK0,sK2,sK3)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_66])])).
% 1.48/0.55  fof(f746,plain,(
% 1.48/0.55    k1_xboole_0 = sK2 | sK0 != k1_relset_1(sK0,sK2,sK3) | v1_funct_2(sK3,sK0,sK2) | ~spl7_7),
% 1.48/0.55    inference(resolution,[],[f122,f75])).
% 1.48/0.55  fof(f75,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f39])).
% 1.48/0.55  fof(f39,plain,(
% 1.48/0.55    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(flattening,[],[f38])).
% 1.48/0.55  fof(f38,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f19])).
% 1.48/0.55  fof(f19,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.48/0.55  fof(f756,plain,(
% 1.48/0.55    spl7_66 | ~spl7_7 | ~spl7_39),
% 1.48/0.55    inference(avatar_split_clause,[],[f751,f410,f121,f753])).
% 1.48/0.55  fof(f410,plain,(
% 1.48/0.55    spl7_39 <=> sK0 = k1_relat_1(sK3)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 1.48/0.55  fof(f751,plain,(
% 1.48/0.55    sK0 = k1_relset_1(sK0,sK2,sK3) | (~spl7_7 | ~spl7_39)),
% 1.48/0.55    inference(forward_demodulation,[],[f743,f412])).
% 1.48/0.55  fof(f412,plain,(
% 1.48/0.55    sK0 = k1_relat_1(sK3) | ~spl7_39),
% 1.48/0.55    inference(avatar_component_clause,[],[f410])).
% 1.48/0.55  fof(f743,plain,(
% 1.48/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK2,sK3) | ~spl7_7),
% 1.48/0.55    inference(resolution,[],[f122,f68])).
% 1.48/0.55  fof(f68,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f35])).
% 1.48/0.55  fof(f35,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f16])).
% 1.48/0.55  fof(f16,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.48/0.55  fof(f739,plain,(
% 1.48/0.55    spl7_7 | ~spl7_24 | ~spl7_37),
% 1.48/0.55    inference(avatar_split_clause,[],[f737,f363,f245,f121])).
% 1.48/0.55  fof(f245,plain,(
% 1.48/0.55    spl7_24 <=> sP6(sK3,sK0)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 1.48/0.55  fof(f363,plain,(
% 1.48/0.55    spl7_37 <=> r1_tarski(k2_relat_1(sK3),sK2)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 1.48/0.55  fof(f737,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl7_24 | ~spl7_37)),
% 1.48/0.55    inference(resolution,[],[f367,f247])).
% 1.48/0.55  fof(f247,plain,(
% 1.48/0.55    sP6(sK3,sK0) | ~spl7_24),
% 1.48/0.55    inference(avatar_component_clause,[],[f245])).
% 1.48/0.55  fof(f367,plain,(
% 1.48/0.55    ( ! [X0] : (~sP6(sK3,X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))) ) | ~spl7_37),
% 1.48/0.55    inference(resolution,[],[f365,f89])).
% 1.48/0.55  fof(f89,plain,(
% 1.48/0.55    ( ! [X2,X3,X1] : (~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~sP6(X3,X2)) )),
% 1.48/0.55    inference(general_splitting,[],[f78,f88_D])).
% 1.48/0.55  fof(f88,plain,(
% 1.48/0.55    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | sP6(X3,X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f88_D])).
% 1.48/0.55  fof(f88_D,plain,(
% 1.48/0.55    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) <=> ~sP6(X3,X2)) )),
% 1.48/0.55    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP6])])).
% 1.48/0.55  fof(f78,plain,(
% 1.48/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~r1_tarski(k2_relat_1(X3),X1) | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f42])).
% 1.48/0.55  fof(f42,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.48/0.55    inference(flattening,[],[f41])).
% 1.48/0.55  fof(f41,plain,(
% 1.48/0.55    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 1.48/0.55    inference(ennf_transformation,[],[f18])).
% 1.48/0.55  fof(f18,axiom,(
% 1.48/0.55    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).
% 1.48/0.55  fof(f365,plain,(
% 1.48/0.55    r1_tarski(k2_relat_1(sK3),sK2) | ~spl7_37),
% 1.48/0.55    inference(avatar_component_clause,[],[f363])).
% 1.48/0.55  fof(f724,plain,(
% 1.48/0.55    spl7_19 | ~spl7_20 | ~spl7_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f719,f96,f217,f213])).
% 1.48/0.55  fof(f217,plain,(
% 1.48/0.55    spl7_20 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.48/0.55  fof(f96,plain,(
% 1.48/0.55    spl7_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.48/0.55  fof(f719,plain,(
% 1.48/0.55    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | sP5(sK3) | ~spl7_2),
% 1.48/0.55    inference(resolution,[],[f98,f86])).
% 1.48/0.55  fof(f98,plain,(
% 1.48/0.55    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_2),
% 1.48/0.55    inference(avatar_component_clause,[],[f96])).
% 1.48/0.55  fof(f722,plain,(
% 1.48/0.55    spl7_32 | ~spl7_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f714,f96,f323])).
% 1.48/0.55  fof(f323,plain,(
% 1.48/0.55    spl7_32 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 1.48/0.55  fof(f714,plain,(
% 1.48/0.55    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_2),
% 1.48/0.55    inference(resolution,[],[f98,f69])).
% 1.48/0.55  fof(f69,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f36])).
% 1.48/0.55  fof(f36,plain,(
% 1.48/0.55    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.55    inference(ennf_transformation,[],[f17])).
% 1.48/0.55  fof(f17,axiom,(
% 1.48/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.48/0.55  fof(f721,plain,(
% 1.48/0.55    spl7_30 | ~spl7_2),
% 1.48/0.55    inference(avatar_split_clause,[],[f713,f96,f303])).
% 1.48/0.55  fof(f303,plain,(
% 1.48/0.55    spl7_30 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 1.48/0.55  fof(f713,plain,(
% 1.48/0.55    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_2),
% 1.48/0.55    inference(resolution,[],[f98,f68])).
% 1.48/0.55  fof(f688,plain,(
% 1.48/0.55    k1_xboole_0 != sK3 | sK0 != k1_relat_1(sK3) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 = sK0),
% 1.48/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.48/0.55  fof(f677,plain,(
% 1.48/0.55    ~spl7_12 | ~spl7_25 | spl7_63),
% 1.48/0.55    inference(avatar_contradiction_clause,[],[f676])).
% 1.48/0.55  fof(f676,plain,(
% 1.48/0.55    $false | (~spl7_12 | ~spl7_25 | spl7_63)),
% 1.48/0.55    inference(resolution,[],[f669,f378])).
% 1.48/0.55  fof(f378,plain,(
% 1.48/0.55    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl7_12 | ~spl7_25)),
% 1.48/0.55    inference(trivial_inequality_removal,[],[f377])).
% 1.48/0.55  fof(f377,plain,(
% 1.48/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl7_12 | ~spl7_25)),
% 1.48/0.55    inference(forward_demodulation,[],[f375,f301])).
% 1.48/0.55  fof(f301,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k1_xboole_0 = k1_relset_1(X2,X3,k1_xboole_0)) ) | (~spl7_12 | ~spl7_25)),
% 1.48/0.55    inference(forward_demodulation,[],[f297,f152])).
% 1.48/0.55  fof(f152,plain,(
% 1.48/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_12),
% 1.48/0.55    inference(avatar_component_clause,[],[f150])).
% 1.48/0.55  fof(f150,plain,(
% 1.48/0.55    spl7_12 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.48/0.55  fof(f297,plain,(
% 1.48/0.55    ( ! [X2,X3] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X2,X3,k1_xboole_0)) ) | ~spl7_25),
% 1.48/0.55    inference(resolution,[],[f68,f279])).
% 1.48/0.55  fof(f279,plain,(
% 1.48/0.55    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl7_25),
% 1.48/0.55    inference(resolution,[],[f267,f62])).
% 1.48/0.55  fof(f62,plain,(
% 1.48/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f7])).
% 1.48/0.55  fof(f7,axiom,(
% 1.48/0.55    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.48/0.55  fof(f267,plain,(
% 1.48/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_25),
% 1.48/0.55    inference(resolution,[],[f253,f187])).
% 1.48/0.55  fof(f253,plain,(
% 1.48/0.55    sP5(k1_xboole_0) | ~spl7_25),
% 1.48/0.55    inference(avatar_component_clause,[],[f251])).
% 1.48/0.55  fof(f251,plain,(
% 1.48/0.55    spl7_25 <=> sP5(k1_xboole_0)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.48/0.55  fof(f375,plain,(
% 1.48/0.55    ( ! [X0] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X0,k1_xboole_0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) )),
% 1.48/0.55    inference(resolution,[],[f374,f134])).
% 1.48/0.55  fof(f134,plain,(
% 1.48/0.55    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.48/0.55    inference(forward_demodulation,[],[f51,f50])).
% 1.48/0.55  fof(f50,plain,(
% 1.48/0.55    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.48/0.55    inference(cnf_transformation,[],[f5])).
% 1.48/0.55  fof(f5,axiom,(
% 1.48/0.55    ! [X0] : k2_subset_1(X0) = X0),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.48/0.55  fof(f51,plain,(
% 1.48/0.55    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.48/0.55    inference(cnf_transformation,[],[f6])).
% 1.48/0.55  fof(f6,axiom,(
% 1.48/0.55    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.48/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.48/0.55  fof(f374,plain,(
% 1.48/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.48/0.55    inference(forward_demodulation,[],[f82,f80])).
% 1.48/0.55  fof(f80,plain,(
% 1.48/0.55    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.48/0.55    inference(equality_resolution,[],[f65])).
% 1.48/0.55  fof(f65,plain,(
% 1.48/0.55    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f4])).
% 1.48/0.55  fof(f82,plain,(
% 1.48/0.55    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.48/0.55    inference(equality_resolution,[],[f73])).
% 1.48/0.55  % (27829)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.48/0.55  fof(f73,plain,(
% 1.48/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 1.48/0.55    inference(cnf_transformation,[],[f39])).
% 1.48/0.55  fof(f669,plain,(
% 1.48/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | spl7_63),
% 1.48/0.55    inference(avatar_component_clause,[],[f667])).
% 1.48/0.55  fof(f667,plain,(
% 1.48/0.55    spl7_63 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,sK2)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_63])])).
% 1.48/0.55  fof(f670,plain,(
% 1.48/0.55    ~spl7_63 | spl7_42 | ~spl7_53),
% 1.48/0.55    inference(avatar_split_clause,[],[f645,f544,f437,f667])).
% 1.48/0.55  fof(f437,plain,(
% 1.48/0.55    spl7_42 <=> v1_funct_2(sK3,k1_xboole_0,sK2)),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.48/0.55  fof(f645,plain,(
% 1.48/0.55    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK2) | (spl7_42 | ~spl7_53)),
% 1.48/0.55    inference(backward_demodulation,[],[f439,f546])).
% 1.48/0.55  fof(f546,plain,(
% 1.48/0.55    k1_xboole_0 = sK3 | ~spl7_53),
% 1.48/0.55    inference(avatar_component_clause,[],[f544])).
% 1.48/0.55  fof(f439,plain,(
% 1.48/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | spl7_42),
% 1.48/0.55    inference(avatar_component_clause,[],[f437])).
% 1.48/0.55  fof(f518,plain,(
% 1.48/0.55    ~spl7_42 | ~spl7_5 | spl7_8),
% 1.48/0.55    inference(avatar_split_clause,[],[f512,f125,f111,f437])).
% 1.48/0.55  fof(f111,plain,(
% 1.48/0.55    spl7_5 <=> k1_xboole_0 = sK0),
% 1.48/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.48/0.55  fof(f512,plain,(
% 1.48/0.55    ~v1_funct_2(sK3,k1_xboole_0,sK2) | (~spl7_5 | spl7_8)),
% 1.48/0.55    inference(backward_demodulation,[],[f127,f113])).
% 1.48/0.55  fof(f113,plain,(
% 1.48/0.55    k1_xboole_0 = sK0 | ~spl7_5),
% 1.48/0.55    inference(avatar_component_clause,[],[f111])).
% 1.48/0.55  fof(f127,plain,(
% 1.48/0.55    ~v1_funct_2(sK3,sK0,sK2) | spl7_8),
% 1.48/0.55    inference(avatar_component_clause,[],[f125])).
% 1.48/0.55  fof(f448,plain,(
% 1.48/0.55    ~spl7_9 | ~spl7_5 | spl7_20),
% 1.48/0.55    inference(avatar_split_clause,[],[f447,f217,f111,f130])).
% 1.48/0.55  fof(f447,plain,(
% 1.48/0.55    ~v1_xboole_0(k1_xboole_0) | (~spl7_5 | spl7_20)),
% 1.48/0.55    inference(forward_demodulation,[],[f418,f80])).
% 1.48/0.56  fof(f418,plain,(
% 1.48/0.56    ~v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) | (~spl7_5 | spl7_20)),
% 1.48/0.56    inference(backward_demodulation,[],[f219,f113])).
% 1.48/0.56  fof(f219,plain,(
% 1.48/0.56    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl7_20),
% 1.48/0.56    inference(avatar_component_clause,[],[f217])).
% 1.48/0.56  fof(f413,plain,(
% 1.48/0.56    ~spl7_3 | spl7_6 | spl7_39 | ~spl7_2 | ~spl7_30),
% 1.48/0.56    inference(avatar_split_clause,[],[f408,f303,f96,f410,f115,f101])).
% 1.48/0.56  fof(f101,plain,(
% 1.48/0.56    spl7_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.48/0.56  fof(f115,plain,(
% 1.48/0.56    spl7_6 <=> k1_xboole_0 = sK1),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.48/0.56  fof(f408,plain,(
% 1.48/0.56    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl7_2 | ~spl7_30)),
% 1.48/0.56    inference(forward_demodulation,[],[f404,f305])).
% 1.48/0.56  fof(f305,plain,(
% 1.48/0.56    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_30),
% 1.48/0.56    inference(avatar_component_clause,[],[f303])).
% 1.48/0.56  fof(f404,plain,(
% 1.48/0.56    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f76,f98])).
% 1.48/0.56  fof(f76,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f39])).
% 1.48/0.56  fof(f366,plain,(
% 1.48/0.56    spl7_37 | ~spl7_1 | ~spl7_32),
% 1.48/0.56    inference(avatar_split_clause,[],[f356,f323,f91,f363])).
% 1.48/0.56  fof(f91,plain,(
% 1.48/0.56    spl7_1 <=> r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.48/0.56  fof(f356,plain,(
% 1.48/0.56    r1_tarski(k2_relat_1(sK3),sK2) | (~spl7_1 | ~spl7_32)),
% 1.48/0.56    inference(backward_demodulation,[],[f93,f325])).
% 1.48/0.56  fof(f325,plain,(
% 1.48/0.56    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl7_32),
% 1.48/0.56    inference(avatar_component_clause,[],[f323])).
% 1.48/0.56  fof(f93,plain,(
% 1.48/0.56    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) | ~spl7_1),
% 1.48/0.56    inference(avatar_component_clause,[],[f91])).
% 1.48/0.56  fof(f311,plain,(
% 1.48/0.56    spl7_31 | ~spl7_18 | ~spl7_25),
% 1.48/0.56    inference(avatar_split_clause,[],[f307,f251,f204,f309])).
% 1.48/0.56  fof(f307,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(k1_xboole_0) | k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl7_25),
% 1.48/0.56    inference(resolution,[],[f292,f58])).
% 1.48/0.56  fof(f58,plain,(
% 1.48/0.56    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 1.48/0.56    inference(cnf_transformation,[],[f32])).
% 1.48/0.56  fof(f32,plain,(
% 1.48/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.48/0.56    inference(flattening,[],[f31])).
% 1.48/0.56  fof(f31,plain,(
% 1.48/0.56    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.48/0.56    inference(ennf_transformation,[],[f12])).
% 1.48/0.56  fof(f12,axiom,(
% 1.48/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 1.48/0.56  fof(f292,plain,(
% 1.48/0.56    ( ! [X3] : (v4_relat_1(k1_xboole_0,X3)) ) | ~spl7_25),
% 1.48/0.56    inference(resolution,[],[f279,f70])).
% 1.48/0.56  fof(f70,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f37])).
% 1.48/0.56  fof(f37,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f22])).
% 1.48/0.56  fof(f22,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.48/0.56    inference(pure_predicate_removal,[],[f15])).
% 1.48/0.56  fof(f15,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.48/0.56  fof(f278,plain,(
% 1.48/0.56    spl7_28 | ~spl7_12 | ~spl7_18),
% 1.48/0.56    inference(avatar_split_clause,[],[f273,f204,f150,f275])).
% 1.48/0.56  fof(f273,plain,(
% 1.48/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl7_12 | ~spl7_18)),
% 1.48/0.56    inference(trivial_inequality_removal,[],[f272])).
% 1.48/0.56  fof(f272,plain,(
% 1.48/0.56    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl7_12 | ~spl7_18)),
% 1.48/0.56    inference(forward_demodulation,[],[f270,f152])).
% 1.48/0.56  fof(f270,plain,(
% 1.48/0.56    k1_xboole_0 = k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~spl7_18),
% 1.48/0.56    inference(resolution,[],[f53,f206])).
% 1.48/0.56  fof(f53,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f25])).
% 1.48/0.56  fof(f25,plain,(
% 1.48/0.56    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f13])).
% 1.48/0.56  fof(f13,axiom,(
% 1.48/0.56    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 1.48/0.56  fof(f254,plain,(
% 1.48/0.56    spl7_25 | ~spl7_9),
% 1.48/0.56    inference(avatar_split_clause,[],[f249,f130,f251])).
% 1.48/0.56  fof(f249,plain,(
% 1.48/0.56    sP5(k1_xboole_0) | ~spl7_9),
% 1.48/0.56    inference(resolution,[],[f209,f132])).
% 1.48/0.56  fof(f132,plain,(
% 1.48/0.56    v1_xboole_0(k1_xboole_0) | ~spl7_9),
% 1.48/0.56    inference(avatar_component_clause,[],[f130])).
% 1.48/0.56  fof(f209,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_xboole_0(X0) | sP5(X0)) )),
% 1.48/0.56    inference(resolution,[],[f86,f134])).
% 1.48/0.56  fof(f248,plain,(
% 1.48/0.56    spl7_24 | ~spl7_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f241,f96,f245])).
% 1.48/0.56  fof(f241,plain,(
% 1.48/0.56    sP6(sK3,sK0) | ~spl7_2),
% 1.48/0.56    inference(resolution,[],[f88,f98])).
% 1.48/0.56  fof(f208,plain,(
% 1.48/0.56    spl7_18),
% 1.48/0.56    inference(avatar_split_clause,[],[f202,f204])).
% 1.48/0.56  fof(f202,plain,(
% 1.48/0.56    v1_relat_1(k1_xboole_0)),
% 1.48/0.56    inference(superposition,[],[f192,f80])).
% 1.48/0.56  fof(f192,plain,(
% 1.48/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.48/0.56    inference(resolution,[],[f67,f134])).
% 1.48/0.56  fof(f67,plain,(
% 1.48/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.48/0.56    inference(cnf_transformation,[],[f34])).
% 1.48/0.56  fof(f34,plain,(
% 1.48/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.48/0.56    inference(ennf_transformation,[],[f14])).
% 1.48/0.56  fof(f14,axiom,(
% 1.48/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.48/0.56  fof(f153,plain,(
% 1.48/0.56    spl7_12 | ~spl7_10),
% 1.48/0.56    inference(avatar_split_clause,[],[f143,f138,f150])).
% 1.48/0.56  fof(f138,plain,(
% 1.48/0.56    spl7_10 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 1.48/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.48/0.56  fof(f143,plain,(
% 1.48/0.56    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl7_10),
% 1.48/0.56    inference(resolution,[],[f140,f54])).
% 1.48/0.56  fof(f54,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 1.48/0.56    inference(cnf_transformation,[],[f26])).
% 1.48/0.56  fof(f26,plain,(
% 1.48/0.56    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f3])).
% 1.48/0.56  fof(f3,axiom,(
% 1.48/0.56    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.48/0.56  fof(f140,plain,(
% 1.48/0.56    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl7_10),
% 1.48/0.56    inference(avatar_component_clause,[],[f138])).
% 1.48/0.56  fof(f141,plain,(
% 1.48/0.56    spl7_10 | ~spl7_9),
% 1.48/0.56    inference(avatar_split_clause,[],[f136,f130,f138])).
% 1.48/0.56  fof(f136,plain,(
% 1.48/0.56    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl7_9),
% 1.48/0.56    inference(resolution,[],[f55,f132])).
% 1.48/0.56  fof(f55,plain,(
% 1.48/0.56    ( ! [X0] : (~v1_xboole_0(X0) | v1_xboole_0(k1_relat_1(X0))) )),
% 1.48/0.56    inference(cnf_transformation,[],[f27])).
% 1.48/0.56  fof(f27,plain,(
% 1.48/0.56    ! [X0] : (v1_xboole_0(k1_relat_1(X0)) | ~v1_xboole_0(X0))),
% 1.48/0.56    inference(ennf_transformation,[],[f9])).
% 1.48/0.56  fof(f9,axiom,(
% 1.48/0.56    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k1_relat_1(X0)))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).
% 1.48/0.56  fof(f133,plain,(
% 1.48/0.56    spl7_9),
% 1.48/0.56    inference(avatar_split_clause,[],[f49,f130])).
% 1.48/0.56  fof(f49,plain,(
% 1.48/0.56    v1_xboole_0(k1_xboole_0)),
% 1.48/0.56    inference(cnf_transformation,[],[f2])).
% 1.48/0.56  fof(f2,axiom,(
% 1.48/0.56    v1_xboole_0(k1_xboole_0)),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.48/0.56  fof(f128,plain,(
% 1.48/0.56    ~spl7_7 | ~spl7_8),
% 1.48/0.56    inference(avatar_split_clause,[],[f119,f125,f121])).
% 1.48/0.56  fof(f119,plain,(
% 1.48/0.56    ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.48/0.56    inference(global_subsumption,[],[f45,f43])).
% 1.48/0.56  fof(f43,plain,(
% 1.48/0.56    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK0,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f24,plain,(
% 1.48/0.56    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.48/0.56    inference(flattening,[],[f23])).
% 1.48/0.56  fof(f23,plain,(
% 1.48/0.56    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.48/0.56    inference(ennf_transformation,[],[f21])).
% 1.48/0.56  fof(f21,negated_conjecture,(
% 1.48/0.56    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.48/0.56    inference(negated_conjecture,[],[f20])).
% 1.48/0.56  fof(f20,conjecture,(
% 1.48/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.48/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).
% 1.48/0.56  fof(f45,plain,(
% 1.48/0.56    v1_funct_1(sK3)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f118,plain,(
% 1.48/0.56    spl7_5 | ~spl7_6),
% 1.48/0.56    inference(avatar_split_clause,[],[f44,f115,f111])).
% 1.48/0.56  fof(f44,plain,(
% 1.48/0.56    k1_xboole_0 != sK1 | k1_xboole_0 = sK0),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f104,plain,(
% 1.48/0.56    spl7_3),
% 1.48/0.56    inference(avatar_split_clause,[],[f46,f101])).
% 1.48/0.56  fof(f46,plain,(
% 1.48/0.56    v1_funct_2(sK3,sK0,sK1)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f99,plain,(
% 1.48/0.56    spl7_2),
% 1.48/0.56    inference(avatar_split_clause,[],[f47,f96])).
% 1.48/0.56  fof(f47,plain,(
% 1.48/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  fof(f94,plain,(
% 1.48/0.56    spl7_1),
% 1.48/0.56    inference(avatar_split_clause,[],[f48,f91])).
% 1.48/0.56  fof(f48,plain,(
% 1.48/0.56    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 1.48/0.56    inference(cnf_transformation,[],[f24])).
% 1.48/0.56  % SZS output end Proof for theBenchmark
% 1.48/0.56  % (27820)------------------------------
% 1.48/0.56  % (27820)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (27820)Termination reason: Refutation
% 1.48/0.56  
% 1.48/0.56  % (27820)Memory used [KB]: 11257
% 1.48/0.56  % (27820)Time elapsed: 0.153 s
% 1.48/0.56  % (27820)------------------------------
% 1.48/0.56  % (27820)------------------------------
% 1.48/0.56  % (27803)Success in time 0.206 s
%------------------------------------------------------------------------------
