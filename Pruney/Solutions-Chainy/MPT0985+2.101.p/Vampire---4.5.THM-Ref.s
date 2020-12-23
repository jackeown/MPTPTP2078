%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:15 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 749 expanded)
%              Number of leaves         :   29 ( 182 expanded)
%              Depth                    :   19
%              Number of atoms          :  453 (3197 expanded)
%              Number of equality atoms :   85 ( 484 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f224,f232,f355,f365,f452,f572,f659,f665,f887,f912,f1170,f1245,f1349])).

fof(f1349,plain,
    ( spl5_2
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f1345])).

fof(f1345,plain,
    ( $false
    | spl5_2
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f170,f1187])).

fof(f1187,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f133,f354])).

fof(f354,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl5_9
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f133,plain,(
    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f132,f119])).

fof(f119,plain,(
    sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f103,f98])).

fof(f98,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f95,f44])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f95,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f42,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f103,plain,(
    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f43,f94,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f94,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f132,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f126,f104])).

fof(f104,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f43,f94,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f126,plain,(
    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f105,f106,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f106,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f94,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f105,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(unit_resulting_resolution,[],[f40,f94,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f170,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_2
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1245,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1243])).

fof(f1243,plain,
    ( $false
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f94,f40,f174,f48])).

fof(f174,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl5_3
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1170,plain,
    ( spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(avatar_contradiction_clause,[],[f1168])).

fof(f1168,plain,
    ( $false
    | spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f68,f1161,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1161,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(unit_resulting_resolution,[],[f944,f957])).

fof(f957,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f704,f956])).

fof(f956,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f913,f709])).

fof(f709,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f579,f658])).

fof(f658,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f656])).

fof(f656,plain,
    ( spl5_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f579,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f98,f350])).

fof(f350,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl5_8
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f913,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f669,f886])).

fof(f886,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f884])).

fof(f884,plain,
    ( spl5_13
  <=> k1_xboole_0 = k2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f669,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0))
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f104,f658])).

fof(f704,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0)
        | ~ r1_tarski(k1_xboole_0,X0) )
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f385,f658])).

fof(f385,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) )
    | ~ spl5_5
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f223,f350])).

fof(f223,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f944,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_8
    | ~ spl5_11
    | ~ spl5_13 ),
    inference(backward_demodulation,[],[f725,f886])).

fof(f725,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f622,f658])).

fof(f622,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl5_2
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f170,f350])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f912,plain,(
    spl5_12 ),
    inference(avatar_contradiction_clause,[],[f910])).

fof(f910,plain,
    ( $false
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f68,f882,f71])).

fof(f882,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f880])).

fof(f880,plain,
    ( spl5_12
  <=> r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f887,plain,
    ( ~ spl5_12
    | spl5_13
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f749,f656,f348,f884,f880])).

fof(f749,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f724,f658])).

fof(f724,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(backward_demodulation,[],[f619,f658])).

fof(f619,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f618,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f618,plain,
    ( k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))
    | ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f617,f350])).

fof(f617,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f597,f80])).

fof(f597,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f270,f350])).

fof(f270,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2))
    | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) ),
    inference(resolution,[],[f264,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f264,plain,(
    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) ),
    inference(unit_resulting_resolution,[],[f131,f71])).

fof(f131,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f130,f119])).

fof(f130,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) ),
    inference(forward_demodulation,[],[f127,f104])).

fof(f127,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2))))) ),
    inference(unit_resulting_resolution,[],[f105,f106,f66])).

fof(f66,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

% (23167)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f665,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f663])).

fof(f663,plain,
    ( $false
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f68,f654,f71])).

fof(f654,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f652])).

fof(f652,plain,
    ( spl5_10
  <=> r1_tarski(k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f659,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f611,f348,f656,f652])).

fof(f611,plain,
    ( k1_xboole_0 = sK2
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f610,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f610,plain,
    ( sK2 = k2_zfmisc_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f609,f350])).

fof(f609,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_8 ),
    inference(forward_demodulation,[],[f587,f79])).

fof(f587,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1)
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f161,f350])).

fof(f161,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),sK2)
    | sK2 = k2_zfmisc_1(sK0,sK1) ),
    inference(resolution,[],[f96,f54])).

fof(f96,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f42,f71])).

fof(f572,plain,
    ( spl5_1
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f567])).

fof(f567,plain,
    ( $false
    | spl5_1
    | ~ spl5_9 ),
    inference(unit_resulting_resolution,[],[f166,f467,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f467,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0))
    | ~ spl5_9 ),
    inference(backward_demodulation,[],[f264,f354])).

fof(f166,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_1
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f452,plain,
    ( spl5_1
    | ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | spl5_1
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f69,f68,f398,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f398,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_1
    | ~ spl5_8 ),
    inference(backward_demodulation,[],[f294,f350])).

fof(f294,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f131,f288,f75])).

fof(f288,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f202,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f202,plain,
    ( r2_hidden(sK3(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)),k2_funct_1(sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f195,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f195,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f166,f70])).

fof(f69,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f365,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f96,f346,f70])).

fof(f346,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f355,plain,
    ( ~ spl5_7
    | spl5_8
    | spl5_9 ),
    inference(avatar_split_clause,[],[f102,f352,f348,f344])).

fof(f102,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f42,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f41,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f232,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f42,f220,f56])).

fof(f220,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl5_4
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f224,plain,
    ( ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f101,f222,f218])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | ~ v1_relat_1(sK2)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(backward_demodulation,[],[f88,f98])).

% (23185)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f88,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | ~ r1_tarski(k2_relat_1(sK2),X0)
      | v1_funct_2(sK2,k1_relat_1(sK2),X0) ) ),
    inference(resolution,[],[f40,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | v1_funct_2(X1,k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

% (23175)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

fof(f175,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f39,f172,f168,f164])).

fof(f39,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:18:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.55  % (23162)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.58  % (23168)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.58  % (23176)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.58  % (23170)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (23164)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.58  % (23158)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.58  % (23184)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.58  % (23186)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.59  % (23181)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (23159)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.59  % (23168)Refutation not found, incomplete strategy% (23168)------------------------------
% 0.22/0.59  % (23168)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (23168)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (23168)Memory used [KB]: 10618
% 0.22/0.59  % (23168)Time elapsed: 0.156 s
% 0.22/0.59  % (23168)------------------------------
% 0.22/0.59  % (23168)------------------------------
% 0.22/0.60  % (23173)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.60  % (23160)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.60  % (23169)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.60  % (23163)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.61  % (23165)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.61  % (23166)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.61  % (23174)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.61  % (23178)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.62  % (23179)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.62  % (23172)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.62  % (23162)Refutation found. Thanks to Tanya!
% 0.22/0.62  % SZS status Theorem for theBenchmark
% 0.22/0.62  % (23171)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.62  % (23161)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.84/0.62  % (23180)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.84/0.62  % (23187)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.84/0.63  % SZS output start Proof for theBenchmark
% 1.84/0.63  fof(f1350,plain,(
% 1.84/0.63    $false),
% 1.84/0.63    inference(avatar_sat_refutation,[],[f175,f224,f232,f355,f365,f452,f572,f659,f665,f887,f912,f1170,f1245,f1349])).
% 1.84/0.63  fof(f1349,plain,(
% 1.84/0.63    spl5_2 | ~spl5_9),
% 1.84/0.63    inference(avatar_contradiction_clause,[],[f1345])).
% 1.84/0.63  fof(f1345,plain,(
% 1.84/0.63    $false | (spl5_2 | ~spl5_9)),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f170,f1187])).
% 1.84/0.63  fof(f1187,plain,(
% 1.84/0.63    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl5_9),
% 1.84/0.63    inference(backward_demodulation,[],[f133,f354])).
% 1.84/0.63  fof(f354,plain,(
% 1.84/0.63    sK0 = k1_relat_1(sK2) | ~spl5_9),
% 1.84/0.63    inference(avatar_component_clause,[],[f352])).
% 1.84/0.63  fof(f352,plain,(
% 1.84/0.63    spl5_9 <=> sK0 = k1_relat_1(sK2)),
% 1.84/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.84/0.63  fof(f133,plain,(
% 1.84/0.63    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 1.84/0.63    inference(forward_demodulation,[],[f132,f119])).
% 1.84/0.63  fof(f119,plain,(
% 1.84/0.63    sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.84/0.63    inference(forward_demodulation,[],[f103,f98])).
% 1.84/0.63  fof(f98,plain,(
% 1.84/0.63    sK1 = k2_relat_1(sK2)),
% 1.84/0.63    inference(forward_demodulation,[],[f95,f44])).
% 1.84/0.63  fof(f44,plain,(
% 1.84/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.84/0.63    inference(cnf_transformation,[],[f21])).
% 1.84/0.63  fof(f21,plain,(
% 1.84/0.63    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.84/0.63    inference(flattening,[],[f20])).
% 1.84/0.63  fof(f20,plain,(
% 1.84/0.63    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.84/0.63    inference(ennf_transformation,[],[f19])).
% 1.84/0.63  fof(f19,negated_conjecture,(
% 1.84/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.84/0.63    inference(negated_conjecture,[],[f18])).
% 1.84/0.63  fof(f18,conjecture,(
% 1.84/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.84/0.63  fof(f95,plain,(
% 1.84/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f42,f55])).
% 1.84/0.63  fof(f55,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f26])).
% 1.84/0.63  fof(f26,plain,(
% 1.84/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.63    inference(ennf_transformation,[],[f14])).
% 1.84/0.63  fof(f14,axiom,(
% 1.84/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.84/0.63  fof(f42,plain,(
% 1.84/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/0.63    inference(cnf_transformation,[],[f21])).
% 1.84/0.63  fof(f103,plain,(
% 1.84/0.63    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f40,f43,f94,f45])).
% 1.84/0.63  fof(f45,plain,(
% 1.84/0.63    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f23])).
% 1.84/0.63  fof(f23,plain,(
% 1.84/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.63    inference(flattening,[],[f22])).
% 1.84/0.63  fof(f22,plain,(
% 1.84/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f10])).
% 1.84/0.63  fof(f10,axiom,(
% 1.84/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.84/0.63  fof(f94,plain,(
% 1.84/0.63    v1_relat_1(sK2)),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f42,f56])).
% 1.84/0.63  fof(f56,plain,(
% 1.84/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f27])).
% 1.84/0.63  fof(f27,plain,(
% 1.84/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.63    inference(ennf_transformation,[],[f11])).
% 1.84/0.63  fof(f11,axiom,(
% 1.84/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.84/0.63  fof(f43,plain,(
% 1.84/0.63    v2_funct_1(sK2)),
% 1.84/0.63    inference(cnf_transformation,[],[f21])).
% 1.84/0.63  fof(f40,plain,(
% 1.84/0.63    v1_funct_1(sK2)),
% 1.84/0.63    inference(cnf_transformation,[],[f21])).
% 1.84/0.63  fof(f132,plain,(
% 1.84/0.63    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))),
% 1.84/0.63    inference(forward_demodulation,[],[f126,f104])).
% 1.84/0.63  fof(f104,plain,(
% 1.84/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f40,f43,f94,f46])).
% 1.84/0.63  fof(f46,plain,(
% 1.84/0.63    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 1.84/0.63    inference(cnf_transformation,[],[f23])).
% 1.84/0.63  fof(f126,plain,(
% 1.84/0.63    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f105,f106,f65])).
% 1.84/0.63  fof(f65,plain,(
% 1.84/0.63    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f33])).
% 1.84/0.63  fof(f33,plain,(
% 1.84/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.63    inference(flattening,[],[f32])).
% 1.84/0.63  fof(f32,plain,(
% 1.84/0.63    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/0.63    inference(ennf_transformation,[],[f16])).
% 1.84/0.63  fof(f16,axiom,(
% 1.84/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.84/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.84/0.63  fof(f106,plain,(
% 1.84/0.63    v1_funct_1(k2_funct_1(sK2))),
% 1.84/0.63    inference(unit_resulting_resolution,[],[f40,f94,f48])).
% 1.84/0.63  fof(f48,plain,(
% 1.84/0.63    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/0.63    inference(cnf_transformation,[],[f25])).
% 1.84/0.63  fof(f25,plain,(
% 1.84/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.63    inference(flattening,[],[f24])).
% 1.84/0.64  fof(f24,plain,(
% 1.84/0.64    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/0.64    inference(ennf_transformation,[],[f9])).
% 1.84/0.64  fof(f9,axiom,(
% 1.84/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.84/0.64  fof(f105,plain,(
% 1.84/0.64    v1_relat_1(k2_funct_1(sK2))),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f40,f94,f47])).
% 1.84/0.64  fof(f47,plain,(
% 1.84/0.64    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f25])).
% 1.84/0.64  fof(f170,plain,(
% 1.84/0.64    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_2),
% 1.84/0.64    inference(avatar_component_clause,[],[f168])).
% 1.84/0.64  fof(f168,plain,(
% 1.84/0.64    spl5_2 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.84/0.64  fof(f1245,plain,(
% 1.84/0.64    spl5_3),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f1243])).
% 1.84/0.64  fof(f1243,plain,(
% 1.84/0.64    $false | spl5_3),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f94,f40,f174,f48])).
% 1.84/0.64  fof(f174,plain,(
% 1.84/0.64    ~v1_funct_1(k2_funct_1(sK2)) | spl5_3),
% 1.84/0.64    inference(avatar_component_clause,[],[f172])).
% 1.84/0.64  fof(f172,plain,(
% 1.84/0.64    spl5_3 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.84/0.64  fof(f1170,plain,(
% 1.84/0.64    spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_11 | ~spl5_13),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f1168])).
% 1.84/0.64  fof(f1168,plain,(
% 1.84/0.64    $false | (spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f68,f1161,f71])).
% 1.84/0.64  fof(f71,plain,(
% 1.84/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.84/0.64    inference(cnf_transformation,[],[f7])).
% 1.84/0.64  fof(f7,axiom,(
% 1.84/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.84/0.64  fof(f1161,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,sK0) | (spl5_2 | ~spl5_5 | ~spl5_8 | ~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f944,f957])).
% 1.84/0.64  fof(f957,plain,(
% 1.84/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl5_5 | ~spl5_8 | ~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(backward_demodulation,[],[f704,f956])).
% 1.84/0.64  fof(f956,plain,(
% 1.84/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_8 | ~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(forward_demodulation,[],[f913,f709])).
% 1.84/0.64  fof(f709,plain,(
% 1.84/0.64    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl5_8 | ~spl5_11)),
% 1.84/0.64    inference(backward_demodulation,[],[f579,f658])).
% 1.84/0.64  fof(f658,plain,(
% 1.84/0.64    k1_xboole_0 = sK2 | ~spl5_11),
% 1.84/0.64    inference(avatar_component_clause,[],[f656])).
% 1.84/0.64  fof(f656,plain,(
% 1.84/0.64    spl5_11 <=> k1_xboole_0 = sK2),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.84/0.64  fof(f579,plain,(
% 1.84/0.64    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_8),
% 1.84/0.64    inference(backward_demodulation,[],[f98,f350])).
% 1.84/0.64  fof(f350,plain,(
% 1.84/0.64    k1_xboole_0 = sK1 | ~spl5_8),
% 1.84/0.64    inference(avatar_component_clause,[],[f348])).
% 1.84/0.64  fof(f348,plain,(
% 1.84/0.64    spl5_8 <=> k1_xboole_0 = sK1),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.84/0.64  fof(f913,plain,(
% 1.84/0.64    k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) | (~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(backward_demodulation,[],[f669,f886])).
% 1.84/0.64  fof(f886,plain,(
% 1.84/0.64    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~spl5_13),
% 1.84/0.64    inference(avatar_component_clause,[],[f884])).
% 1.84/0.64  fof(f884,plain,(
% 1.84/0.64    spl5_13 <=> k1_xboole_0 = k2_funct_1(k1_xboole_0)),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.84/0.64  fof(f669,plain,(
% 1.84/0.64    k1_relat_1(k1_xboole_0) = k2_relat_1(k2_funct_1(k1_xboole_0)) | ~spl5_11),
% 1.84/0.64    inference(backward_demodulation,[],[f104,f658])).
% 1.84/0.64  fof(f704,plain,(
% 1.84/0.64    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),X0) | ~r1_tarski(k1_xboole_0,X0)) ) | (~spl5_5 | ~spl5_8 | ~spl5_11)),
% 1.84/0.64    inference(backward_demodulation,[],[f385,f658])).
% 1.84/0.64  fof(f385,plain,(
% 1.84/0.64    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) ) | (~spl5_5 | ~spl5_8)),
% 1.84/0.64    inference(backward_demodulation,[],[f223,f350])).
% 1.84/0.64  fof(f223,plain,(
% 1.84/0.64    ( ! [X0] : (v1_funct_2(sK2,k1_relat_1(sK2),X0) | ~r1_tarski(sK1,X0)) ) | ~spl5_5),
% 1.84/0.64    inference(avatar_component_clause,[],[f222])).
% 1.84/0.64  fof(f222,plain,(
% 1.84/0.64    spl5_5 <=> ! [X0] : (~r1_tarski(sK1,X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0))),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.84/0.64  fof(f944,plain,(
% 1.84/0.64    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl5_2 | ~spl5_8 | ~spl5_11 | ~spl5_13)),
% 1.84/0.64    inference(backward_demodulation,[],[f725,f886])).
% 1.84/0.64  fof(f725,plain,(
% 1.84/0.64    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl5_2 | ~spl5_8 | ~spl5_11)),
% 1.84/0.64    inference(backward_demodulation,[],[f622,f658])).
% 1.84/0.64  fof(f622,plain,(
% 1.84/0.64    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl5_2 | ~spl5_8)),
% 1.84/0.64    inference(forward_demodulation,[],[f170,f350])).
% 1.84/0.64  fof(f68,plain,(
% 1.84/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.84/0.64    inference(cnf_transformation,[],[f6])).
% 1.84/0.64  fof(f6,axiom,(
% 1.84/0.64    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.84/0.64  fof(f912,plain,(
% 1.84/0.64    spl5_12),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f910])).
% 1.84/0.64  fof(f910,plain,(
% 1.84/0.64    $false | spl5_12),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f68,f882,f71])).
% 1.84/0.64  fof(f882,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | spl5_12),
% 1.84/0.64    inference(avatar_component_clause,[],[f880])).
% 1.84/0.64  fof(f880,plain,(
% 1.84/0.64    spl5_12 <=> r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0))),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.84/0.64  fof(f887,plain,(
% 1.84/0.64    ~spl5_12 | spl5_13 | ~spl5_8 | ~spl5_11),
% 1.84/0.64    inference(avatar_split_clause,[],[f749,f656,f348,f884,f880])).
% 1.84/0.64  fof(f749,plain,(
% 1.84/0.64    k1_xboole_0 = k2_funct_1(k1_xboole_0) | ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | (~spl5_8 | ~spl5_11)),
% 1.84/0.64    inference(forward_demodulation,[],[f724,f658])).
% 1.84/0.64  fof(f724,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,k2_funct_1(k1_xboole_0)) | k1_xboole_0 = k2_funct_1(sK2) | (~spl5_8 | ~spl5_11)),
% 1.84/0.64    inference(backward_demodulation,[],[f619,f658])).
% 1.84/0.64  fof(f619,plain,(
% 1.84/0.64    k1_xboole_0 = k2_funct_1(sK2) | ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f618,f80])).
% 1.84/0.64  fof(f80,plain,(
% 1.84/0.64    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.84/0.64    inference(equality_resolution,[],[f50])).
% 1.84/0.64  fof(f50,plain,(
% 1.84/0.64    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f5])).
% 1.84/0.64  fof(f5,axiom,(
% 1.84/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.84/0.64  fof(f618,plain,(
% 1.84/0.64    k2_funct_1(sK2) = k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)) | ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f617,f350])).
% 1.84/0.64  fof(f617,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f597,f80])).
% 1.84/0.64  fof(f597,plain,(
% 1.84/0.64    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2)) | ~spl5_8),
% 1.84/0.64    inference(backward_demodulation,[],[f270,f350])).
% 1.84/0.64  fof(f270,plain,(
% 1.84/0.64    ~r1_tarski(k2_zfmisc_1(sK1,k1_relat_1(sK2)),k2_funct_1(sK2)) | k2_funct_1(sK2) = k2_zfmisc_1(sK1,k1_relat_1(sK2))),
% 1.84/0.64    inference(resolution,[],[f264,f54])).
% 1.84/0.64  fof(f54,plain,(
% 1.84/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.84/0.64    inference(cnf_transformation,[],[f4])).
% 1.84/0.64  fof(f4,axiom,(
% 1.84/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.84/0.64  fof(f264,plain,(
% 1.84/0.64    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2)))),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f131,f71])).
% 1.84/0.64  fof(f131,plain,(
% 1.84/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))),
% 1.84/0.64    inference(forward_demodulation,[],[f130,f119])).
% 1.84/0.64  fof(f130,plain,(
% 1.84/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2))))),
% 1.84/0.64    inference(forward_demodulation,[],[f127,f104])).
% 1.84/0.64  fof(f127,plain,(
% 1.84/0.64    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k2_relat_1(k2_funct_1(sK2)))))),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f105,f106,f66])).
% 1.84/0.64  fof(f66,plain,(
% 1.84/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f33])).
% 1.84/0.64  % (23167)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.84/0.64  fof(f665,plain,(
% 1.84/0.64    spl5_10),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f663])).
% 1.84/0.64  fof(f663,plain,(
% 1.84/0.64    $false | spl5_10),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f68,f654,f71])).
% 1.84/0.64  fof(f654,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,sK2) | spl5_10),
% 1.84/0.64    inference(avatar_component_clause,[],[f652])).
% 1.84/0.64  fof(f652,plain,(
% 1.84/0.64    spl5_10 <=> r1_tarski(k1_xboole_0,sK2)),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.84/0.64  fof(f659,plain,(
% 1.84/0.64    ~spl5_10 | spl5_11 | ~spl5_8),
% 1.84/0.64    inference(avatar_split_clause,[],[f611,f348,f656,f652])).
% 1.84/0.64  fof(f611,plain,(
% 1.84/0.64    k1_xboole_0 = sK2 | ~r1_tarski(k1_xboole_0,sK2) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f610,f79])).
% 1.84/0.64  fof(f79,plain,(
% 1.84/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.84/0.64    inference(equality_resolution,[],[f51])).
% 1.84/0.64  fof(f51,plain,(
% 1.84/0.64    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f5])).
% 1.84/0.64  fof(f610,plain,(
% 1.84/0.64    sK2 = k2_zfmisc_1(sK0,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK2) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f609,f350])).
% 1.84/0.64  fof(f609,plain,(
% 1.84/0.64    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_8),
% 1.84/0.64    inference(forward_demodulation,[],[f587,f79])).
% 1.84/0.64  fof(f587,plain,(
% 1.84/0.64    ~r1_tarski(k2_zfmisc_1(sK0,k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(sK0,sK1) | ~spl5_8),
% 1.84/0.64    inference(backward_demodulation,[],[f161,f350])).
% 1.84/0.64  fof(f161,plain,(
% 1.84/0.64    ~r1_tarski(k2_zfmisc_1(sK0,sK1),sK2) | sK2 = k2_zfmisc_1(sK0,sK1)),
% 1.84/0.64    inference(resolution,[],[f96,f54])).
% 1.84/0.64  fof(f96,plain,(
% 1.84/0.64    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f42,f71])).
% 1.84/0.64  fof(f572,plain,(
% 1.84/0.64    spl5_1 | ~spl5_9),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f567])).
% 1.84/0.64  fof(f567,plain,(
% 1.84/0.64    $false | (spl5_1 | ~spl5_9)),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f166,f467,f70])).
% 1.84/0.64  fof(f70,plain,(
% 1.84/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f7])).
% 1.84/0.64  fof(f467,plain,(
% 1.84/0.64    r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) | ~spl5_9),
% 1.84/0.64    inference(backward_demodulation,[],[f264,f354])).
% 1.84/0.64  fof(f166,plain,(
% 1.84/0.64    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_1),
% 1.84/0.64    inference(avatar_component_clause,[],[f164])).
% 1.84/0.64  fof(f164,plain,(
% 1.84/0.64    spl5_1 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.84/0.64  fof(f452,plain,(
% 1.84/0.64    spl5_1 | ~spl5_8),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f447])).
% 1.84/0.64  fof(f447,plain,(
% 1.84/0.64    $false | (spl5_1 | ~spl5_8)),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f69,f68,f398,f75])).
% 1.84/0.64  fof(f75,plain,(
% 1.84/0.64    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f36])).
% 1.84/0.64  fof(f36,plain,(
% 1.84/0.64    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 1.84/0.64    inference(ennf_transformation,[],[f12])).
% 1.84/0.64  fof(f12,axiom,(
% 1.84/0.64    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 1.84/0.64  fof(f398,plain,(
% 1.84/0.64    ~v1_xboole_0(k1_xboole_0) | (spl5_1 | ~spl5_8)),
% 1.84/0.64    inference(backward_demodulation,[],[f294,f350])).
% 1.84/0.64  fof(f294,plain,(
% 1.84/0.64    ~v1_xboole_0(sK1) | spl5_1),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f131,f288,f75])).
% 1.84/0.64  fof(f288,plain,(
% 1.84/0.64    ~v1_xboole_0(k2_funct_1(sK2)) | spl5_1),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f202,f77])).
% 1.84/0.64  fof(f77,plain,(
% 1.84/0.64    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f1])).
% 1.84/0.64  fof(f1,axiom,(
% 1.84/0.64    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.84/0.64  fof(f202,plain,(
% 1.84/0.64    r2_hidden(sK3(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)),k2_funct_1(sK2)) | spl5_1),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f195,f73])).
% 1.84/0.64  fof(f73,plain,(
% 1.84/0.64    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f35])).
% 1.84/0.64  fof(f35,plain,(
% 1.84/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.84/0.64    inference(ennf_transformation,[],[f2])).
% 1.84/0.64  fof(f2,axiom,(
% 1.84/0.64    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.84/0.64  fof(f195,plain,(
% 1.84/0.64    ~r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) | spl5_1),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f166,f70])).
% 1.84/0.64  fof(f69,plain,(
% 1.84/0.64    v1_xboole_0(k1_xboole_0)),
% 1.84/0.64    inference(cnf_transformation,[],[f3])).
% 1.84/0.64  fof(f3,axiom,(
% 1.84/0.64    v1_xboole_0(k1_xboole_0)),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.84/0.64  fof(f365,plain,(
% 1.84/0.64    spl5_7),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f358])).
% 1.84/0.64  fof(f358,plain,(
% 1.84/0.64    $false | spl5_7),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f96,f346,f70])).
% 1.84/0.64  fof(f346,plain,(
% 1.84/0.64    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl5_7),
% 1.84/0.64    inference(avatar_component_clause,[],[f344])).
% 1.84/0.64  fof(f344,plain,(
% 1.84/0.64    spl5_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.84/0.64  fof(f355,plain,(
% 1.84/0.64    ~spl5_7 | spl5_8 | spl5_9),
% 1.84/0.64    inference(avatar_split_clause,[],[f102,f352,f348,f344])).
% 1.84/0.64  fof(f102,plain,(
% 1.84/0.64    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/0.64    inference(backward_demodulation,[],[f92,f93])).
% 1.84/0.64  fof(f93,plain,(
% 1.84/0.64    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f42,f67])).
% 1.84/0.64  fof(f67,plain,(
% 1.84/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f34])).
% 1.84/0.64  fof(f34,plain,(
% 1.84/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.64    inference(ennf_transformation,[],[f13])).
% 1.84/0.64  fof(f13,axiom,(
% 1.84/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.84/0.64  fof(f92,plain,(
% 1.84/0.64    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/0.64    inference(resolution,[],[f41,f62])).
% 1.84/0.64  fof(f62,plain,(
% 1.84/0.64    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.64    inference(cnf_transformation,[],[f29])).
% 1.84/0.64  fof(f29,plain,(
% 1.84/0.64    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.64    inference(flattening,[],[f28])).
% 1.84/0.64  fof(f28,plain,(
% 1.84/0.64    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.64    inference(ennf_transformation,[],[f15])).
% 1.84/0.64  fof(f15,axiom,(
% 1.84/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.84/0.64  fof(f41,plain,(
% 1.84/0.64    v1_funct_2(sK2,sK0,sK1)),
% 1.84/0.64    inference(cnf_transformation,[],[f21])).
% 1.84/0.64  fof(f232,plain,(
% 1.84/0.64    spl5_4),
% 1.84/0.64    inference(avatar_contradiction_clause,[],[f227])).
% 1.84/0.64  fof(f227,plain,(
% 1.84/0.64    $false | spl5_4),
% 1.84/0.64    inference(unit_resulting_resolution,[],[f42,f220,f56])).
% 1.84/0.64  fof(f220,plain,(
% 1.84/0.64    ~v1_relat_1(sK2) | spl5_4),
% 1.84/0.64    inference(avatar_component_clause,[],[f218])).
% 1.84/0.64  fof(f218,plain,(
% 1.84/0.64    spl5_4 <=> v1_relat_1(sK2)),
% 1.84/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.84/0.64  fof(f224,plain,(
% 1.84/0.64    ~spl5_4 | spl5_5),
% 1.84/0.64    inference(avatar_split_clause,[],[f101,f222,f218])).
% 1.84/0.64  fof(f101,plain,(
% 1.84/0.64    ( ! [X0] : (~r1_tarski(sK1,X0) | ~v1_relat_1(sK2) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 1.84/0.64    inference(backward_demodulation,[],[f88,f98])).
% 1.84/0.64  % (23185)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.84/0.64  fof(f88,plain,(
% 1.84/0.64    ( ! [X0] : (~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),X0) | v1_funct_2(sK2,k1_relat_1(sK2),X0)) )),
% 1.84/0.64    inference(resolution,[],[f40,f63])).
% 1.84/0.64  fof(f63,plain,(
% 1.84/0.64    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | v1_funct_2(X1,k1_relat_1(X1),X0)) )),
% 1.84/0.64    inference(cnf_transformation,[],[f31])).
% 1.84/0.64  % (23175)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.84/0.64  fof(f31,plain,(
% 1.84/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.84/0.64    inference(flattening,[],[f30])).
% 1.84/0.64  fof(f30,plain,(
% 1.84/0.64    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.84/0.64    inference(ennf_transformation,[],[f17])).
% 1.84/0.64  fof(f17,axiom,(
% 1.84/0.64    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 1.84/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).
% 1.84/0.64  fof(f175,plain,(
% 1.84/0.64    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 1.84/0.64    inference(avatar_split_clause,[],[f39,f172,f168,f164])).
% 1.84/0.64  fof(f39,plain,(
% 1.84/0.64    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.84/0.64    inference(cnf_transformation,[],[f21])).
% 1.84/0.64  % SZS output end Proof for theBenchmark
% 1.84/0.64  % (23162)------------------------------
% 1.84/0.64  % (23162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.64  % (23162)Termination reason: Refutation
% 1.84/0.64  
% 1.84/0.64  % (23162)Memory used [KB]: 6524
% 1.84/0.64  % (23162)Time elapsed: 0.193 s
% 1.84/0.64  % (23162)------------------------------
% 1.84/0.64  % (23162)------------------------------
% 2.17/0.65  % (23157)Success in time 0.277 s
%------------------------------------------------------------------------------
