%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:06 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 330 expanded)
%              Number of leaves         :   42 ( 147 expanded)
%              Depth                    :    8
%              Number of atoms          :  509 (1206 expanded)
%              Number of equality atoms :  141 ( 354 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1072,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f117,f122,f142,f147,f269,f336,f338,f358,f409,f430,f483,f505,f519,f669,f704,f818,f819,f828,f882,f884,f885,f956,f1034,f1043,f1050,f1052,f1054,f1071])).

fof(f1071,plain,
    ( k1_xboole_0 != sK1
    | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1054,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != sK3
    | sK2 = sK3 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1052,plain,
    ( k1_xboole_0 != sK1
    | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | k1_xboole_0 != sK0
    | sK0 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1050,plain,
    ( ~ spl8_35
    | spl8_113
    | ~ spl8_111 ),
    inference(avatar_split_clause,[],[f1044,f1031,f1047,f366])).

fof(f366,plain,
    ( spl8_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f1047,plain,
    ( spl8_113
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).

fof(f1031,plain,
    ( spl8_111
  <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).

fof(f1044,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_111 ),
    inference(resolution,[],[f1033,f297])).

fof(f297,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f81,f80])).

fof(f80,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f1033,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_111 ),
    inference(avatar_component_clause,[],[f1031])).

fof(f1043,plain,
    ( ~ spl8_32
    | spl8_112
    | ~ spl8_102 ),
    inference(avatar_split_clause,[],[f1037,f953,f1040,f350])).

fof(f350,plain,
    ( spl8_32
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f1040,plain,
    ( spl8_112
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).

fof(f953,plain,
    ( spl8_102
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).

fof(f1037,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_102 ),
    inference(resolution,[],[f955,f297])).

fof(f955,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_102 ),
    inference(avatar_component_clause,[],[f953])).

fof(f1034,plain,
    ( spl8_111
    | ~ spl8_36
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f1029,f406,f371,f1031])).

fof(f371,plain,
    ( spl8_36
  <=> v1_funct_2(sK3,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f406,plain,
    ( spl8_42
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f1029,plain,
    ( v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)
    | ~ spl8_36
    | ~ spl8_42 ),
    inference(forward_demodulation,[],[f373,f408])).

fof(f408,plain,
    ( k1_xboole_0 = sK0
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f406])).

fof(f373,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_36 ),
    inference(avatar_component_clause,[],[f371])).

fof(f956,plain,
    ( spl8_102
    | ~ spl8_33
    | ~ spl8_42 ),
    inference(avatar_split_clause,[],[f923,f406,f355,f953])).

fof(f355,plain,
    ( spl8_33
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f923,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl8_33
    | ~ spl8_42 ),
    inference(backward_demodulation,[],[f357,f408])).

fof(f357,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f355])).

fof(f885,plain,
    ( spl8_36
    | ~ spl8_6
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f858,f333,f114,f371])).

fof(f114,plain,
    ( spl8_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f333,plain,
    ( spl8_31
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f858,plain,
    ( v1_funct_2(sK3,sK0,k1_xboole_0)
    | ~ spl8_6
    | ~ spl8_31 ),
    inference(backward_demodulation,[],[f116,f335])).

fof(f335,plain,
    ( k1_xboole_0 = sK1
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f333])).

fof(f116,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f114])).

fof(f884,plain,
    ( spl8_35
    | ~ spl8_5
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f883,f333,f109,f366])).

fof(f109,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f883,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_5
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f857,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f857,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_31 ),
    inference(backward_demodulation,[],[f111,f335])).

fof(f111,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f882,plain,
    ( spl8_32
    | ~ spl8_1
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f881,f333,f89,f350])).

fof(f89,plain,
    ( spl8_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f881,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_1
    | ~ spl8_31 ),
    inference(forward_demodulation,[],[f854,f79])).

fof(f854,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl8_1
    | ~ spl8_31 ),
    inference(backward_demodulation,[],[f91,f335])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f828,plain,
    ( spl8_27
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f469,f109,f271])).

fof(f271,plain,
    ( spl8_27
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f469,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f111,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f819,plain,
    ( ~ spl8_21
    | ~ spl8_10
    | spl8_67
    | spl8_64
    | ~ spl8_7
    | ~ spl8_51 ),
    inference(avatar_split_clause,[],[f661,f503,f119,f641,f665,f144,f229])).

fof(f229,plain,
    ( spl8_21
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f144,plain,
    ( spl8_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f665,plain,
    ( spl8_67
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f641,plain,
    ( spl8_64
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).

fof(f119,plain,
    ( spl8_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f503,plain,
    ( spl8_51
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f661,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3)
    | ~ spl8_7
    | ~ spl8_51 ),
    inference(resolution,[],[f504,f121])).

fof(f121,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f504,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f503])).

fof(f818,plain,
    ( ~ spl8_10
    | ~ spl8_21
    | ~ spl8_71
    | spl8_64
    | ~ spl8_7
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f808,f517,f119,f641,f701,f229,f144])).

fof(f701,plain,
    ( spl8_71
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f517,plain,
    ( spl8_53
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f808,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_7
    | ~ spl8_53 ),
    inference(resolution,[],[f518,f121])).

fof(f518,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f517])).

fof(f704,plain,
    ( spl8_71
    | ~ spl8_67 ),
    inference(avatar_split_clause,[],[f697,f665,f701])).

fof(f697,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl8_67 ),
    inference(resolution,[],[f667,f38])).

fof(f38,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
                  ( r2_hidden(X4,X0)
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
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).

fof(f667,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f665])).

fof(f669,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f519,plain,
    ( ~ spl8_9
    | spl8_53
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f515,f208,f99,f517,f139])).

fof(f139,plain,
    ( spl8_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f99,plain,
    ( spl8_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f208,plain,
    ( spl8_18
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f515,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f513,f210])).

fof(f210,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f208])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl8_3 ),
    inference(resolution,[],[f49,f101])).

fof(f101,plain,
    ( v1_funct_1(sK2)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f99])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ? [X2] :
              ( k1_funct_1(X0,X2) != k1_funct_1(X1,X2)
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k1_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2] :
                  ( r2_hidden(X2,k1_relat_1(X0))
                 => k1_funct_1(X0,X2) = k1_funct_1(X1,X2) )
              & k1_relat_1(X1) = k1_relat_1(X0) )
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f505,plain,
    ( ~ spl8_9
    | spl8_51
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f501,f208,f99,f503,f139])).

fof(f501,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | sK2 = X0 )
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f500,f210])).

fof(f500,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl8_3
    | ~ spl8_18 ),
    inference(forward_demodulation,[],[f498,f210])).

fof(f498,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl8_3 ),
    inference(resolution,[],[f48,f101])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f483,plain,
    ( spl8_25
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f475,f109,f253])).

fof(f253,plain,
    ( spl8_25
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).

fof(f475,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f111,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f430,plain,
    ( ~ spl8_35
    | spl8_45
    | spl8_42
    | ~ spl8_36 ),
    inference(avatar_split_clause,[],[f425,f371,f406,f427,f366])).

fof(f427,plain,
    ( spl8_45
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f425,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_36 ),
    inference(resolution,[],[f373,f313])).

fof(f313,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(forward_demodulation,[],[f83,f79])).

fof(f83,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f409,plain,
    ( ~ spl8_32
    | spl8_41
    | spl8_42
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f400,f355,f406,f402,f350])).

fof(f402,plain,
    ( spl8_41
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).

fof(f400,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_33 ),
    inference(resolution,[],[f357,f313])).

fof(f358,plain,
    ( spl8_33
    | ~ spl8_2
    | ~ spl8_31 ),
    inference(avatar_split_clause,[],[f340,f333,f94,f355])).

fof(f94,plain,
    ( spl8_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f340,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl8_2
    | ~ spl8_31 ),
    inference(backward_demodulation,[],[f96,f335])).

fof(f96,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f338,plain,
    ( ~ spl8_6
    | spl8_31
    | spl8_21
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(avatar_split_clause,[],[f337,f271,f109,f229,f333,f114])).

fof(f337,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_5
    | ~ spl8_27 ),
    inference(forward_demodulation,[],[f327,f273])).

fof(f273,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f271])).

fof(f327,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl8_5 ),
    inference(resolution,[],[f70,f111])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f336,plain,
    ( ~ spl8_2
    | spl8_31
    | spl8_18
    | ~ spl8_1
    | ~ spl8_26 ),
    inference(avatar_split_clause,[],[f331,f266,f89,f208,f333,f94])).

fof(f266,plain,
    ( spl8_26
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f331,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_1
    | ~ spl8_26 ),
    inference(forward_demodulation,[],[f326,f268])).

fof(f268,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_26 ),
    inference(avatar_component_clause,[],[f266])).

fof(f326,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl8_1 ),
    inference(resolution,[],[f70,f91])).

fof(f269,plain,
    ( spl8_26
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f261,f89,f266])).

fof(f261,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f63,f91])).

fof(f147,plain,
    ( spl8_10
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f130,f109,f144])).

fof(f130,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f62,f111])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f142,plain,
    ( spl8_9
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f129,f89,f139])).

fof(f129,plain,
    ( v1_relat_1(sK2)
    | ~ spl8_1 ),
    inference(resolution,[],[f62,f91])).

fof(f122,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f39,f119])).

fof(f39,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f117,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f40,f114])).

fof(f40,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f41,f109])).

fof(f41,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f107,plain,(
    ~ spl8_4 ),
    inference(avatar_split_clause,[],[f42,f104])).

fof(f104,plain,
    ( spl8_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f42,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f102,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f43,f99])).

fof(f43,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f44,f94])).

fof(f44,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f45,f89])).

fof(f45,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:02:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (24205)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (24206)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (24217)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (24212)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (24221)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (24214)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (24224)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (24207)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (24207)Refutation not found, incomplete strategy% (24207)------------------------------
% 0.20/0.54  % (24207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24207)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24207)Memory used [KB]: 10874
% 0.20/0.54  % (24207)Time elapsed: 0.126 s
% 0.20/0.54  % (24207)------------------------------
% 0.20/0.54  % (24207)------------------------------
% 0.20/0.54  % (24234)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (24214)Refutation not found, incomplete strategy% (24214)------------------------------
% 0.20/0.54  % (24214)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (24214)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (24214)Memory used [KB]: 10746
% 0.20/0.54  % (24214)Time elapsed: 0.127 s
% 0.20/0.54  % (24214)------------------------------
% 0.20/0.54  % (24214)------------------------------
% 0.20/0.54  % (24229)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (24213)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (24226)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (24232)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (24218)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (24235)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (24215)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (24209)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (24216)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (24210)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (24211)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (24228)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.56  % (24216)Refutation not found, incomplete strategy% (24216)------------------------------
% 0.20/0.56  % (24216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (24227)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (24222)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.56  % (24216)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (24216)Memory used [KB]: 10746
% 0.20/0.56  % (24216)Time elapsed: 0.139 s
% 0.20/0.56  % (24216)------------------------------
% 0.20/0.56  % (24216)------------------------------
% 0.20/0.56  % (24223)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.57  % (24225)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (24230)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (24233)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.58  % (24220)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.58  % (24231)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.75/0.59  % (24228)Refutation not found, incomplete strategy% (24228)------------------------------
% 1.75/0.59  % (24228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.59  % (24228)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.59  
% 1.75/0.59  % (24228)Memory used [KB]: 11001
% 1.75/0.59  % (24228)Time elapsed: 0.144 s
% 1.75/0.59  % (24228)------------------------------
% 1.75/0.59  % (24228)------------------------------
% 1.75/0.59  % (24219)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.75/0.59  % (24222)Refutation found. Thanks to Tanya!
% 1.75/0.59  % SZS status Theorem for theBenchmark
% 1.75/0.59  % SZS output start Proof for theBenchmark
% 1.75/0.59  fof(f1072,plain,(
% 1.75/0.59    $false),
% 1.75/0.59    inference(avatar_sat_refutation,[],[f92,f97,f102,f107,f112,f117,f122,f142,f147,f269,f336,f338,f358,f409,f430,f483,f505,f519,f669,f704,f818,f819,f828,f882,f884,f885,f956,f1034,f1043,f1050,f1052,f1054,f1071])).
% 1.75/0.59  fof(f1071,plain,(
% 1.75/0.59    k1_xboole_0 != sK1 | k1_relat_1(sK2) != k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK2)),
% 1.75/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.75/0.59  fof(f1054,plain,(
% 1.75/0.59    k1_xboole_0 != sK2 | k1_xboole_0 != sK3 | sK2 = sK3),
% 1.75/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.75/0.59  fof(f1052,plain,(
% 1.75/0.59    k1_xboole_0 != sK1 | k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | k1_xboole_0 != sK0 | sK0 = k1_relat_1(sK3)),
% 1.75/0.59    introduced(theory_tautology_sat_conflict,[])).
% 1.75/0.59  fof(f1050,plain,(
% 1.75/0.59    ~spl8_35 | spl8_113 | ~spl8_111),
% 1.75/0.59    inference(avatar_split_clause,[],[f1044,f1031,f1047,f366])).
% 1.75/0.59  fof(f366,plain,(
% 1.75/0.59    spl8_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 1.75/0.59  fof(f1047,plain,(
% 1.75/0.59    spl8_113 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_113])])).
% 1.75/0.59  fof(f1031,plain,(
% 1.75/0.59    spl8_111 <=> v1_funct_2(sK3,k1_xboole_0,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_111])])).
% 1.75/0.59  fof(f1044,plain,(
% 1.75/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_111),
% 1.75/0.59    inference(resolution,[],[f1033,f297])).
% 1.75/0.59  fof(f297,plain,(
% 1.75/0.59    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.75/0.59    inference(forward_demodulation,[],[f81,f80])).
% 1.75/0.59  fof(f80,plain,(
% 1.75/0.59    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.75/0.59    inference(equality_resolution,[],[f59])).
% 1.75/0.59  fof(f59,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f5])).
% 1.75/0.59  fof(f5,axiom,(
% 1.75/0.59    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.75/0.59  fof(f81,plain,(
% 1.75/0.59    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 1.75/0.59    inference(equality_resolution,[],[f68])).
% 1.75/0.59  fof(f68,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f31])).
% 1.75/0.59  fof(f31,plain,(
% 1.75/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.59    inference(flattening,[],[f30])).
% 1.75/0.59  fof(f30,plain,(
% 1.75/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.59    inference(ennf_transformation,[],[f16])).
% 1.75/0.59  fof(f16,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.75/0.59  fof(f1033,plain,(
% 1.75/0.59    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | ~spl8_111),
% 1.75/0.59    inference(avatar_component_clause,[],[f1031])).
% 1.75/0.59  fof(f1043,plain,(
% 1.75/0.59    ~spl8_32 | spl8_112 | ~spl8_102),
% 1.75/0.59    inference(avatar_split_clause,[],[f1037,f953,f1040,f350])).
% 1.75/0.59  fof(f350,plain,(
% 1.75/0.59    spl8_32 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 1.75/0.59  fof(f1040,plain,(
% 1.75/0.59    spl8_112 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_112])])).
% 1.75/0.59  fof(f953,plain,(
% 1.75/0.59    spl8_102 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_102])])).
% 1.75/0.59  fof(f1037,plain,(
% 1.75/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl8_102),
% 1.75/0.59    inference(resolution,[],[f955,f297])).
% 1.75/0.59  fof(f955,plain,(
% 1.75/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl8_102),
% 1.75/0.59    inference(avatar_component_clause,[],[f953])).
% 1.75/0.59  fof(f1034,plain,(
% 1.75/0.59    spl8_111 | ~spl8_36 | ~spl8_42),
% 1.75/0.59    inference(avatar_split_clause,[],[f1029,f406,f371,f1031])).
% 1.75/0.59  fof(f371,plain,(
% 1.75/0.59    spl8_36 <=> v1_funct_2(sK3,sK0,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 1.75/0.59  fof(f406,plain,(
% 1.75/0.59    spl8_42 <=> k1_xboole_0 = sK0),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 1.75/0.59  fof(f1029,plain,(
% 1.75/0.59    v1_funct_2(sK3,k1_xboole_0,k1_xboole_0) | (~spl8_36 | ~spl8_42)),
% 1.75/0.59    inference(forward_demodulation,[],[f373,f408])).
% 1.75/0.59  fof(f408,plain,(
% 1.75/0.59    k1_xboole_0 = sK0 | ~spl8_42),
% 1.75/0.59    inference(avatar_component_clause,[],[f406])).
% 1.75/0.59  fof(f373,plain,(
% 1.75/0.59    v1_funct_2(sK3,sK0,k1_xboole_0) | ~spl8_36),
% 1.75/0.59    inference(avatar_component_clause,[],[f371])).
% 1.75/0.59  fof(f956,plain,(
% 1.75/0.59    spl8_102 | ~spl8_33 | ~spl8_42),
% 1.75/0.59    inference(avatar_split_clause,[],[f923,f406,f355,f953])).
% 1.75/0.59  fof(f355,plain,(
% 1.75/0.59    spl8_33 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 1.75/0.59  fof(f923,plain,(
% 1.75/0.59    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl8_33 | ~spl8_42)),
% 1.75/0.59    inference(backward_demodulation,[],[f357,f408])).
% 1.75/0.59  fof(f357,plain,(
% 1.75/0.59    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl8_33),
% 1.75/0.59    inference(avatar_component_clause,[],[f355])).
% 1.75/0.59  fof(f885,plain,(
% 1.75/0.59    spl8_36 | ~spl8_6 | ~spl8_31),
% 1.75/0.59    inference(avatar_split_clause,[],[f858,f333,f114,f371])).
% 1.75/0.59  fof(f114,plain,(
% 1.75/0.59    spl8_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 1.75/0.59  fof(f333,plain,(
% 1.75/0.59    spl8_31 <=> k1_xboole_0 = sK1),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 1.75/0.59  fof(f858,plain,(
% 1.75/0.59    v1_funct_2(sK3,sK0,k1_xboole_0) | (~spl8_6 | ~spl8_31)),
% 1.75/0.59    inference(backward_demodulation,[],[f116,f335])).
% 1.75/0.59  fof(f335,plain,(
% 1.75/0.59    k1_xboole_0 = sK1 | ~spl8_31),
% 1.75/0.59    inference(avatar_component_clause,[],[f333])).
% 1.75/0.59  fof(f116,plain,(
% 1.75/0.59    v1_funct_2(sK3,sK0,sK1) | ~spl8_6),
% 1.75/0.59    inference(avatar_component_clause,[],[f114])).
% 1.75/0.59  fof(f884,plain,(
% 1.75/0.59    spl8_35 | ~spl8_5 | ~spl8_31),
% 1.75/0.59    inference(avatar_split_clause,[],[f883,f333,f109,f366])).
% 1.75/0.59  fof(f109,plain,(
% 1.75/0.59    spl8_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 1.75/0.59  fof(f883,plain,(
% 1.75/0.59    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_5 | ~spl8_31)),
% 1.75/0.59    inference(forward_demodulation,[],[f857,f79])).
% 1.75/0.59  fof(f79,plain,(
% 1.75/0.59    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.75/0.59    inference(equality_resolution,[],[f60])).
% 1.75/0.59  fof(f60,plain,(
% 1.75/0.59    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f5])).
% 1.75/0.59  fof(f857,plain,(
% 1.75/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_5 | ~spl8_31)),
% 1.75/0.59    inference(backward_demodulation,[],[f111,f335])).
% 1.75/0.59  fof(f111,plain,(
% 1.75/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_5),
% 1.75/0.59    inference(avatar_component_clause,[],[f109])).
% 1.75/0.59  fof(f882,plain,(
% 1.75/0.59    spl8_32 | ~spl8_1 | ~spl8_31),
% 1.75/0.59    inference(avatar_split_clause,[],[f881,f333,f89,f350])).
% 1.75/0.59  fof(f89,plain,(
% 1.75/0.59    spl8_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.75/0.59  fof(f881,plain,(
% 1.75/0.59    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl8_1 | ~spl8_31)),
% 1.75/0.59    inference(forward_demodulation,[],[f854,f79])).
% 1.75/0.59  fof(f854,plain,(
% 1.75/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl8_1 | ~spl8_31)),
% 1.75/0.59    inference(backward_demodulation,[],[f91,f335])).
% 1.75/0.59  fof(f91,plain,(
% 1.75/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_1),
% 1.75/0.59    inference(avatar_component_clause,[],[f89])).
% 1.75/0.59  fof(f828,plain,(
% 1.75/0.59    spl8_27 | ~spl8_5),
% 1.75/0.59    inference(avatar_split_clause,[],[f469,f109,f271])).
% 1.75/0.59  fof(f271,plain,(
% 1.75/0.59    spl8_27 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 1.75/0.59  fof(f469,plain,(
% 1.75/0.59    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_5),
% 1.75/0.59    inference(resolution,[],[f111,f63])).
% 1.75/0.59  fof(f63,plain,(
% 1.75/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f28])).
% 1.75/0.59  fof(f28,plain,(
% 1.75/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.59    inference(ennf_transformation,[],[f13])).
% 1.75/0.59  fof(f13,axiom,(
% 1.75/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.75/0.59  fof(f819,plain,(
% 1.75/0.59    ~spl8_21 | ~spl8_10 | spl8_67 | spl8_64 | ~spl8_7 | ~spl8_51),
% 1.75/0.59    inference(avatar_split_clause,[],[f661,f503,f119,f641,f665,f144,f229])).
% 1.75/0.59  fof(f229,plain,(
% 1.75/0.59    spl8_21 <=> sK0 = k1_relat_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 1.75/0.59  fof(f144,plain,(
% 1.75/0.59    spl8_10 <=> v1_relat_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 1.75/0.59  fof(f665,plain,(
% 1.75/0.59    spl8_67 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 1.75/0.59  fof(f641,plain,(
% 1.75/0.59    spl8_64 <=> sK2 = sK3),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_64])])).
% 1.75/0.59  fof(f119,plain,(
% 1.75/0.59    spl8_7 <=> v1_funct_1(sK3)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 1.75/0.59  fof(f503,plain,(
% 1.75/0.59    spl8_51 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0)),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 1.75/0.59  fof(f661,plain,(
% 1.75/0.59    sK2 = sK3 | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | sK0 != k1_relat_1(sK3) | (~spl8_7 | ~spl8_51)),
% 1.75/0.59    inference(resolution,[],[f504,f121])).
% 1.75/0.59  fof(f121,plain,(
% 1.75/0.59    v1_funct_1(sK3) | ~spl8_7),
% 1.75/0.59    inference(avatar_component_clause,[],[f119])).
% 1.75/0.59  fof(f504,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl8_51),
% 1.75/0.59    inference(avatar_component_clause,[],[f503])).
% 1.75/0.59  fof(f818,plain,(
% 1.75/0.59    ~spl8_10 | ~spl8_21 | ~spl8_71 | spl8_64 | ~spl8_7 | ~spl8_53),
% 1.75/0.59    inference(avatar_split_clause,[],[f808,f517,f119,f641,f701,f229,f144])).
% 1.75/0.59  fof(f701,plain,(
% 1.75/0.59    spl8_71 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).
% 1.75/0.59  fof(f517,plain,(
% 1.75/0.59    spl8_53 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.59    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 1.75/0.59  fof(f808,plain,(
% 1.75/0.59    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl8_7 | ~spl8_53)),
% 1.75/0.59    inference(resolution,[],[f518,f121])).
% 1.75/0.59  fof(f518,plain,(
% 1.75/0.59    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl8_53),
% 1.75/0.59    inference(avatar_component_clause,[],[f517])).
% 1.75/0.59  fof(f704,plain,(
% 1.75/0.59    spl8_71 | ~spl8_67),
% 1.75/0.59    inference(avatar_split_clause,[],[f697,f665,f701])).
% 1.75/0.59  fof(f697,plain,(
% 1.75/0.59    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl8_67),
% 1.75/0.59    inference(resolution,[],[f667,f38])).
% 1.75/0.59  fof(f38,plain,(
% 1.75/0.59    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.75/0.59    inference(cnf_transformation,[],[f21])).
% 1.75/0.59  fof(f21,plain,(
% 1.75/0.59    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.75/0.59    inference(flattening,[],[f20])).
% 1.75/0.59  fof(f20,plain,(
% 1.75/0.59    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.75/0.59    inference(ennf_transformation,[],[f18])).
% 1.75/0.59  fof(f18,negated_conjecture,(
% 1.75/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.75/0.59    inference(negated_conjecture,[],[f17])).
% 1.75/0.59  fof(f17,conjecture,(
% 1.75/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.75/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_2)).
% 1.75/0.59  fof(f667,plain,(
% 1.75/0.59    r2_hidden(sK4(sK2,sK3),sK0) | ~spl8_67),
% 1.75/0.59    inference(avatar_component_clause,[],[f665])).
% 1.75/0.61  fof(f669,plain,(
% 1.75/0.61    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.75/0.61    introduced(theory_tautology_sat_conflict,[])).
% 1.75/0.61  fof(f519,plain,(
% 1.75/0.61    ~spl8_9 | spl8_53 | ~spl8_3 | ~spl8_18),
% 1.75/0.61    inference(avatar_split_clause,[],[f515,f208,f99,f517,f139])).
% 1.75/0.61  fof(f139,plain,(
% 1.75/0.61    spl8_9 <=> v1_relat_1(sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 1.75/0.61  fof(f99,plain,(
% 1.75/0.61    spl8_3 <=> v1_funct_1(sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.75/0.61  fof(f208,plain,(
% 1.75/0.61    spl8_18 <=> sK0 = k1_relat_1(sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 1.75/0.61  fof(f515,plain,(
% 1.75/0.61    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | (~spl8_3 | ~spl8_18)),
% 1.75/0.61    inference(forward_demodulation,[],[f513,f210])).
% 1.75/0.61  fof(f210,plain,(
% 1.75/0.61    sK0 = k1_relat_1(sK2) | ~spl8_18),
% 1.75/0.61    inference(avatar_component_clause,[],[f208])).
% 1.91/0.61  fof(f513,plain,(
% 1.91/0.61    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | ~spl8_3),
% 1.91/0.61    inference(resolution,[],[f49,f101])).
% 1.91/0.61  fof(f101,plain,(
% 1.91/0.61    v1_funct_1(sK2) | ~spl8_3),
% 1.91/0.61    inference(avatar_component_clause,[],[f99])).
% 1.91/0.61  fof(f49,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.91/0.61    inference(cnf_transformation,[],[f23])).
% 1.91/0.61  fof(f23,plain,(
% 1.91/0.61    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.91/0.61    inference(flattening,[],[f22])).
% 1.91/0.61  fof(f22,plain,(
% 1.91/0.61    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k1_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.91/0.61    inference(ennf_transformation,[],[f9])).
% 1.91/0.61  fof(f9,axiom,(
% 1.91/0.61    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X1) = k1_relat_1(X0)) => X0 = X1)))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.91/0.61  fof(f505,plain,(
% 1.91/0.61    ~spl8_9 | spl8_51 | ~spl8_3 | ~spl8_18),
% 1.91/0.61    inference(avatar_split_clause,[],[f501,f208,f99,f503,f139])).
% 1.91/0.61  fof(f501,plain,(
% 1.91/0.61    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | sK2 = X0) ) | (~spl8_3 | ~spl8_18)),
% 1.91/0.61    inference(forward_demodulation,[],[f500,f210])).
% 1.91/0.61  fof(f500,plain,(
% 1.91/0.61    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | (~spl8_3 | ~spl8_18)),
% 1.91/0.61    inference(forward_demodulation,[],[f498,f210])).
% 1.91/0.61  fof(f498,plain,(
% 1.91/0.61    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | ~spl8_3),
% 1.91/0.61    inference(resolution,[],[f48,f101])).
% 1.91/0.61  fof(f48,plain,(
% 1.91/0.61    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(X0) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 1.91/0.61    inference(cnf_transformation,[],[f23])).
% 1.91/0.61  fof(f483,plain,(
% 1.91/0.61    spl8_25 | ~spl8_5),
% 1.91/0.61    inference(avatar_split_clause,[],[f475,f109,f253])).
% 1.91/0.61  fof(f253,plain,(
% 1.91/0.61    spl8_25 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_25])])).
% 1.91/0.61  fof(f475,plain,(
% 1.91/0.61    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl8_5),
% 1.91/0.61    inference(resolution,[],[f111,f87])).
% 1.91/0.61  fof(f87,plain,(
% 1.91/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.91/0.61    inference(duplicate_literal_removal,[],[f86])).
% 1.91/0.61  fof(f86,plain,(
% 1.91/0.61    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.91/0.61    inference(equality_resolution,[],[f75])).
% 1.91/0.61  fof(f75,plain,(
% 1.91/0.61    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f37])).
% 1.91/0.61  fof(f37,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(flattening,[],[f36])).
% 1.91/0.61  fof(f36,plain,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.91/0.61    inference(ennf_transformation,[],[f14])).
% 1.91/0.61  fof(f14,axiom,(
% 1.91/0.61    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.91/0.61  fof(f430,plain,(
% 1.91/0.61    ~spl8_35 | spl8_45 | spl8_42 | ~spl8_36),
% 1.91/0.61    inference(avatar_split_clause,[],[f425,f371,f406,f427,f366])).
% 1.91/0.61  fof(f427,plain,(
% 1.91/0.61    spl8_45 <=> k1_xboole_0 = sK3),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 1.91/0.61  fof(f425,plain,(
% 1.91/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK3 | ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl8_36),
% 1.91/0.61    inference(resolution,[],[f373,f313])).
% 1.91/0.61  fof(f313,plain,(
% 1.91/0.61    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))) )),
% 1.91/0.61    inference(forward_demodulation,[],[f83,f79])).
% 1.91/0.61  fof(f83,plain,(
% 1.91/0.61    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 1.91/0.61    inference(equality_resolution,[],[f66])).
% 1.91/0.61  fof(f66,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f31])).
% 1.91/0.61  fof(f409,plain,(
% 1.91/0.61    ~spl8_32 | spl8_41 | spl8_42 | ~spl8_33),
% 1.91/0.61    inference(avatar_split_clause,[],[f400,f355,f406,f402,f350])).
% 1.91/0.61  fof(f402,plain,(
% 1.91/0.61    spl8_41 <=> k1_xboole_0 = sK2),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_41])])).
% 1.91/0.61  fof(f400,plain,(
% 1.91/0.61    k1_xboole_0 = sK0 | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl8_33),
% 1.91/0.61    inference(resolution,[],[f357,f313])).
% 1.91/0.61  fof(f358,plain,(
% 1.91/0.61    spl8_33 | ~spl8_2 | ~spl8_31),
% 1.91/0.61    inference(avatar_split_clause,[],[f340,f333,f94,f355])).
% 1.91/0.61  fof(f94,plain,(
% 1.91/0.61    spl8_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.91/0.61  fof(f340,plain,(
% 1.91/0.61    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl8_2 | ~spl8_31)),
% 1.91/0.61    inference(backward_demodulation,[],[f96,f335])).
% 1.91/0.61  fof(f96,plain,(
% 1.91/0.61    v1_funct_2(sK2,sK0,sK1) | ~spl8_2),
% 1.91/0.61    inference(avatar_component_clause,[],[f94])).
% 1.91/0.61  fof(f338,plain,(
% 1.91/0.61    ~spl8_6 | spl8_31 | spl8_21 | ~spl8_5 | ~spl8_27),
% 1.91/0.61    inference(avatar_split_clause,[],[f337,f271,f109,f229,f333,f114])).
% 1.91/0.61  fof(f337,plain,(
% 1.91/0.61    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl8_5 | ~spl8_27)),
% 1.91/0.61    inference(forward_demodulation,[],[f327,f273])).
% 1.91/0.61  fof(f273,plain,(
% 1.91/0.61    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl8_27),
% 1.91/0.61    inference(avatar_component_clause,[],[f271])).
% 1.91/0.61  fof(f327,plain,(
% 1.91/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl8_5),
% 1.91/0.61    inference(resolution,[],[f70,f111])).
% 1.91/0.61  fof(f70,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f31])).
% 1.91/0.61  fof(f336,plain,(
% 1.91/0.61    ~spl8_2 | spl8_31 | spl8_18 | ~spl8_1 | ~spl8_26),
% 1.91/0.61    inference(avatar_split_clause,[],[f331,f266,f89,f208,f333,f94])).
% 1.91/0.61  fof(f266,plain,(
% 1.91/0.61    spl8_26 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 1.91/0.61  fof(f331,plain,(
% 1.91/0.61    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | (~spl8_1 | ~spl8_26)),
% 1.91/0.61    inference(forward_demodulation,[],[f326,f268])).
% 1.91/0.61  fof(f268,plain,(
% 1.91/0.61    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl8_26),
% 1.91/0.61    inference(avatar_component_clause,[],[f266])).
% 1.91/0.61  fof(f326,plain,(
% 1.91/0.61    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl8_1),
% 1.91/0.61    inference(resolution,[],[f70,f91])).
% 1.91/0.61  fof(f269,plain,(
% 1.91/0.61    spl8_26 | ~spl8_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f261,f89,f266])).
% 1.91/0.61  fof(f261,plain,(
% 1.91/0.61    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl8_1),
% 1.91/0.61    inference(resolution,[],[f63,f91])).
% 1.91/0.61  fof(f147,plain,(
% 1.91/0.61    spl8_10 | ~spl8_5),
% 1.91/0.61    inference(avatar_split_clause,[],[f130,f109,f144])).
% 1.91/0.61  fof(f130,plain,(
% 1.91/0.61    v1_relat_1(sK3) | ~spl8_5),
% 1.91/0.61    inference(resolution,[],[f62,f111])).
% 1.91/0.61  fof(f62,plain,(
% 1.91/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.91/0.61    inference(cnf_transformation,[],[f27])).
% 1.91/0.61  fof(f27,plain,(
% 1.91/0.61    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/0.61    inference(ennf_transformation,[],[f11])).
% 1.91/0.61  fof(f11,axiom,(
% 1.91/0.61    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.91/0.61  fof(f142,plain,(
% 1.91/0.61    spl8_9 | ~spl8_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f129,f89,f139])).
% 1.91/0.61  fof(f129,plain,(
% 1.91/0.61    v1_relat_1(sK2) | ~spl8_1),
% 1.91/0.61    inference(resolution,[],[f62,f91])).
% 1.91/0.61  fof(f122,plain,(
% 1.91/0.61    spl8_7),
% 1.91/0.61    inference(avatar_split_clause,[],[f39,f119])).
% 1.91/0.61  fof(f39,plain,(
% 1.91/0.61    v1_funct_1(sK3)),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f117,plain,(
% 1.91/0.61    spl8_6),
% 1.91/0.61    inference(avatar_split_clause,[],[f40,f114])).
% 1.91/0.61  fof(f40,plain,(
% 1.91/0.61    v1_funct_2(sK3,sK0,sK1)),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f112,plain,(
% 1.91/0.61    spl8_5),
% 1.91/0.61    inference(avatar_split_clause,[],[f41,f109])).
% 1.91/0.61  fof(f41,plain,(
% 1.91/0.61    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f107,plain,(
% 1.91/0.61    ~spl8_4),
% 1.91/0.61    inference(avatar_split_clause,[],[f42,f104])).
% 1.91/0.61  fof(f104,plain,(
% 1.91/0.61    spl8_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.91/0.61    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.91/0.61  fof(f42,plain,(
% 1.91/0.61    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f102,plain,(
% 1.91/0.61    spl8_3),
% 1.91/0.61    inference(avatar_split_clause,[],[f43,f99])).
% 1.91/0.61  fof(f43,plain,(
% 1.91/0.61    v1_funct_1(sK2)),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f97,plain,(
% 1.91/0.61    spl8_2),
% 1.91/0.61    inference(avatar_split_clause,[],[f44,f94])).
% 1.91/0.61  fof(f44,plain,(
% 1.91/0.61    v1_funct_2(sK2,sK0,sK1)),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  fof(f92,plain,(
% 1.91/0.61    spl8_1),
% 1.91/0.61    inference(avatar_split_clause,[],[f45,f89])).
% 1.91/0.61  fof(f45,plain,(
% 1.91/0.61    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.91/0.61    inference(cnf_transformation,[],[f21])).
% 1.91/0.61  % SZS output end Proof for theBenchmark
% 1.91/0.61  % (24222)------------------------------
% 1.91/0.61  % (24222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.91/0.61  % (24222)Termination reason: Refutation
% 1.91/0.61  
% 1.91/0.61  % (24222)Memory used [KB]: 11385
% 1.91/0.61  % (24222)Time elapsed: 0.154 s
% 1.91/0.61  % (24222)------------------------------
% 1.91/0.61  % (24222)------------------------------
% 1.91/0.61  % (24204)Success in time 0.247 s
%------------------------------------------------------------------------------
