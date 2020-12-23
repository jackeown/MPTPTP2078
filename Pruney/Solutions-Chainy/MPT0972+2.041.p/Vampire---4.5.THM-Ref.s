%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:11 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 309 expanded)
%              Number of leaves         :   43 ( 131 expanded)
%              Depth                    :    8
%              Number of atoms          :  511 (1096 expanded)
%              Number of equality atoms :  118 ( 215 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f150,f155,f158,f207,f212,f288,f293,f390,f396,f434,f557,f570,f577,f677,f706,f826,f893,f1143,f1153,f1155,f1399])).

fof(f1399,plain,
    ( ~ spl7_12
    | spl7_105
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_77
    | ~ spl7_113 ),
    inference(avatar_split_clause,[],[f1398,f1150,f704,f393,f122,f1055,f152])).

fof(f152,plain,
    ( spl7_12
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f1055,plain,
    ( spl7_105
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).

fof(f122,plain,
    ( spl7_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f393,plain,
    ( spl7_42
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f704,plain,
    ( spl7_77
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).

fof(f1150,plain,
    ( spl7_113
  <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).

fof(f1398,plain,
    ( sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_77
    | ~ spl7_113 ),
    inference(trivial_inequality_removal,[],[f1397])).

fof(f1397,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_77
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1396,f395])).

fof(f395,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f393])).

fof(f1396,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_77
    | ~ spl7_113 ),
    inference(trivial_inequality_removal,[],[f1395])).

fof(f1395,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3))
    | sK2 = sK3
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_77
    | ~ spl7_113 ),
    inference(forward_demodulation,[],[f1393,f1152])).

fof(f1152,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_113 ),
    inference(avatar_component_clause,[],[f1150])).

fof(f1393,plain,
    ( sK2 = sK3
    | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3))
    | sK0 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_77 ),
    inference(resolution,[],[f705,f124])).

fof(f124,plain,
    ( v1_funct_1(sK3)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f122])).

fof(f705,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(X0) )
    | ~ spl7_77 ),
    inference(avatar_component_clause,[],[f704])).

fof(f1155,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1153,plain,
    ( spl7_113
    | ~ spl7_112 ),
    inference(avatar_split_clause,[],[f1144,f1140,f1150])).

fof(f1140,plain,
    ( spl7_112
  <=> r2_hidden(sK4(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).

fof(f1144,plain,
    ( k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))
    | ~ spl7_112 ),
    inference(resolution,[],[f1142,f39])).

fof(f39,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK0)
      | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f1142,plain,
    ( r2_hidden(sK4(sK2,sK3),sK0)
    | ~ spl7_112 ),
    inference(avatar_component_clause,[],[f1140])).

fof(f1143,plain,
    ( ~ spl7_12
    | spl7_112
    | spl7_105
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f1138,f432,f393,f122,f1055,f1140,f152])).

fof(f432,plain,
    ( spl7_45
  <=> ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | sK2 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f1138,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_45 ),
    inference(trivial_inequality_removal,[],[f1137])).

fof(f1137,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_42
    | ~ spl7_45 ),
    inference(forward_demodulation,[],[f1135,f395])).

fof(f1135,plain,
    ( sK2 = sK3
    | r2_hidden(sK4(sK2,sK3),sK0)
    | ~ v1_relat_1(sK3)
    | sK0 != k1_relat_1(sK3)
    | ~ spl7_7
    | ~ spl7_45 ),
    inference(resolution,[],[f433,f124])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | sK2 = X0
        | r2_hidden(sK4(sK2,X0),sK0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f432])).

fof(f893,plain,
    ( spl7_27
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f884,f112,f270])).

fof(f270,plain,
    ( spl7_27
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f112,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f884,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f114,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f826,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f706,plain,
    ( ~ spl7_10
    | spl7_77
    | ~ spl7_3
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f702,f387,f102,f704,f143])).

fof(f143,plain,
    ( spl7_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f102,plain,
    ( spl7_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f387,plain,
    ( spl7_41
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f702,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_41 ),
    inference(forward_demodulation,[],[f700,f389])).

fof(f389,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f387])).

fof(f700,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0))
        | sK2 = X0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f51,f104])).

fof(f104,plain,
    ( v1_funct_1(sK2)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f677,plain,
    ( spl7_26
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f672,f92,f265])).

fof(f265,plain,
    ( spl7_26
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f92,plain,
    ( spl7_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f672,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f94,f90])).

fof(f94,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f577,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f570,plain,
    ( spl7_64
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f565,f209,f127,f567])).

fof(f567,plain,
    ( spl7_64
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f127,plain,
    ( spl7_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f209,plain,
    ( spl7_19
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f565,plain,
    ( k1_xboole_0 = sK3
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(resolution,[],[f539,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl7_8 ),
    inference(resolution,[],[f162,f59])).

fof(f59,plain,(
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

fof(f162,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl7_8 ),
    inference(resolution,[],[f156,f129])).

fof(f129,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f127])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f61,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f539,plain,
    ( ! [X0] : r1_tarski(sK3,X0)
    | ~ spl7_19 ),
    inference(resolution,[],[f211,f156])).

fof(f211,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f209])).

fof(f557,plain,
    ( spl7_62
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f552,f200,f127,f554])).

fof(f554,plain,
    ( spl7_62
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).

fof(f200,plain,
    ( spl7_17
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f552,plain,
    ( k1_xboole_0 = sK2
    | ~ spl7_8
    | ~ spl7_17 ),
    inference(resolution,[],[f523,f163])).

fof(f523,plain,
    ( ! [X0] : r1_tarski(sK2,X0)
    | ~ spl7_17 ),
    inference(resolution,[],[f202,f156])).

fof(f202,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f200])).

fof(f434,plain,
    ( ~ spl7_10
    | spl7_45
    | ~ spl7_3
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f430,f387,f102,f432,f143])).

fof(f430,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK2,X0),sK0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_41 ),
    inference(forward_demodulation,[],[f429,f389])).

fof(f429,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl7_3
    | ~ spl7_41 ),
    inference(forward_demodulation,[],[f427,f389])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k1_relat_1(sK2)
        | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2))
        | sK2 = X0 )
    | ~ spl7_3 ),
    inference(resolution,[],[f50,f104])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f396,plain,
    ( ~ spl7_6
    | spl7_40
    | spl7_42
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(avatar_split_clause,[],[f391,f290,f112,f393,f383,f117])).

fof(f117,plain,
    ( spl7_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f383,plain,
    ( spl7_40
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f290,plain,
    ( spl7_29
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f391,plain,
    ( sK0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5
    | ~ spl7_29 ),
    inference(forward_demodulation,[],[f377,f292])).

fof(f292,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_29 ),
    inference(avatar_component_clause,[],[f290])).

fof(f377,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f114])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f390,plain,
    ( ~ spl7_2
    | spl7_40
    | spl7_41
    | ~ spl7_1
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f381,f285,f92,f387,f383,f97])).

fof(f97,plain,
    ( spl7_2
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f285,plain,
    ( spl7_28
  <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f381,plain,
    ( sK0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_1
    | ~ spl7_28 ),
    inference(forward_demodulation,[],[f376,f287])).

fof(f287,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f285])).

fof(f376,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f76,f94])).

fof(f293,plain,
    ( spl7_29
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f281,f112,f290])).

fof(f281,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f69,f114])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f288,plain,
    ( spl7_28
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f280,f92,f285])).

fof(f280,plain,
    ( k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f69,f94])).

fof(f212,plain,
    ( spl7_19
    | ~ spl7_18
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f196,f112,f204,f209])).

fof(f204,plain,
    ( spl7_18
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f196,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f55,f114])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f207,plain,
    ( spl7_17
    | ~ spl7_18
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f195,f92,f204,f200])).

fof(f195,plain,
    ( ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f55,f94])).

fof(f158,plain,(
    spl7_11 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | spl7_11 ),
    inference(resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f149,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl7_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f155,plain,
    ( spl7_12
    | ~ spl7_11
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f141,f112,f147,f152])).

fof(f141,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f49,f114])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f150,plain,
    ( spl7_10
    | ~ spl7_11
    | ~ spl7_1 ),
    inference(avatar_split_clause,[],[f140,f92,f147,f143])).

fof(f140,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2)
    | ~ spl7_1 ),
    inference(resolution,[],[f49,f94])).

fof(f130,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f47,f127])).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f125,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f40,f122])).

fof(f40,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f120,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f41,f117])).

fof(f41,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f115,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f42,f112])).

fof(f42,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f110,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f43,f107])).

fof(f107,plain,
    ( spl7_4
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f43,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f105,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f44,f102])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f100,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f45,f97])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:57:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.52  % (12423)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (12415)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (12427)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (12422)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (12435)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.57  % (12433)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.58  % (12411)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.58  % (12416)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.58  % (12421)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.58  % (12417)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.58  % (12419)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.59  % (12412)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.58/0.59  % (12426)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.59  % (12428)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.59  % (12414)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.60  % (12438)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.58/0.60  % (12429)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.60  % (12434)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.60  % (12437)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.60  % (12413)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.58/0.60  % (12430)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.85/0.60  % (12418)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.85/0.60  % (12424)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.85/0.61  % (12431)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.85/0.61  % (12421)Refutation not found, incomplete strategy% (12421)------------------------------
% 1.85/0.61  % (12421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.61  % (12436)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.85/0.61  % (12420)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.85/0.61  % (12425)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.85/0.61  % (12440)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.85/0.61  % (12432)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.85/0.61  % (12439)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.85/0.61  % (12421)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.61  
% 1.85/0.61  % (12421)Memory used [KB]: 10746
% 1.85/0.62  % (12413)Refutation not found, incomplete strategy% (12413)------------------------------
% 1.85/0.62  % (12413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (12421)Time elapsed: 0.171 s
% 1.85/0.62  % (12421)------------------------------
% 1.85/0.62  % (12421)------------------------------
% 1.85/0.62  % (12413)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.62  
% 1.85/0.62  % (12413)Memory used [KB]: 10874
% 1.85/0.62  % (12413)Time elapsed: 0.175 s
% 1.85/0.62  % (12413)------------------------------
% 1.85/0.62  % (12413)------------------------------
% 1.85/0.62  % (12419)Refutation not found, incomplete strategy% (12419)------------------------------
% 1.85/0.62  % (12419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (12419)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.62  
% 1.85/0.62  % (12419)Memory used [KB]: 10874
% 1.85/0.62  % (12419)Time elapsed: 0.190 s
% 1.85/0.62  % (12419)------------------------------
% 1.85/0.62  % (12419)------------------------------
% 1.85/0.63  % (12433)Refutation not found, incomplete strategy% (12433)------------------------------
% 1.85/0.63  % (12433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.63  % (12433)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.63  
% 1.85/0.63  % (12433)Memory used [KB]: 11001
% 1.85/0.63  % (12433)Time elapsed: 0.201 s
% 1.85/0.63  % (12433)------------------------------
% 1.85/0.63  % (12433)------------------------------
% 1.85/0.64  % (12427)Refutation found. Thanks to Tanya!
% 1.85/0.64  % SZS status Theorem for theBenchmark
% 1.85/0.64  % SZS output start Proof for theBenchmark
% 1.85/0.64  fof(f1400,plain,(
% 1.85/0.64    $false),
% 1.85/0.64    inference(avatar_sat_refutation,[],[f95,f100,f105,f110,f115,f120,f125,f130,f150,f155,f158,f207,f212,f288,f293,f390,f396,f434,f557,f570,f577,f677,f706,f826,f893,f1143,f1153,f1155,f1399])).
% 1.85/0.64  fof(f1399,plain,(
% 1.85/0.64    ~spl7_12 | spl7_105 | ~spl7_7 | ~spl7_42 | ~spl7_77 | ~spl7_113),
% 1.85/0.64    inference(avatar_split_clause,[],[f1398,f1150,f704,f393,f122,f1055,f152])).
% 1.85/0.64  fof(f152,plain,(
% 1.85/0.64    spl7_12 <=> v1_relat_1(sK3)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.85/0.64  fof(f1055,plain,(
% 1.85/0.64    spl7_105 <=> sK2 = sK3),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_105])])).
% 1.85/0.64  fof(f122,plain,(
% 1.85/0.64    spl7_7 <=> v1_funct_1(sK3)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 1.85/0.64  fof(f393,plain,(
% 1.85/0.64    spl7_42 <=> sK0 = k1_relat_1(sK3)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 1.85/0.64  fof(f704,plain,(
% 1.85/0.64    spl7_77 <=> ! [X0] : (k1_relat_1(X0) != sK0 | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_77])])).
% 1.85/0.64  fof(f1150,plain,(
% 1.85/0.64    spl7_113 <=> k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3))),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_113])])).
% 1.85/0.64  fof(f1398,plain,(
% 1.85/0.64    sK2 = sK3 | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_42 | ~spl7_77 | ~spl7_113)),
% 1.85/0.64    inference(trivial_inequality_removal,[],[f1397])).
% 1.85/0.64  fof(f1397,plain,(
% 1.85/0.64    sK0 != sK0 | sK2 = sK3 | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_42 | ~spl7_77 | ~spl7_113)),
% 1.85/0.64    inference(forward_demodulation,[],[f1396,f395])).
% 1.85/0.64  fof(f395,plain,(
% 1.85/0.64    sK0 = k1_relat_1(sK3) | ~spl7_42),
% 1.85/0.64    inference(avatar_component_clause,[],[f393])).
% 1.85/0.64  fof(f1396,plain,(
% 1.85/0.64    sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_77 | ~spl7_113)),
% 1.85/0.64    inference(trivial_inequality_removal,[],[f1395])).
% 1.85/0.64  fof(f1395,plain,(
% 1.85/0.64    k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK2,sK4(sK2,sK3)) | sK2 = sK3 | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_77 | ~spl7_113)),
% 1.85/0.64    inference(forward_demodulation,[],[f1393,f1152])).
% 1.85/0.64  fof(f1152,plain,(
% 1.85/0.64    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_113),
% 1.85/0.64    inference(avatar_component_clause,[],[f1150])).
% 1.85/0.64  fof(f1393,plain,(
% 1.85/0.64    sK2 = sK3 | k1_funct_1(sK2,sK4(sK2,sK3)) != k1_funct_1(sK3,sK4(sK2,sK3)) | sK0 != k1_relat_1(sK3) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_77)),
% 1.85/0.64    inference(resolution,[],[f705,f124])).
% 1.85/0.64  fof(f124,plain,(
% 1.85/0.64    v1_funct_1(sK3) | ~spl7_7),
% 1.85/0.64    inference(avatar_component_clause,[],[f122])).
% 1.85/0.64  fof(f705,plain,(
% 1.85/0.64    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | k1_relat_1(X0) != sK0 | ~v1_relat_1(X0)) ) | ~spl7_77),
% 1.85/0.64    inference(avatar_component_clause,[],[f704])).
% 1.85/0.64  fof(f1155,plain,(
% 1.85/0.64    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.85/0.64    introduced(theory_tautology_sat_conflict,[])).
% 1.85/0.64  fof(f1153,plain,(
% 1.85/0.64    spl7_113 | ~spl7_112),
% 1.85/0.64    inference(avatar_split_clause,[],[f1144,f1140,f1150])).
% 1.85/0.64  fof(f1140,plain,(
% 1.85/0.64    spl7_112 <=> r2_hidden(sK4(sK2,sK3),sK0)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_112])])).
% 1.85/0.64  fof(f1144,plain,(
% 1.85/0.64    k1_funct_1(sK2,sK4(sK2,sK3)) = k1_funct_1(sK3,sK4(sK2,sK3)) | ~spl7_112),
% 1.85/0.64    inference(resolution,[],[f1142,f39])).
% 1.85/0.64  fof(f39,plain,(
% 1.85/0.64    ( ! [X4] : (~r2_hidden(X4,sK0) | k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)) )),
% 1.85/0.64    inference(cnf_transformation,[],[f22])).
% 1.85/0.64  fof(f22,plain,(
% 1.85/0.64    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.85/0.64    inference(flattening,[],[f21])).
% 1.85/0.64  fof(f21,plain,(
% 1.85/0.64    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~r2_hidden(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.85/0.64    inference(ennf_transformation,[],[f19])).
% 1.85/0.64  fof(f19,negated_conjecture,(
% 1.85/0.64    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.85/0.64    inference(negated_conjecture,[],[f18])).
% 1.85/0.64  fof(f18,conjecture,(
% 1.85/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (r2_hidden(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.85/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_funct_2)).
% 1.85/0.64  fof(f1142,plain,(
% 1.85/0.64    r2_hidden(sK4(sK2,sK3),sK0) | ~spl7_112),
% 1.85/0.64    inference(avatar_component_clause,[],[f1140])).
% 1.85/0.64  fof(f1143,plain,(
% 1.85/0.64    ~spl7_12 | spl7_112 | spl7_105 | ~spl7_7 | ~spl7_42 | ~spl7_45),
% 1.85/0.64    inference(avatar_split_clause,[],[f1138,f432,f393,f122,f1055,f1140,f152])).
% 1.85/0.64  fof(f432,plain,(
% 1.85/0.64    spl7_45 <=> ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | sK2 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 1.85/0.64  fof(f1138,plain,(
% 1.85/0.64    sK2 = sK3 | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_42 | ~spl7_45)),
% 1.85/0.64    inference(trivial_inequality_removal,[],[f1137])).
% 1.85/0.64  fof(f1137,plain,(
% 1.85/0.64    sK0 != sK0 | sK2 = sK3 | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | (~spl7_7 | ~spl7_42 | ~spl7_45)),
% 1.85/0.64    inference(forward_demodulation,[],[f1135,f395])).
% 1.85/0.64  fof(f1135,plain,(
% 1.85/0.64    sK2 = sK3 | r2_hidden(sK4(sK2,sK3),sK0) | ~v1_relat_1(sK3) | sK0 != k1_relat_1(sK3) | (~spl7_7 | ~spl7_45)),
% 1.85/0.64    inference(resolution,[],[f433,f124])).
% 1.85/0.64  fof(f433,plain,(
% 1.85/0.64    ( ! [X0] : (~v1_funct_1(X0) | sK2 = X0 | r2_hidden(sK4(sK2,X0),sK0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl7_45),
% 1.85/0.64    inference(avatar_component_clause,[],[f432])).
% 1.85/0.64  fof(f893,plain,(
% 1.85/0.64    spl7_27 | ~spl7_5),
% 1.85/0.64    inference(avatar_split_clause,[],[f884,f112,f270])).
% 1.85/0.64  fof(f270,plain,(
% 1.85/0.64    spl7_27 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.85/0.64  fof(f112,plain,(
% 1.85/0.64    spl7_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.85/0.64  fof(f884,plain,(
% 1.85/0.64    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl7_5),
% 1.85/0.64    inference(resolution,[],[f114,f90])).
% 1.85/0.64  fof(f90,plain,(
% 1.85/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.85/0.64    inference(duplicate_literal_removal,[],[f89])).
% 1.85/0.64  fof(f89,plain,(
% 1.85/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.85/0.64    inference(equality_resolution,[],[f78])).
% 1.85/0.64  fof(f78,plain,(
% 1.85/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.85/0.64    inference(cnf_transformation,[],[f38])).
% 1.85/0.64  fof(f38,plain,(
% 1.85/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.64    inference(flattening,[],[f37])).
% 1.85/0.64  fof(f37,plain,(
% 1.85/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.85/0.64    inference(ennf_transformation,[],[f16])).
% 1.85/0.64  fof(f16,axiom,(
% 1.85/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.85/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.85/0.64  fof(f114,plain,(
% 1.85/0.64    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_5),
% 1.85/0.64    inference(avatar_component_clause,[],[f112])).
% 1.85/0.64  fof(f826,plain,(
% 1.85/0.64    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 1.85/0.64    introduced(theory_tautology_sat_conflict,[])).
% 1.85/0.64  fof(f706,plain,(
% 1.85/0.64    ~spl7_10 | spl7_77 | ~spl7_3 | ~spl7_41),
% 1.85/0.64    inference(avatar_split_clause,[],[f702,f387,f102,f704,f143])).
% 1.85/0.64  fof(f143,plain,(
% 1.85/0.64    spl7_10 <=> v1_relat_1(sK2)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 1.85/0.64  fof(f102,plain,(
% 1.85/0.64    spl7_3 <=> v1_funct_1(sK2)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.85/0.64  fof(f387,plain,(
% 1.85/0.64    spl7_41 <=> sK0 = k1_relat_1(sK2)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).
% 1.85/0.64  fof(f702,plain,(
% 1.85/0.64    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | (~spl7_3 | ~spl7_41)),
% 1.85/0.64    inference(forward_demodulation,[],[f700,f389])).
% 1.85/0.64  fof(f389,plain,(
% 1.85/0.64    sK0 = k1_relat_1(sK2) | ~spl7_41),
% 1.85/0.64    inference(avatar_component_clause,[],[f387])).
% 1.85/0.64  fof(f700,plain,(
% 1.85/0.64    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | k1_funct_1(sK2,sK4(sK2,X0)) != k1_funct_1(X0,sK4(sK2,X0)) | sK2 = X0) ) | ~spl7_3),
% 1.85/0.64    inference(resolution,[],[f51,f104])).
% 1.85/0.64  fof(f104,plain,(
% 1.85/0.64    v1_funct_1(sK2) | ~spl7_3),
% 1.85/0.64    inference(avatar_component_clause,[],[f102])).
% 1.85/0.64  fof(f51,plain,(
% 1.85/0.64    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | X0 = X1) )),
% 1.85/0.64    inference(cnf_transformation,[],[f25])).
% 1.85/0.64  fof(f25,plain,(
% 1.85/0.64    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.64    inference(flattening,[],[f24])).
% 1.85/0.64  fof(f24,plain,(
% 1.85/0.64    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.85/0.64    inference(ennf_transformation,[],[f12])).
% 1.85/0.64  fof(f12,axiom,(
% 1.85/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.85/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_1)).
% 1.85/0.64  fof(f677,plain,(
% 1.85/0.64    spl7_26 | ~spl7_1),
% 1.85/0.64    inference(avatar_split_clause,[],[f672,f92,f265])).
% 1.85/0.64  fof(f265,plain,(
% 1.85/0.64    spl7_26 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 1.85/0.64  fof(f92,plain,(
% 1.85/0.64    spl7_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.85/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 1.85/0.64  fof(f672,plain,(
% 1.85/0.64    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl7_1),
% 1.85/0.64    inference(resolution,[],[f94,f90])).
% 1.85/0.65  fof(f94,plain,(
% 1.85/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl7_1),
% 1.85/0.65    inference(avatar_component_clause,[],[f92])).
% 1.85/0.65  fof(f577,plain,(
% 1.85/0.65    k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.85/0.65    introduced(theory_tautology_sat_conflict,[])).
% 1.85/0.65  fof(f570,plain,(
% 1.85/0.65    spl7_64 | ~spl7_8 | ~spl7_19),
% 1.85/0.65    inference(avatar_split_clause,[],[f565,f209,f127,f567])).
% 1.85/0.65  fof(f567,plain,(
% 1.85/0.65    spl7_64 <=> k1_xboole_0 = sK3),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 1.85/0.65  fof(f127,plain,(
% 1.85/0.65    spl7_8 <=> v1_xboole_0(k1_xboole_0)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.85/0.65  fof(f209,plain,(
% 1.85/0.65    spl7_19 <=> v1_xboole_0(sK3)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 1.85/0.65  fof(f565,plain,(
% 1.85/0.65    k1_xboole_0 = sK3 | (~spl7_8 | ~spl7_19)),
% 1.85/0.65    inference(resolution,[],[f539,f163])).
% 1.85/0.65  fof(f163,plain,(
% 1.85/0.65    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl7_8),
% 1.85/0.65    inference(resolution,[],[f162,f59])).
% 1.85/0.65  fof(f59,plain,(
% 1.85/0.65    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.85/0.65    inference(cnf_transformation,[],[f4])).
% 1.85/0.65  fof(f4,axiom,(
% 1.85/0.65    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.85/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.85/0.65  fof(f162,plain,(
% 1.85/0.65    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl7_8),
% 1.85/0.65    inference(resolution,[],[f156,f129])).
% 1.85/0.65  fof(f129,plain,(
% 1.85/0.65    v1_xboole_0(k1_xboole_0) | ~spl7_8),
% 1.85/0.65    inference(avatar_component_clause,[],[f127])).
% 1.85/0.65  fof(f156,plain,(
% 1.85/0.65    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) )),
% 1.85/0.65    inference(resolution,[],[f61,f53])).
% 1.85/0.65  fof(f53,plain,(
% 1.85/0.65    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.85/0.65    inference(cnf_transformation,[],[f1])).
% 1.85/0.65  fof(f1,axiom,(
% 1.85/0.65    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.85/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.85/0.65  fof(f61,plain,(
% 1.85/0.65    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.85/0.65    inference(cnf_transformation,[],[f29])).
% 1.85/0.65  fof(f29,plain,(
% 1.85/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.85/0.65    inference(ennf_transformation,[],[f2])).
% 1.85/0.65  fof(f2,axiom,(
% 1.85/0.65    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.85/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.85/0.65  fof(f539,plain,(
% 1.85/0.65    ( ! [X0] : (r1_tarski(sK3,X0)) ) | ~spl7_19),
% 1.85/0.65    inference(resolution,[],[f211,f156])).
% 1.85/0.65  fof(f211,plain,(
% 1.85/0.65    v1_xboole_0(sK3) | ~spl7_19),
% 1.85/0.65    inference(avatar_component_clause,[],[f209])).
% 1.85/0.65  fof(f557,plain,(
% 1.85/0.65    spl7_62 | ~spl7_8 | ~spl7_17),
% 1.85/0.65    inference(avatar_split_clause,[],[f552,f200,f127,f554])).
% 1.85/0.65  fof(f554,plain,(
% 1.85/0.65    spl7_62 <=> k1_xboole_0 = sK2),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_62])])).
% 1.85/0.65  fof(f200,plain,(
% 1.85/0.65    spl7_17 <=> v1_xboole_0(sK2)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.85/0.65  fof(f552,plain,(
% 1.85/0.65    k1_xboole_0 = sK2 | (~spl7_8 | ~spl7_17)),
% 1.85/0.65    inference(resolution,[],[f523,f163])).
% 1.85/0.65  fof(f523,plain,(
% 1.85/0.65    ( ! [X0] : (r1_tarski(sK2,X0)) ) | ~spl7_17),
% 1.85/0.65    inference(resolution,[],[f202,f156])).
% 1.85/0.65  fof(f202,plain,(
% 1.85/0.65    v1_xboole_0(sK2) | ~spl7_17),
% 1.85/0.65    inference(avatar_component_clause,[],[f200])).
% 1.85/0.65  fof(f434,plain,(
% 1.85/0.65    ~spl7_10 | spl7_45 | ~spl7_3 | ~spl7_41),
% 1.85/0.65    inference(avatar_split_clause,[],[f430,f387,f102,f432,f143])).
% 1.85/0.65  fof(f430,plain,(
% 1.85/0.65    ( ! [X0] : (r2_hidden(sK4(sK2,X0),sK0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | sK2 = X0) ) | (~spl7_3 | ~spl7_41)),
% 1.85/0.65    inference(forward_demodulation,[],[f429,f389])).
% 1.85/0.65  fof(f429,plain,(
% 1.85/0.65    ( ! [X0] : (k1_relat_1(X0) != sK0 | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | (~spl7_3 | ~spl7_41)),
% 1.85/0.65    inference(forward_demodulation,[],[f427,f389])).
% 1.85/0.65  fof(f427,plain,(
% 1.85/0.65    ( ! [X0] : (~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK2) | r2_hidden(sK4(sK2,X0),k1_relat_1(sK2)) | sK2 = X0) ) | ~spl7_3),
% 1.85/0.65    inference(resolution,[],[f50,f104])).
% 1.85/0.65  fof(f50,plain,(
% 1.85/0.65    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | X0 = X1) )),
% 1.85/0.65    inference(cnf_transformation,[],[f25])).
% 1.85/0.65  fof(f396,plain,(
% 1.85/0.65    ~spl7_6 | spl7_40 | spl7_42 | ~spl7_5 | ~spl7_29),
% 1.85/0.65    inference(avatar_split_clause,[],[f391,f290,f112,f393,f383,f117])).
% 1.85/0.65  fof(f117,plain,(
% 1.85/0.65    spl7_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 1.85/0.65  fof(f383,plain,(
% 1.85/0.65    spl7_40 <=> k1_xboole_0 = sK1),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 1.85/0.65  fof(f290,plain,(
% 1.85/0.65    spl7_29 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).
% 1.85/0.65  fof(f391,plain,(
% 1.85/0.65    sK0 = k1_relat_1(sK3) | k1_xboole_0 = sK1 | ~v1_funct_2(sK3,sK0,sK1) | (~spl7_5 | ~spl7_29)),
% 1.85/0.65    inference(forward_demodulation,[],[f377,f292])).
% 1.85/0.65  fof(f292,plain,(
% 1.85/0.65    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_29),
% 1.85/0.65    inference(avatar_component_clause,[],[f290])).
% 1.85/0.65  fof(f377,plain,(
% 1.85/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl7_5),
% 1.85/0.65    inference(resolution,[],[f76,f114])).
% 1.85/0.65  fof(f76,plain,(
% 1.85/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.85/0.65    inference(cnf_transformation,[],[f34])).
% 1.85/0.65  fof(f34,plain,(
% 1.85/0.65    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.65    inference(flattening,[],[f33])).
% 1.85/0.65  fof(f33,plain,(
% 1.85/0.65    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.65    inference(ennf_transformation,[],[f17])).
% 1.85/0.65  fof(f17,axiom,(
% 1.85/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.85/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.85/0.65  fof(f390,plain,(
% 1.85/0.65    ~spl7_2 | spl7_40 | spl7_41 | ~spl7_1 | ~spl7_28),
% 1.85/0.65    inference(avatar_split_clause,[],[f381,f285,f92,f387,f383,f97])).
% 1.85/0.65  fof(f97,plain,(
% 1.85/0.65    spl7_2 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 1.85/0.65  fof(f285,plain,(
% 1.85/0.65    spl7_28 <=> k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.85/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 1.85/0.65  fof(f381,plain,(
% 1.85/0.65    sK0 = k1_relat_1(sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1) | (~spl7_1 | ~spl7_28)),
% 1.85/0.65    inference(forward_demodulation,[],[f376,f287])).
% 1.85/0.65  fof(f287,plain,(
% 1.85/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl7_28),
% 1.85/0.65    inference(avatar_component_clause,[],[f285])).
% 1.85/0.65  fof(f376,plain,(
% 1.85/0.65    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl7_1),
% 1.85/0.65    inference(resolution,[],[f76,f94])).
% 1.85/0.65  fof(f293,plain,(
% 1.85/0.65    spl7_29 | ~spl7_5),
% 1.85/0.65    inference(avatar_split_clause,[],[f281,f112,f290])).
% 1.85/0.65  fof(f281,plain,(
% 1.85/0.65    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl7_5),
% 1.85/0.65    inference(resolution,[],[f69,f114])).
% 1.85/0.65  fof(f69,plain,(
% 1.85/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.85/0.65    inference(cnf_transformation,[],[f31])).
% 2.21/0.65  fof(f31,plain,(
% 2.21/0.65    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.65    inference(ennf_transformation,[],[f15])).
% 2.21/0.65  fof(f15,axiom,(
% 2.21/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.21/0.65  fof(f288,plain,(
% 2.21/0.65    spl7_28 | ~spl7_1),
% 2.21/0.65    inference(avatar_split_clause,[],[f280,f92,f285])).
% 2.21/0.65  fof(f280,plain,(
% 2.21/0.65    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) | ~spl7_1),
% 2.21/0.65    inference(resolution,[],[f69,f94])).
% 2.21/0.65  fof(f212,plain,(
% 2.21/0.65    spl7_19 | ~spl7_18 | ~spl7_5),
% 2.21/0.65    inference(avatar_split_clause,[],[f196,f112,f204,f209])).
% 2.21/0.65  fof(f204,plain,(
% 2.21/0.65    spl7_18 <=> v1_xboole_0(sK1)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.21/0.65  fof(f196,plain,(
% 2.21/0.65    ~v1_xboole_0(sK1) | v1_xboole_0(sK3) | ~spl7_5),
% 2.21/0.65    inference(resolution,[],[f55,f114])).
% 2.21/0.65  fof(f55,plain,(
% 2.21/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0) | v1_xboole_0(X2)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f26])).
% 2.21/0.65  fof(f26,plain,(
% 2.21/0.65    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f14])).
% 2.21/0.65  fof(f14,axiom,(
% 2.21/0.65    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 2.21/0.65  fof(f207,plain,(
% 2.21/0.65    spl7_17 | ~spl7_18 | ~spl7_1),
% 2.21/0.65    inference(avatar_split_clause,[],[f195,f92,f204,f200])).
% 2.21/0.65  fof(f195,plain,(
% 2.21/0.65    ~v1_xboole_0(sK1) | v1_xboole_0(sK2) | ~spl7_1),
% 2.21/0.65    inference(resolution,[],[f55,f94])).
% 2.21/0.65  fof(f158,plain,(
% 2.21/0.65    spl7_11),
% 2.21/0.65    inference(avatar_contradiction_clause,[],[f157])).
% 2.21/0.65  fof(f157,plain,(
% 2.21/0.65    $false | spl7_11),
% 2.21/0.65    inference(resolution,[],[f149,f54])).
% 2.21/0.65  fof(f54,plain,(
% 2.21/0.65    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.21/0.65    inference(cnf_transformation,[],[f9])).
% 2.21/0.65  fof(f9,axiom,(
% 2.21/0.65    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.21/0.65  fof(f149,plain,(
% 2.21/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl7_11),
% 2.21/0.65    inference(avatar_component_clause,[],[f147])).
% 2.21/0.65  fof(f147,plain,(
% 2.21/0.65    spl7_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.21/0.65  fof(f155,plain,(
% 2.21/0.65    spl7_12 | ~spl7_11 | ~spl7_5),
% 2.21/0.65    inference(avatar_split_clause,[],[f141,f112,f147,f152])).
% 2.21/0.65  fof(f141,plain,(
% 2.21/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK3) | ~spl7_5),
% 2.21/0.65    inference(resolution,[],[f49,f114])).
% 2.21/0.65  fof(f49,plain,(
% 2.21/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 2.21/0.65    inference(cnf_transformation,[],[f23])).
% 2.21/0.65  fof(f23,plain,(
% 2.21/0.65    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.21/0.65    inference(ennf_transformation,[],[f8])).
% 2.21/0.65  fof(f8,axiom,(
% 2.21/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.21/0.65  fof(f150,plain,(
% 2.21/0.65    spl7_10 | ~spl7_11 | ~spl7_1),
% 2.21/0.65    inference(avatar_split_clause,[],[f140,f92,f147,f143])).
% 2.21/0.65  fof(f140,plain,(
% 2.21/0.65    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2) | ~spl7_1),
% 2.21/0.65    inference(resolution,[],[f49,f94])).
% 2.21/0.65  fof(f130,plain,(
% 2.21/0.65    spl7_8),
% 2.21/0.65    inference(avatar_split_clause,[],[f47,f127])).
% 2.21/0.65  fof(f47,plain,(
% 2.21/0.65    v1_xboole_0(k1_xboole_0)),
% 2.21/0.65    inference(cnf_transformation,[],[f3])).
% 2.21/0.65  fof(f3,axiom,(
% 2.21/0.65    v1_xboole_0(k1_xboole_0)),
% 2.21/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 2.21/0.65  fof(f125,plain,(
% 2.21/0.65    spl7_7),
% 2.21/0.65    inference(avatar_split_clause,[],[f40,f122])).
% 2.21/0.65  fof(f40,plain,(
% 2.21/0.65    v1_funct_1(sK3)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f120,plain,(
% 2.21/0.65    spl7_6),
% 2.21/0.65    inference(avatar_split_clause,[],[f41,f117])).
% 2.21/0.65  fof(f41,plain,(
% 2.21/0.65    v1_funct_2(sK3,sK0,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f115,plain,(
% 2.21/0.65    spl7_5),
% 2.21/0.65    inference(avatar_split_clause,[],[f42,f112])).
% 2.21/0.65  fof(f42,plain,(
% 2.21/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f110,plain,(
% 2.21/0.65    ~spl7_4),
% 2.21/0.65    inference(avatar_split_clause,[],[f43,f107])).
% 2.21/0.65  fof(f107,plain,(
% 2.21/0.65    spl7_4 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 2.21/0.65    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.21/0.65  fof(f43,plain,(
% 2.21/0.65    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f105,plain,(
% 2.21/0.65    spl7_3),
% 2.21/0.65    inference(avatar_split_clause,[],[f44,f102])).
% 2.21/0.65  fof(f44,plain,(
% 2.21/0.65    v1_funct_1(sK2)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f100,plain,(
% 2.21/0.65    spl7_2),
% 2.21/0.65    inference(avatar_split_clause,[],[f45,f97])).
% 2.21/0.65  fof(f45,plain,(
% 2.21/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  fof(f95,plain,(
% 2.21/0.65    spl7_1),
% 2.21/0.65    inference(avatar_split_clause,[],[f46,f92])).
% 2.21/0.65  fof(f46,plain,(
% 2.21/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.65    inference(cnf_transformation,[],[f22])).
% 2.21/0.65  % SZS output end Proof for theBenchmark
% 2.21/0.65  % (12427)------------------------------
% 2.21/0.65  % (12427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.65  % (12427)Termination reason: Refutation
% 2.21/0.65  
% 2.21/0.65  % (12427)Memory used [KB]: 11641
% 2.21/0.65  % (12427)Time elapsed: 0.206 s
% 2.21/0.65  % (12427)------------------------------
% 2.21/0.65  % (12427)------------------------------
% 2.21/0.65  % (12410)Success in time 0.289 s
%------------------------------------------------------------------------------
