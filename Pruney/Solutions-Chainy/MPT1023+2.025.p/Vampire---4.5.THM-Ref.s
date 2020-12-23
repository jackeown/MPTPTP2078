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
% DateTime   : Thu Dec  3 13:06:10 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 353 expanded)
%              Number of leaves         :   51 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  568 (1209 expanded)
%              Number of equality atoms :  113 ( 219 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1104,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f149,f154,f159,f174,f181,f186,f223,f238,f245,f329,f362,f365,f382,f425,f435,f461,f512,f572,f585,f588,f682,f683,f1074,f1091,f1097,f1102,f1103])).

fof(f1103,plain,
    ( sK2 != sK3
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1102,plain,
    ( ~ spl12_11
    | ~ spl12_2
    | spl12_38
    | ~ spl12_29
    | ~ spl12_43
    | spl12_70 ),
    inference(avatar_split_clause,[],[f1101,f1094,f680,f432,f594,f106,f171])).

fof(f171,plain,
    ( spl12_11
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).

fof(f106,plain,
    ( spl12_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f594,plain,
    ( spl12_38
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f432,plain,
    ( spl12_29
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f680,plain,
    ( spl12_43
  <=> ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).

fof(f1094,plain,
    ( spl12_70
  <=> r2_hidden(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f1101,plain,
    ( sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl12_29
    | ~ spl12_43
    | spl12_70 ),
    inference(trivial_inequality_removal,[],[f1100])).

fof(f1100,plain,
    ( sK0 != sK0
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl12_29
    | ~ spl12_43
    | spl12_70 ),
    inference(forward_demodulation,[],[f1098,f434])).

fof(f434,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f432])).

fof(f1098,plain,
    ( sK2 = sK3
    | sK0 != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl12_43
    | spl12_70 ),
    inference(resolution,[],[f1096,f681])).

fof(f681,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | sK3 = X0
        | k1_relat_1(X0) != sK0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl12_43 ),
    inference(avatar_component_clause,[],[f680])).

fof(f1096,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl12_70 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f1097,plain,
    ( ~ spl12_70
    | spl12_69 ),
    inference(avatar_split_clause,[],[f1092,f1088,f1094])).

fof(f1088,plain,
    ( spl12_69
  <=> m1_subset_1(sK4(sK3,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).

fof(f1092,plain,
    ( ~ r2_hidden(sK4(sK3,sK2),sK0)
    | spl12_69 ),
    inference(resolution,[],[f1090,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f1090,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),sK0)
    | spl12_69 ),
    inference(avatar_component_clause,[],[f1088])).

fof(f1091,plain,
    ( ~ spl12_11
    | ~ spl12_2
    | spl12_38
    | ~ spl12_69
    | ~ spl12_29
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f1086,f1072,f432,f1088,f594,f106,f171])).

fof(f1072,plain,
    ( spl12_68
  <=> ! [X0] :
        ( k1_relat_1(X0) != sK0
        | ~ m1_subset_1(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f1086,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl12_29
    | ~ spl12_68 ),
    inference(trivial_inequality_removal,[],[f1085])).

fof(f1085,plain,
    ( sK0 != sK0
    | ~ m1_subset_1(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl12_29
    | ~ spl12_68 ),
    inference(forward_demodulation,[],[f1084,f434])).

fof(f1084,plain,
    ( ~ m1_subset_1(sK4(sK3,sK2),sK0)
    | sK2 = sK3
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK0 != k1_relat_1(sK2)
    | ~ spl12_68 ),
    inference(equality_resolution,[],[f1073])).

fof(f1073,plain,
    ( ! [X0] :
        ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ m1_subset_1(sK4(sK3,X0),sK0)
        | sK3 = X0
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK0 )
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f1072])).

fof(f1074,plain,
    ( ~ spl12_8
    | spl12_68
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f687,f242,f1072,f146])).

fof(f146,plain,
    ( spl12_8
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f242,plain,
    ( spl12_22
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).

fof(f687,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK0
        | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | sK3 = X0
        | ~ m1_subset_1(sK4(sK3,X0),sK0) )
    | ~ spl12_22 ),
    inference(forward_demodulation,[],[f189,f244])).

fof(f244,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl12_22 ),
    inference(avatar_component_clause,[],[f242])).

fof(f189,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ m1_subset_1(sK4(sK3,X0),sK0) ) ),
    inference(global_subsumption,[],[f42,f187])).

fof(f187,plain,(
    ! [X0] :
      ( k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0))
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_relat_1(sK3)
      | sK3 = X0
      | ~ m1_subset_1(sK4(sK3,X0),sK0) ) ),
    inference(superposition,[],[f53,f41])).

fof(f41,plain,(
    ! [X4] :
      ( k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4)
      | ~ m1_subset_1(X4,sK0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).

fof(f42,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f683,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != sK2
    | r2_relset_1(sK0,sK1,sK2,sK3)
    | ~ r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f682,plain,
    ( ~ spl12_8
    | ~ spl12_1
    | spl12_43
    | ~ spl12_22 ),
    inference(avatar_split_clause,[],[f290,f242,f680,f101,f146])).

fof(f101,plain,
    ( spl12_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f290,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK3,X0),sK0)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != sK0
        | ~ v1_relat_1(sK3)
        | sK3 = X0 )
    | ~ spl12_22 ),
    inference(superposition,[],[f52,f244])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f588,plain,
    ( ~ spl12_30
    | ~ spl12_12
    | spl12_35 ),
    inference(avatar_split_clause,[],[f587,f578,f178,f458])).

fof(f458,plain,
    ( spl12_30
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f178,plain,
    ( spl12_12
  <=> r2_relset_1(sK0,sK1,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f578,plain,
    ( spl12_35
  <=> r2_relset_1(sK0,sK1,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).

fof(f587,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl12_12
    | spl12_35 ),
    inference(resolution,[],[f586,f180])).

fof(f180,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f586,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK1,X0,sK2)
        | ~ v1_xboole_0(X0) )
    | spl12_35 ),
    inference(superposition,[],[f580,f51])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f580,plain,
    ( ~ r2_relset_1(sK0,sK1,k1_xboole_0,sK2)
    | spl12_35 ),
    inference(avatar_component_clause,[],[f578])).

fof(f585,plain,
    ( ~ spl12_35
    | spl12_36
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f516,f131,f582,f578])).

fof(f582,plain,
    ( spl12_36
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).

fof(f131,plain,
    ( spl12_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f516,plain,
    ( k1_xboole_0 = sK2
    | ~ r2_relset_1(sK0,sK1,k1_xboole_0,sK2)
    | ~ spl12_7 ),
    inference(resolution,[],[f163,f50])).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK2 = X0
        | ~ r2_relset_1(sK0,sK1,X0,sK2) )
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f133,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f131])).

fof(f572,plain,
    ( ~ spl12_26
    | ~ spl12_9
    | spl12_31 ),
    inference(avatar_split_clause,[],[f567,f505,f151,f379])).

fof(f379,plain,
    ( spl12_26
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f151,plain,
    ( spl12_9
  <=> r2_relset_1(sK0,sK1,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f505,plain,
    ( spl12_31
  <=> r2_relset_1(sK0,sK1,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f567,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl12_9
    | spl12_31 ),
    inference(resolution,[],[f564,f153])).

fof(f153,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f564,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK1,X0,sK3)
        | ~ v1_xboole_0(X0) )
    | spl12_31 ),
    inference(superposition,[],[f507,f51])).

fof(f507,plain,
    ( ~ r2_relset_1(sK0,sK1,k1_xboole_0,sK3)
    | spl12_31 ),
    inference(avatar_component_clause,[],[f505])).

fof(f512,plain,
    ( ~ spl12_31
    | spl12_32
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f499,f126,f509,f505])).

fof(f509,plain,
    ( spl12_32
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f126,plain,
    ( spl12_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f499,plain,
    ( k1_xboole_0 = sK3
    | ~ r2_relset_1(sK0,sK1,k1_xboole_0,sK3)
    | ~ spl12_6 ),
    inference(resolution,[],[f138,f50])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | sK3 = X0
        | ~ r2_relset_1(sK0,sK1,X0,sK3) )
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f84])).

fof(f128,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f461,plain,
    ( spl12_30
    | ~ spl12_28 ),
    inference(avatar_split_clause,[],[f455,f423,f458])).

fof(f423,plain,
    ( spl12_28
  <=> ! [X1] : ~ r2_hidden(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f455,plain,
    ( v1_xboole_0(sK2)
    | ~ spl12_28 ),
    inference(resolution,[],[f424,f54])).

fof(f54,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f424,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK2)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f423])).

fof(f435,plain,
    ( ~ spl12_7
    | spl12_29
    | ~ spl12_24 ),
    inference(avatar_split_clause,[],[f420,f326,f432,f131])).

fof(f326,plain,
    ( spl12_24
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).

fof(f420,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_24 ),
    inference(superposition,[],[f328,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f328,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl12_24 ),
    inference(avatar_component_clause,[],[f326])).

fof(f425,plain,
    ( ~ spl12_18
    | spl12_28
    | ~ spl12_13 ),
    inference(avatar_split_clause,[],[f225,f183,f423,f217])).

fof(f217,plain,
    ( spl12_18
  <=> sP11(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f183,plain,
    ( spl12_13
  <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).

fof(f225,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK2)
        | ~ sP11(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl12_13 ),
    inference(resolution,[],[f192,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP11(X1) ) ),
    inference(general_splitting,[],[f82,f97_D])).

fof(f97,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP11(X1) ) ),
    inference(cnf_transformation,[],[f97_D])).

fof(f97_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP11(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f192,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK2) )
    | ~ spl12_13 ),
    inference(resolution,[],[f185,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f185,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl12_13 ),
    inference(avatar_component_clause,[],[f183])).

fof(f382,plain,
    ( spl12_26
    | ~ spl12_19 ),
    inference(avatar_split_clause,[],[f376,f221,f379])).

fof(f221,plain,
    ( spl12_19
  <=> ! [X1] : ~ r2_hidden(X1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).

fof(f376,plain,
    ( v1_xboole_0(sK3)
    | ~ spl12_19 ),
    inference(resolution,[],[f222,f54])).

fof(f222,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3)
    | ~ spl12_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f365,plain,(
    spl12_25 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | spl12_25 ),
    inference(unit_resulting_resolution,[],[f49,f50,f361,f97])).

fof(f361,plain,
    ( ~ sP11(k1_xboole_0)
    | spl12_25 ),
    inference(avatar_component_clause,[],[f359])).

fof(f359,plain,
    ( spl12_25
  <=> sP11(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f362,plain,
    ( ~ spl12_25
    | spl12_18
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f357,f235,f217,f359])).

fof(f235,plain,
    ( spl12_21
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f357,plain,
    ( ~ sP11(k1_xboole_0)
    | spl12_18
    | ~ spl12_21 ),
    inference(forward_demodulation,[],[f345,f85])).

fof(f85,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f345,plain,
    ( ~ sP11(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl12_18
    | ~ spl12_21 ),
    inference(backward_demodulation,[],[f219,f237])).

fof(f237,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f219,plain,
    ( ~ sP11(k2_zfmisc_1(sK0,sK1))
    | spl12_18 ),
    inference(avatar_component_clause,[],[f217])).

fof(f329,plain,
    ( ~ spl12_4
    | spl12_24
    | spl12_21
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f162,f131,f235,f326,f116])).

fof(f116,plain,
    ( spl12_4
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f162,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f245,plain,
    ( ~ spl12_6
    | spl12_22
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f239,f231,f242,f126])).

fof(f231,plain,
    ( spl12_20
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f239,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_20 ),
    inference(superposition,[],[f233,f67])).

fof(f233,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f231])).

fof(f238,plain,
    ( ~ spl12_3
    | spl12_20
    | spl12_21
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f137,f126,f235,f231,f111])).

fof(f111,plain,
    ( spl12_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f137,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ v1_funct_2(sK3,sK0,sK1)
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f73])).

fof(f223,plain,
    ( ~ spl12_18
    | spl12_19
    | ~ spl12_10 ),
    inference(avatar_split_clause,[],[f213,f156,f221,f217])).

fof(f156,plain,
    ( spl12_10
  <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f213,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | ~ sP11(k2_zfmisc_1(sK0,sK1)) )
    | ~ spl12_10 ),
    inference(resolution,[],[f176,f98])).

fof(f176,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
        | ~ r2_hidden(X0,sK3) )
    | ~ spl12_10 ),
    inference(resolution,[],[f158,f57])).

fof(f158,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f186,plain,
    ( spl12_13
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f168,f131,f183])).

fof(f168,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f181,plain,
    ( spl12_12
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f166,f131,f178])).

fof(f166,plain,
    ( r2_relset_1(sK0,sK1,sK2,sK2)
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f99])).

fof(f99,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f174,plain,
    ( spl12_11
    | ~ spl12_7 ),
    inference(avatar_split_clause,[],[f160,f131,f171])).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ spl12_7 ),
    inference(resolution,[],[f133,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( spl12_10
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f143,f126,f156])).

fof(f143,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f61])).

fof(f154,plain,
    ( spl12_9
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f141,f126,f151])).

fof(f141,plain,
    ( r2_relset_1(sK0,sK1,sK3,sK3)
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f99])).

fof(f149,plain,
    ( spl12_8
    | ~ spl12_6 ),
    inference(avatar_split_clause,[],[f135,f126,f146])).

fof(f135,plain,
    ( v1_relat_1(sK3)
    | ~ spl12_6 ),
    inference(resolution,[],[f128,f66])).

fof(f134,plain,(
    spl12_7 ),
    inference(avatar_split_clause,[],[f48,f131])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f129,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f44,f126])).

fof(f44,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f124,plain,(
    ~ spl12_5 ),
    inference(avatar_split_clause,[],[f45,f121])).

fof(f121,plain,
    ( spl12_5
  <=> r2_relset_1(sK0,sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

fof(f45,plain,(
    ~ r2_relset_1(sK0,sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f119,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f47,f116])).

fof(f47,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f114,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f43,f111])).

fof(f43,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f109,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f46,f106])).

fof(f46,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f104,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f42,f101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:22:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (5841)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (5846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (5855)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (5847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (5864)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (5842)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (5843)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (5852)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (5851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (5865)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (5851)Refutation not found, incomplete strategy% (5851)------------------------------
% 0.21/0.53  % (5851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (5851)Memory used [KB]: 10746
% 0.21/0.53  % (5851)Time elapsed: 0.116 s
% 0.21/0.53  % (5851)------------------------------
% 0.21/0.53  % (5851)------------------------------
% 0.21/0.53  % (5857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (5859)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (5863)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (5853)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (5844)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (5848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (5869)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (5867)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (5862)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.54  % (5858)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (5845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (5852)Refutation not found, incomplete strategy% (5852)------------------------------
% 0.21/0.54  % (5852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (5852)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (5852)Memory used [KB]: 10746
% 0.21/0.54  % (5852)Time elapsed: 0.108 s
% 0.21/0.54  % (5852)------------------------------
% 0.21/0.54  % (5852)------------------------------
% 0.21/0.55  % (5868)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (5860)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (5870)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (5871)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (5850)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (5861)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (5854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.51/0.57  % (5866)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.51/0.57  % (5849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.64/0.58  % (5864)Refutation found. Thanks to Tanya!
% 1.64/0.58  % SZS status Theorem for theBenchmark
% 1.64/0.59  % SZS output start Proof for theBenchmark
% 1.64/0.59  fof(f1104,plain,(
% 1.64/0.59    $false),
% 1.64/0.59    inference(avatar_sat_refutation,[],[f104,f109,f114,f119,f124,f129,f134,f149,f154,f159,f174,f181,f186,f223,f238,f245,f329,f362,f365,f382,f425,f435,f461,f512,f572,f585,f588,f682,f683,f1074,f1091,f1097,f1102,f1103])).
% 1.64/0.60  fof(f1103,plain,(
% 1.64/0.60    sK2 != sK3 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.64/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.64/0.60  fof(f1102,plain,(
% 1.64/0.60    ~spl12_11 | ~spl12_2 | spl12_38 | ~spl12_29 | ~spl12_43 | spl12_70),
% 1.64/0.60    inference(avatar_split_clause,[],[f1101,f1094,f680,f432,f594,f106,f171])).
% 1.64/0.60  fof(f171,plain,(
% 1.64/0.60    spl12_11 <=> v1_relat_1(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_11])])).
% 1.64/0.60  fof(f106,plain,(
% 1.64/0.60    spl12_2 <=> v1_funct_1(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 1.64/0.60  fof(f594,plain,(
% 1.64/0.60    spl12_38 <=> sK2 = sK3),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).
% 1.64/0.60  fof(f432,plain,(
% 1.64/0.60    spl12_29 <=> sK0 = k1_relat_1(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).
% 1.64/0.60  fof(f680,plain,(
% 1.64/0.60    spl12_43 <=> ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_43])])).
% 1.64/0.60  fof(f1094,plain,(
% 1.64/0.60    spl12_70 <=> r2_hidden(sK4(sK3,sK2),sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).
% 1.64/0.60  fof(f1101,plain,(
% 1.64/0.60    sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl12_29 | ~spl12_43 | spl12_70)),
% 1.64/0.60    inference(trivial_inequality_removal,[],[f1100])).
% 1.64/0.60  fof(f1100,plain,(
% 1.64/0.60    sK0 != sK0 | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl12_29 | ~spl12_43 | spl12_70)),
% 1.64/0.60    inference(forward_demodulation,[],[f1098,f434])).
% 1.64/0.60  fof(f434,plain,(
% 1.64/0.60    sK0 = k1_relat_1(sK2) | ~spl12_29),
% 1.64/0.60    inference(avatar_component_clause,[],[f432])).
% 1.64/0.60  fof(f1098,plain,(
% 1.64/0.60    sK2 = sK3 | sK0 != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl12_43 | spl12_70)),
% 1.64/0.60    inference(resolution,[],[f1096,f681])).
% 1.64/0.60  fof(f681,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | sK3 = X0 | k1_relat_1(X0) != sK0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl12_43),
% 1.64/0.60    inference(avatar_component_clause,[],[f680])).
% 1.64/0.60  fof(f1096,plain,(
% 1.64/0.60    ~r2_hidden(sK4(sK3,sK2),sK0) | spl12_70),
% 1.64/0.60    inference(avatar_component_clause,[],[f1094])).
% 1.64/0.60  fof(f1097,plain,(
% 1.64/0.60    ~spl12_70 | spl12_69),
% 1.64/0.60    inference(avatar_split_clause,[],[f1092,f1088,f1094])).
% 1.64/0.60  fof(f1088,plain,(
% 1.64/0.60    spl12_69 <=> m1_subset_1(sK4(sK3,sK2),sK0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_69])])).
% 1.64/0.60  fof(f1092,plain,(
% 1.64/0.60    ~r2_hidden(sK4(sK3,sK2),sK0) | spl12_69),
% 1.64/0.60    inference(resolution,[],[f1090,f56])).
% 1.64/0.60  fof(f56,plain,(
% 1.64/0.60    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f26])).
% 1.64/0.60  fof(f26,plain,(
% 1.64/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.64/0.60    inference(ennf_transformation,[],[f8])).
% 1.64/0.60  fof(f8,axiom,(
% 1.64/0.60    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.64/0.60  fof(f1090,plain,(
% 1.64/0.60    ~m1_subset_1(sK4(sK3,sK2),sK0) | spl12_69),
% 1.64/0.60    inference(avatar_component_clause,[],[f1088])).
% 1.64/0.60  fof(f1091,plain,(
% 1.64/0.60    ~spl12_11 | ~spl12_2 | spl12_38 | ~spl12_69 | ~spl12_29 | ~spl12_68),
% 1.64/0.60    inference(avatar_split_clause,[],[f1086,f1072,f432,f1088,f594,f106,f171])).
% 1.64/0.60  fof(f1072,plain,(
% 1.64/0.60    spl12_68 <=> ! [X0] : (k1_relat_1(X0) != sK0 | ~m1_subset_1(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).
% 1.64/0.60  fof(f1086,plain,(
% 1.64/0.60    ~m1_subset_1(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl12_29 | ~spl12_68)),
% 1.64/0.60    inference(trivial_inequality_removal,[],[f1085])).
% 1.64/0.60  fof(f1085,plain,(
% 1.64/0.60    sK0 != sK0 | ~m1_subset_1(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl12_29 | ~spl12_68)),
% 1.64/0.60    inference(forward_demodulation,[],[f1084,f434])).
% 1.64/0.60  fof(f1084,plain,(
% 1.64/0.60    ~m1_subset_1(sK4(sK3,sK2),sK0) | sK2 = sK3 | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK0 != k1_relat_1(sK2) | ~spl12_68),
% 1.64/0.60    inference(equality_resolution,[],[f1073])).
% 1.64/0.60  fof(f1073,plain,(
% 1.64/0.60    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~m1_subset_1(sK4(sK3,X0),sK0) | sK3 = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK0) ) | ~spl12_68),
% 1.64/0.60    inference(avatar_component_clause,[],[f1072])).
% 1.64/0.60  fof(f1074,plain,(
% 1.64/0.60    ~spl12_8 | spl12_68 | ~spl12_22),
% 1.64/0.60    inference(avatar_split_clause,[],[f687,f242,f1072,f146])).
% 1.64/0.60  fof(f146,plain,(
% 1.64/0.60    spl12_8 <=> v1_relat_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).
% 1.64/0.60  fof(f242,plain,(
% 1.64/0.60    spl12_22 <=> sK0 = k1_relat_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_22])])).
% 1.64/0.60  fof(f687,plain,(
% 1.64/0.60    ( ! [X0] : (k1_relat_1(X0) != sK0 | k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(sK3) | sK3 = X0 | ~m1_subset_1(sK4(sK3,X0),sK0)) ) | ~spl12_22),
% 1.64/0.60    inference(forward_demodulation,[],[f189,f244])).
% 1.64/0.60  fof(f244,plain,(
% 1.64/0.60    sK0 = k1_relat_1(sK3) | ~spl12_22),
% 1.64/0.60    inference(avatar_component_clause,[],[f242])).
% 1.64/0.60  fof(f189,plain,(
% 1.64/0.60    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~m1_subset_1(sK4(sK3,X0),sK0)) )),
% 1.64/0.60    inference(global_subsumption,[],[f42,f187])).
% 1.64/0.60  fof(f187,plain,(
% 1.64/0.60    ( ! [X0] : (k1_funct_1(X0,sK4(sK3,X0)) != k1_funct_1(sK2,sK4(sK3,X0)) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK3 = X0 | ~m1_subset_1(sK4(sK3,X0),sK0)) )),
% 1.64/0.60    inference(superposition,[],[f53,f41])).
% 1.64/0.60  fof(f41,plain,(
% 1.64/0.60    ( ! [X4] : (k1_funct_1(sK2,X4) = k1_funct_1(sK3,X4) | ~m1_subset_1(X4,sK0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f22,plain,(
% 1.64/0.60    ? [X0,X1,X2] : (? [X3] : (~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.64/0.60    inference(flattening,[],[f21])).
% 1.64/0.60  fof(f21,plain,(
% 1.64/0.60    ? [X0,X1,X2] : (? [X3] : ((~r2_relset_1(X0,X1,X2,X3) & ! [X4] : (k1_funct_1(X2,X4) = k1_funct_1(X3,X4) | ~m1_subset_1(X4,X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.64/0.60    inference(ennf_transformation,[],[f20])).
% 1.64/0.60  fof(f20,negated_conjecture,(
% 1.64/0.60    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.64/0.60    inference(negated_conjecture,[],[f19])).
% 1.64/0.60  fof(f19,conjecture,(
% 1.64/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X0) => k1_funct_1(X2,X4) = k1_funct_1(X3,X4)) => r2_relset_1(X0,X1,X2,X3))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_funct_2)).
% 1.64/0.60  fof(f53,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_funct_1(X0,sK4(X0,X1)) != k1_funct_1(X1,sK4(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f25])).
% 1.64/0.60  fof(f25,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : (X0 = X1 | ? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.64/0.60    inference(flattening,[],[f24])).
% 1.64/0.60  fof(f24,plain,(
% 1.64/0.60    ! [X0] : (! [X1] : ((X0 = X1 | (? [X2] : (k1_funct_1(X0,X2) != k1_funct_1(X1,X2) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f12])).
% 1.64/0.60  fof(f12,axiom,(
% 1.64/0.60    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2] : (r2_hidden(X2,k1_relat_1(X0)) => k1_funct_1(X0,X2) = k1_funct_1(X1,X2)) & k1_relat_1(X0) = k1_relat_1(X1)) => X0 = X1)))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_funct_1)).
% 1.64/0.60  fof(f42,plain,(
% 1.64/0.60    v1_funct_1(sK3)),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f683,plain,(
% 1.64/0.60    k1_xboole_0 != sK3 | k1_xboole_0 != sK2 | r2_relset_1(sK0,sK1,sK2,sK3) | ~r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.64/0.60    introduced(theory_tautology_sat_conflict,[])).
% 1.64/0.60  fof(f682,plain,(
% 1.64/0.60    ~spl12_8 | ~spl12_1 | spl12_43 | ~spl12_22),
% 1.64/0.60    inference(avatar_split_clause,[],[f290,f242,f680,f101,f146])).
% 1.64/0.60  fof(f101,plain,(
% 1.64/0.60    spl12_1 <=> v1_funct_1(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 1.64/0.60  fof(f290,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(sK4(sK3,X0),sK0) | ~v1_funct_1(sK3) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != sK0 | ~v1_relat_1(sK3) | sK3 = X0) ) | ~spl12_22),
% 1.64/0.60    inference(superposition,[],[f52,f244])).
% 1.64/0.60  fof(f52,plain,(
% 1.64/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X0) != k1_relat_1(X1) | ~v1_relat_1(X0) | X0 = X1) )),
% 1.64/0.60    inference(cnf_transformation,[],[f25])).
% 1.64/0.60  fof(f588,plain,(
% 1.64/0.60    ~spl12_30 | ~spl12_12 | spl12_35),
% 1.64/0.60    inference(avatar_split_clause,[],[f587,f578,f178,f458])).
% 1.64/0.60  fof(f458,plain,(
% 1.64/0.60    spl12_30 <=> v1_xboole_0(sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).
% 1.64/0.60  fof(f178,plain,(
% 1.64/0.60    spl12_12 <=> r2_relset_1(sK0,sK1,sK2,sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).
% 1.64/0.60  fof(f578,plain,(
% 1.64/0.60    spl12_35 <=> r2_relset_1(sK0,sK1,k1_xboole_0,sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_35])])).
% 1.64/0.60  fof(f587,plain,(
% 1.64/0.60    ~v1_xboole_0(sK2) | (~spl12_12 | spl12_35)),
% 1.64/0.60    inference(resolution,[],[f586,f180])).
% 1.64/0.60  fof(f180,plain,(
% 1.64/0.60    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl12_12),
% 1.64/0.60    inference(avatar_component_clause,[],[f178])).
% 1.64/0.60  fof(f586,plain,(
% 1.64/0.60    ( ! [X0] : (~r2_relset_1(sK0,sK1,X0,sK2) | ~v1_xboole_0(X0)) ) | spl12_35),
% 1.64/0.60    inference(superposition,[],[f580,f51])).
% 1.64/0.60  fof(f51,plain,(
% 1.64/0.60    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f23])).
% 1.64/0.60  fof(f23,plain,(
% 1.64/0.60    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.64/0.60    inference(ennf_transformation,[],[f4])).
% 1.64/0.60  fof(f4,axiom,(
% 1.64/0.60    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.64/0.60  fof(f580,plain,(
% 1.64/0.60    ~r2_relset_1(sK0,sK1,k1_xboole_0,sK2) | spl12_35),
% 1.64/0.60    inference(avatar_component_clause,[],[f578])).
% 1.64/0.60  fof(f585,plain,(
% 1.64/0.60    ~spl12_35 | spl12_36 | ~spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f516,f131,f582,f578])).
% 1.64/0.60  fof(f582,plain,(
% 1.64/0.60    spl12_36 <=> k1_xboole_0 = sK2),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_36])])).
% 1.64/0.60  fof(f131,plain,(
% 1.64/0.60    spl12_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).
% 1.64/0.60  fof(f516,plain,(
% 1.64/0.60    k1_xboole_0 = sK2 | ~r2_relset_1(sK0,sK1,k1_xboole_0,sK2) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f163,f50])).
% 1.64/0.60  fof(f50,plain,(
% 1.64/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f7])).
% 1.64/0.60  fof(f7,axiom,(
% 1.64/0.60    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.64/0.60  fof(f163,plain,(
% 1.64/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK2 = X0 | ~r2_relset_1(sK0,sK1,X0,sK2)) ) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f133,f84])).
% 1.64/0.60  fof(f84,plain,(
% 1.64/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f40])).
% 1.64/0.60  fof(f40,plain,(
% 1.64/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(flattening,[],[f39])).
% 1.64/0.60  fof(f39,plain,(
% 1.64/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.64/0.60    inference(ennf_transformation,[],[f17])).
% 1.64/0.60  fof(f17,axiom,(
% 1.64/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.64/0.60  fof(f133,plain,(
% 1.64/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_7),
% 1.64/0.60    inference(avatar_component_clause,[],[f131])).
% 1.64/0.60  fof(f572,plain,(
% 1.64/0.60    ~spl12_26 | ~spl12_9 | spl12_31),
% 1.64/0.60    inference(avatar_split_clause,[],[f567,f505,f151,f379])).
% 1.64/0.60  fof(f379,plain,(
% 1.64/0.60    spl12_26 <=> v1_xboole_0(sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).
% 1.64/0.60  fof(f151,plain,(
% 1.64/0.60    spl12_9 <=> r2_relset_1(sK0,sK1,sK3,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 1.64/0.60  fof(f505,plain,(
% 1.64/0.60    spl12_31 <=> r2_relset_1(sK0,sK1,k1_xboole_0,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).
% 1.64/0.60  fof(f567,plain,(
% 1.64/0.60    ~v1_xboole_0(sK3) | (~spl12_9 | spl12_31)),
% 1.64/0.60    inference(resolution,[],[f564,f153])).
% 1.64/0.60  fof(f153,plain,(
% 1.64/0.60    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl12_9),
% 1.64/0.60    inference(avatar_component_clause,[],[f151])).
% 1.64/0.60  fof(f564,plain,(
% 1.64/0.60    ( ! [X0] : (~r2_relset_1(sK0,sK1,X0,sK3) | ~v1_xboole_0(X0)) ) | spl12_31),
% 1.64/0.60    inference(superposition,[],[f507,f51])).
% 1.64/0.60  fof(f507,plain,(
% 1.64/0.60    ~r2_relset_1(sK0,sK1,k1_xboole_0,sK3) | spl12_31),
% 1.64/0.60    inference(avatar_component_clause,[],[f505])).
% 1.64/0.60  fof(f512,plain,(
% 1.64/0.60    ~spl12_31 | spl12_32 | ~spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f499,f126,f509,f505])).
% 1.64/0.60  fof(f509,plain,(
% 1.64/0.60    spl12_32 <=> k1_xboole_0 = sK3),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).
% 1.64/0.60  fof(f126,plain,(
% 1.64/0.60    spl12_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 1.64/0.60  fof(f499,plain,(
% 1.64/0.60    k1_xboole_0 = sK3 | ~r2_relset_1(sK0,sK1,k1_xboole_0,sK3) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f138,f50])).
% 1.64/0.60  fof(f138,plain,(
% 1.64/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK3 = X0 | ~r2_relset_1(sK0,sK1,X0,sK3)) ) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f128,f84])).
% 1.64/0.60  fof(f128,plain,(
% 1.64/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_6),
% 1.64/0.60    inference(avatar_component_clause,[],[f126])).
% 1.64/0.60  fof(f461,plain,(
% 1.64/0.60    spl12_30 | ~spl12_28),
% 1.64/0.60    inference(avatar_split_clause,[],[f455,f423,f458])).
% 1.64/0.60  fof(f423,plain,(
% 1.64/0.60    spl12_28 <=> ! [X1] : ~r2_hidden(X1,sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 1.64/0.60  fof(f455,plain,(
% 1.64/0.60    v1_xboole_0(sK2) | ~spl12_28),
% 1.64/0.60    inference(resolution,[],[f424,f54])).
% 1.64/0.60  fof(f54,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f1])).
% 1.64/0.60  fof(f1,axiom,(
% 1.64/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.64/0.60  fof(f424,plain,(
% 1.64/0.60    ( ! [X1] : (~r2_hidden(X1,sK2)) ) | ~spl12_28),
% 1.64/0.60    inference(avatar_component_clause,[],[f423])).
% 1.64/0.60  fof(f435,plain,(
% 1.64/0.60    ~spl12_7 | spl12_29 | ~spl12_24),
% 1.64/0.60    inference(avatar_split_clause,[],[f420,f326,f432,f131])).
% 1.64/0.60  fof(f326,plain,(
% 1.64/0.60    spl12_24 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_24])])).
% 1.64/0.60  fof(f420,plain,(
% 1.64/0.60    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_24),
% 1.64/0.60    inference(superposition,[],[f328,f67])).
% 1.64/0.60  fof(f67,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.64/0.60    inference(cnf_transformation,[],[f30])).
% 1.64/0.60  fof(f30,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f16])).
% 1.64/0.60  fof(f16,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.64/0.60  fof(f328,plain,(
% 1.64/0.60    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl12_24),
% 1.64/0.60    inference(avatar_component_clause,[],[f326])).
% 1.64/0.60  fof(f425,plain,(
% 1.64/0.60    ~spl12_18 | spl12_28 | ~spl12_13),
% 1.64/0.60    inference(avatar_split_clause,[],[f225,f183,f423,f217])).
% 1.64/0.60  fof(f217,plain,(
% 1.64/0.60    spl12_18 <=> sP11(k2_zfmisc_1(sK0,sK1))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 1.64/0.60  fof(f183,plain,(
% 1.64/0.60    spl12_13 <=> r1_tarski(sK2,k2_zfmisc_1(sK0,sK1))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_13])])).
% 1.64/0.60  fof(f225,plain,(
% 1.64/0.60    ( ! [X1] : (~r2_hidden(X1,sK2) | ~sP11(k2_zfmisc_1(sK0,sK1))) ) | ~spl12_13),
% 1.64/0.60    inference(resolution,[],[f192,f98])).
% 1.64/0.60  fof(f98,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP11(X1)) )),
% 1.64/0.60    inference(general_splitting,[],[f82,f97_D])).
% 1.64/0.60  fof(f97,plain,(
% 1.64/0.60    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP11(X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f97_D])).
% 1.64/0.60  fof(f97_D,plain,(
% 1.64/0.60    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP11(X1)) )),
% 1.64/0.60    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP11])])).
% 1.64/0.60  fof(f82,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f38])).
% 1.64/0.60  fof(f38,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.64/0.60    inference(ennf_transformation,[],[f11])).
% 1.64/0.60  fof(f11,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.64/0.60  fof(f192,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK2)) ) | ~spl12_13),
% 1.64/0.60    inference(resolution,[],[f185,f57])).
% 1.64/0.60  fof(f57,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f27])).
% 1.64/0.60  fof(f27,plain,(
% 1.64/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.64/0.60    inference(ennf_transformation,[],[f2])).
% 1.64/0.60  fof(f2,axiom,(
% 1.64/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.64/0.60  fof(f185,plain,(
% 1.64/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl12_13),
% 1.64/0.60    inference(avatar_component_clause,[],[f183])).
% 1.64/0.60  fof(f382,plain,(
% 1.64/0.60    spl12_26 | ~spl12_19),
% 1.64/0.60    inference(avatar_split_clause,[],[f376,f221,f379])).
% 1.64/0.60  fof(f221,plain,(
% 1.64/0.60    spl12_19 <=> ! [X1] : ~r2_hidden(X1,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_19])])).
% 1.64/0.60  fof(f376,plain,(
% 1.64/0.60    v1_xboole_0(sK3) | ~spl12_19),
% 1.64/0.60    inference(resolution,[],[f222,f54])).
% 1.64/0.60  fof(f222,plain,(
% 1.64/0.60    ( ! [X1] : (~r2_hidden(X1,sK3)) ) | ~spl12_19),
% 1.64/0.60    inference(avatar_component_clause,[],[f221])).
% 1.64/0.60  fof(f365,plain,(
% 1.64/0.60    spl12_25),
% 1.64/0.60    inference(avatar_contradiction_clause,[],[f363])).
% 1.64/0.60  fof(f363,plain,(
% 1.64/0.60    $false | spl12_25),
% 1.64/0.60    inference(unit_resulting_resolution,[],[f49,f50,f361,f97])).
% 1.64/0.60  fof(f361,plain,(
% 1.64/0.60    ~sP11(k1_xboole_0) | spl12_25),
% 1.64/0.60    inference(avatar_component_clause,[],[f359])).
% 1.64/0.60  fof(f359,plain,(
% 1.64/0.60    spl12_25 <=> sP11(k1_xboole_0)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 1.64/0.60  fof(f49,plain,(
% 1.64/0.60    v1_xboole_0(k1_xboole_0)),
% 1.64/0.60    inference(cnf_transformation,[],[f3])).
% 1.64/0.60  fof(f3,axiom,(
% 1.64/0.60    v1_xboole_0(k1_xboole_0)),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.64/0.60  fof(f362,plain,(
% 1.64/0.60    ~spl12_25 | spl12_18 | ~spl12_21),
% 1.64/0.60    inference(avatar_split_clause,[],[f357,f235,f217,f359])).
% 1.64/0.60  fof(f235,plain,(
% 1.64/0.60    spl12_21 <=> k1_xboole_0 = sK1),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 1.64/0.60  fof(f357,plain,(
% 1.64/0.60    ~sP11(k1_xboole_0) | (spl12_18 | ~spl12_21)),
% 1.64/0.60    inference(forward_demodulation,[],[f345,f85])).
% 1.64/0.60  fof(f85,plain,(
% 1.64/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.64/0.60    inference(equality_resolution,[],[f64])).
% 1.64/0.60  fof(f64,plain,(
% 1.64/0.60    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f6])).
% 1.64/0.60  fof(f6,axiom,(
% 1.64/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.64/0.60  fof(f345,plain,(
% 1.64/0.60    ~sP11(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl12_18 | ~spl12_21)),
% 1.64/0.60    inference(backward_demodulation,[],[f219,f237])).
% 1.64/0.60  fof(f237,plain,(
% 1.64/0.60    k1_xboole_0 = sK1 | ~spl12_21),
% 1.64/0.60    inference(avatar_component_clause,[],[f235])).
% 1.64/0.60  fof(f219,plain,(
% 1.64/0.60    ~sP11(k2_zfmisc_1(sK0,sK1)) | spl12_18),
% 1.64/0.60    inference(avatar_component_clause,[],[f217])).
% 1.64/0.60  fof(f329,plain,(
% 1.64/0.60    ~spl12_4 | spl12_24 | spl12_21 | ~spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f162,f131,f235,f326,f116])).
% 1.64/0.60  fof(f116,plain,(
% 1.64/0.60    spl12_4 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 1.64/0.60  fof(f162,plain,(
% 1.64/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f133,f73])).
% 1.64/0.60  fof(f73,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f32])).
% 1.64/0.60  fof(f32,plain,(
% 1.64/0.60    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(flattening,[],[f31])).
% 1.64/0.60  fof(f31,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f18])).
% 1.64/0.60  fof(f18,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.64/0.60  fof(f245,plain,(
% 1.64/0.60    ~spl12_6 | spl12_22 | ~spl12_20),
% 1.64/0.60    inference(avatar_split_clause,[],[f239,f231,f242,f126])).
% 1.64/0.60  fof(f231,plain,(
% 1.64/0.60    spl12_20 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 1.64/0.60  fof(f239,plain,(
% 1.64/0.60    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_20),
% 1.64/0.60    inference(superposition,[],[f233,f67])).
% 1.64/0.60  fof(f233,plain,(
% 1.64/0.60    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl12_20),
% 1.64/0.60    inference(avatar_component_clause,[],[f231])).
% 1.64/0.60  fof(f238,plain,(
% 1.64/0.60    ~spl12_3 | spl12_20 | spl12_21 | ~spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f137,f126,f235,f231,f111])).
% 1.64/0.60  fof(f111,plain,(
% 1.64/0.60    spl12_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 1.64/0.60  fof(f137,plain,(
% 1.64/0.60    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~v1_funct_2(sK3,sK0,sK1) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f128,f73])).
% 1.64/0.60  fof(f223,plain,(
% 1.64/0.60    ~spl12_18 | spl12_19 | ~spl12_10),
% 1.64/0.60    inference(avatar_split_clause,[],[f213,f156,f221,f217])).
% 1.64/0.60  fof(f156,plain,(
% 1.64/0.60    spl12_10 <=> r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).
% 1.64/0.60  fof(f213,plain,(
% 1.64/0.60    ( ! [X1] : (~r2_hidden(X1,sK3) | ~sP11(k2_zfmisc_1(sK0,sK1))) ) | ~spl12_10),
% 1.64/0.60    inference(resolution,[],[f176,f98])).
% 1.64/0.60  fof(f176,plain,(
% 1.64/0.60    ( ! [X0] : (r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r2_hidden(X0,sK3)) ) | ~spl12_10),
% 1.64/0.60    inference(resolution,[],[f158,f57])).
% 1.64/0.60  fof(f158,plain,(
% 1.64/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl12_10),
% 1.64/0.60    inference(avatar_component_clause,[],[f156])).
% 1.64/0.60  fof(f186,plain,(
% 1.64/0.60    spl12_13 | ~spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f168,f131,f183])).
% 1.64/0.60  fof(f168,plain,(
% 1.64/0.60    r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f133,f61])).
% 1.64/0.60  fof(f61,plain,(
% 1.64/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f9])).
% 1.64/0.60  fof(f9,axiom,(
% 1.64/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.64/0.60  fof(f181,plain,(
% 1.64/0.60    spl12_12 | ~spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f166,f131,f178])).
% 1.64/0.60  fof(f166,plain,(
% 1.64/0.60    r2_relset_1(sK0,sK1,sK2,sK2) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f133,f99])).
% 1.64/0.60  fof(f99,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.64/0.60    inference(duplicate_literal_removal,[],[f92])).
% 1.64/0.60  fof(f92,plain,(
% 1.64/0.60    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 1.64/0.60    inference(equality_resolution,[],[f83])).
% 1.64/0.60  fof(f83,plain,(
% 1.64/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f40])).
% 1.64/0.60  fof(f174,plain,(
% 1.64/0.60    spl12_11 | ~spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f160,f131,f171])).
% 1.64/0.60  fof(f160,plain,(
% 1.64/0.60    v1_relat_1(sK2) | ~spl12_7),
% 1.64/0.60    inference(resolution,[],[f133,f66])).
% 1.64/0.60  fof(f66,plain,(
% 1.64/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.64/0.60    inference(cnf_transformation,[],[f29])).
% 1.64/0.60  fof(f29,plain,(
% 1.64/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.64/0.60    inference(ennf_transformation,[],[f14])).
% 1.64/0.60  fof(f14,axiom,(
% 1.64/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.64/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.64/0.60  fof(f159,plain,(
% 1.64/0.60    spl12_10 | ~spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f143,f126,f156])).
% 1.64/0.60  fof(f143,plain,(
% 1.64/0.60    r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f128,f61])).
% 1.64/0.60  fof(f154,plain,(
% 1.64/0.60    spl12_9 | ~spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f141,f126,f151])).
% 1.64/0.60  fof(f141,plain,(
% 1.64/0.60    r2_relset_1(sK0,sK1,sK3,sK3) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f128,f99])).
% 1.64/0.60  fof(f149,plain,(
% 1.64/0.60    spl12_8 | ~spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f135,f126,f146])).
% 1.64/0.60  fof(f135,plain,(
% 1.64/0.60    v1_relat_1(sK3) | ~spl12_6),
% 1.64/0.60    inference(resolution,[],[f128,f66])).
% 1.64/0.60  fof(f134,plain,(
% 1.64/0.60    spl12_7),
% 1.64/0.60    inference(avatar_split_clause,[],[f48,f131])).
% 1.64/0.60  fof(f48,plain,(
% 1.64/0.60    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f129,plain,(
% 1.64/0.60    spl12_6),
% 1.64/0.60    inference(avatar_split_clause,[],[f44,f126])).
% 1.64/0.60  fof(f44,plain,(
% 1.64/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f124,plain,(
% 1.64/0.60    ~spl12_5),
% 1.64/0.60    inference(avatar_split_clause,[],[f45,f121])).
% 1.64/0.60  fof(f121,plain,(
% 1.64/0.60    spl12_5 <=> r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.64/0.60    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 1.64/0.60  fof(f45,plain,(
% 1.64/0.60    ~r2_relset_1(sK0,sK1,sK2,sK3)),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f119,plain,(
% 1.64/0.60    spl12_4),
% 1.64/0.60    inference(avatar_split_clause,[],[f47,f116])).
% 1.64/0.60  fof(f47,plain,(
% 1.64/0.60    v1_funct_2(sK2,sK0,sK1)),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f114,plain,(
% 1.64/0.60    spl12_3),
% 1.64/0.60    inference(avatar_split_clause,[],[f43,f111])).
% 1.64/0.60  fof(f43,plain,(
% 1.64/0.60    v1_funct_2(sK3,sK0,sK1)),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f109,plain,(
% 1.64/0.60    spl12_2),
% 1.64/0.60    inference(avatar_split_clause,[],[f46,f106])).
% 1.64/0.60  fof(f46,plain,(
% 1.64/0.60    v1_funct_1(sK2)),
% 1.64/0.60    inference(cnf_transformation,[],[f22])).
% 1.64/0.60  fof(f104,plain,(
% 1.64/0.60    spl12_1),
% 1.64/0.60    inference(avatar_split_clause,[],[f42,f101])).
% 1.64/0.60  % SZS output end Proof for theBenchmark
% 1.64/0.60  % (5864)------------------------------
% 1.64/0.60  % (5864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.60  % (5864)Termination reason: Refutation
% 1.64/0.60  
% 1.64/0.60  % (5864)Memory used [KB]: 11385
% 1.64/0.60  % (5864)Time elapsed: 0.161 s
% 1.64/0.60  % (5864)------------------------------
% 1.64/0.60  % (5864)------------------------------
% 1.64/0.60  % (5838)Success in time 0.236 s
%------------------------------------------------------------------------------
