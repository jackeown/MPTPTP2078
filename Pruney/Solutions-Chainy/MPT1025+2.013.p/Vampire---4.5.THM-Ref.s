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
% DateTime   : Thu Dec  3 13:06:23 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 285 expanded)
%              Number of leaves         :   40 ( 121 expanded)
%              Depth                    :   12
%              Number of atoms          :  606 (1215 expanded)
%              Number of equality atoms :  123 ( 246 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f538,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f125,f130,f142,f148,f159,f209,f265,f309,f330,f367,f372,f392,f401,f436,f444,f469,f482,f502,f504,f520,f534])).

fof(f534,plain,
    ( spl9_40
    | ~ spl9_46 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | spl9_40
    | ~ spl9_46 ),
    inference(unit_resulting_resolution,[],[f468,f519,f178])).

fof(f178,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | v5_relat_1(X3,X2) ) ),
    inference(superposition,[],[f98,f115])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f519,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_46 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl9_46
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).

fof(f468,plain,
    ( ~ v5_relat_1(sK3,sK4)
    | spl9_40 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl9_40
  <=> v5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f520,plain,
    ( spl9_46
    | ~ spl9_4
    | ~ spl9_32 ),
    inference(avatar_split_clause,[],[f512,f394,f139,f517])).

fof(f139,plain,
    ( spl9_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f394,plain,
    ( spl9_32
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f512,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl9_4
    | ~ spl9_32 ),
    inference(forward_demodulation,[],[f507,f114])).

fof(f114,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f507,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ spl9_4
    | ~ spl9_32 ),
    inference(backward_demodulation,[],[f141,f396])).

fof(f396,plain,
    ( k1_xboole_0 = sK1
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f394])).

fof(f141,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f504,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f502,plain,
    ( spl9_41
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f475,f461,f479])).

fof(f479,plain,
    ( spl9_41
  <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f461,plain,
    ( spl9_39
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f475,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_39 ),
    inference(resolution,[],[f463,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f463,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f461])).

fof(f482,plain,
    ( ~ spl9_41
    | ~ spl9_21
    | ~ spl9_29 ),
    inference(avatar_split_clause,[],[f376,f364,f306,f479])).

fof(f306,plain,
    ( spl9_21
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f364,plain,
    ( spl9_29
  <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).

fof(f376,plain,
    ( ~ m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_21
    | ~ spl9_29 ),
    inference(subsumption_resolution,[],[f375,f308])).

fof(f308,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f306])).

fof(f375,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_29 ),
    inference(trivial_inequality_removal,[],[f373])).

fof(f373,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_29 ),
    inference(superposition,[],[f66,f366])).

fof(f366,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl9_29 ),
    inference(avatar_component_clause,[],[f364])).

fof(f66,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ m1_subset_1(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ m1_subset_1(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ m1_subset_1(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).

fof(f469,plain,
    ( ~ spl9_40
    | ~ spl9_6
    | spl9_35 ),
    inference(avatar_split_clause,[],[f459,f433,f156,f466])).

fof(f156,plain,
    ( spl9_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f433,plain,
    ( spl9_35
  <=> r1_tarski(k2_relat_1(sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f459,plain,
    ( ~ v5_relat_1(sK3,sK4)
    | ~ spl9_6
    | spl9_35 ),
    inference(subsumption_resolution,[],[f458,f158])).

fof(f158,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f156])).

fof(f458,plain,
    ( ~ v5_relat_1(sK3,sK4)
    | ~ v1_relat_1(sK3)
    | spl9_35 ),
    inference(resolution,[],[f435,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f435,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK4)
    | spl9_35 ),
    inference(avatar_component_clause,[],[f433])).

fof(f444,plain,
    ( spl9_36
    | ~ spl9_11
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f437,f398,f206,f441])).

fof(f441,plain,
    ( spl9_36
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f206,plain,
    ( spl9_11
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f398,plain,
    ( spl9_33
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f437,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl9_11
    | ~ spl9_33 ),
    inference(forward_demodulation,[],[f208,f400])).

fof(f400,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f398])).

fof(f208,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f206])).

fof(f436,plain,
    ( ~ spl9_35
    | ~ spl9_31 ),
    inference(avatar_split_clause,[],[f427,f389,f433])).

fof(f389,plain,
    ( spl9_31
  <=> r2_hidden(sK4,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f427,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK4)
    | ~ spl9_31 ),
    inference(resolution,[],[f391,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f391,plain,
    ( r2_hidden(sK4,k2_relat_1(sK3))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f389])).

fof(f401,plain,
    ( spl9_32
    | spl9_33
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f253,f139,f127,f398,f394])).

fof(f127,plain,
    ( spl9_2
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f253,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ spl9_2
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f250,f141])).

fof(f250,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(resolution,[],[f99,f129])).

fof(f129,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f127])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f39])).

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

fof(f392,plain,
    ( spl9_31
    | ~ spl9_6
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f387,f369,f156,f389])).

fof(f369,plain,
    ( spl9_30
  <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f387,plain,
    ( r2_hidden(sK4,k2_relat_1(sK3))
    | ~ spl9_6
    | ~ spl9_30 ),
    inference(subsumption_resolution,[],[f381,f158])).

fof(f381,plain,
    ( r2_hidden(sK4,k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl9_30 ),
    inference(resolution,[],[f371,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k2_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).

fof(f371,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f369])).

fof(f372,plain,
    ( spl9_30
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f281,f262,f156,f369])).

fof(f262,plain,
    ( spl9_18
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f281,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f269,f158])).

fof(f269,plain,
    ( r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_18 ),
    inference(resolution,[],[f264,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK8(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
            & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK8(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2)
        & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f264,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f262])).

fof(f367,plain,
    ( spl9_29
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f276,f262,f156,f122,f364])).

fof(f122,plain,
    ( spl9_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f276,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f275,f158])).

fof(f275,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f266,f124])).

fof(f124,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f266,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_18 ),
    inference(resolution,[],[f264,f109])).

fof(f109,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f50,f49,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f330,plain,
    ( spl9_24
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f278,f262,f156,f122,f327])).

fof(f327,plain,
    ( spl9_24
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f278,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f277,f158])).

fof(f277,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f267,f124])).

fof(f267,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_18 ),
    inference(resolution,[],[f264,f111])).

fof(f111,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f309,plain,
    ( spl9_21
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f280,f262,f156,f122,f306])).

fof(f280,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl9_1
    | ~ spl9_6
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f279,f158])).

fof(f279,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ v1_relat_1(sK3)
    | ~ spl9_1
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f268,f124])).

fof(f268,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_18 ),
    inference(resolution,[],[f264,f110])).

fof(f110,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f265,plain,
    ( spl9_18
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f256,f145,f139,f262])).

fof(f145,plain,
    ( spl9_5
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f256,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_4
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f147,f211])).

fof(f211,plain,
    ( ! [X3] : k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)
    | ~ spl9_4 ),
    inference(resolution,[],[f106,f141])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f147,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f209,plain,
    ( spl9_11
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f201,f139,f206])).

fof(f201,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_4 ),
    inference(resolution,[],[f96,f141])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f159,plain,
    ( spl9_6
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f152,f139,f156])).

fof(f152,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_4 ),
    inference(resolution,[],[f95,f141])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f148,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f65,f145])).

fof(f65,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f64,f139])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f130,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f63,f127])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f125,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f62,f122])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n015.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 11:31:08 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.47  % (28488)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.47  % (28472)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.54  % (28468)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.54  % (28466)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.65/0.55  % (28470)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.65/0.55  % (28477)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.65/0.55  % (28467)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.65/0.55  % (28469)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.65/0.56  % (28476)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.65/0.56  % (28480)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.65/0.56  % (28487)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.65/0.56  % (28479)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.65/0.56  % (28484)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.65/0.56  % (28486)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.65/0.56  % (28485)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.65/0.56  % (28465)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.65/0.56  % (28483)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.65/0.56  % (28478)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.65/0.57  % (28471)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.75/0.57  % (28475)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.75/0.58  % (28482)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.75/0.58  % (28467)Refutation found. Thanks to Tanya!
% 1.75/0.58  % SZS status Theorem for theBenchmark
% 1.75/0.58  % SZS output start Proof for theBenchmark
% 1.75/0.58  fof(f538,plain,(
% 1.75/0.58    $false),
% 1.75/0.58    inference(avatar_sat_refutation,[],[f125,f130,f142,f148,f159,f209,f265,f309,f330,f367,f372,f392,f401,f436,f444,f469,f482,f502,f504,f520,f534])).
% 1.75/0.58  fof(f534,plain,(
% 1.75/0.58    spl9_40 | ~spl9_46),
% 1.75/0.58    inference(avatar_contradiction_clause,[],[f526])).
% 1.75/0.58  fof(f526,plain,(
% 1.75/0.58    $false | (spl9_40 | ~spl9_46)),
% 1.75/0.58    inference(unit_resulting_resolution,[],[f468,f519,f178])).
% 1.75/0.58  fof(f178,plain,(
% 1.75/0.58    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | v5_relat_1(X3,X2)) )),
% 1.75/0.58    inference(superposition,[],[f98,f115])).
% 1.75/0.58  fof(f115,plain,(
% 1.75/0.58    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 1.75/0.58    inference(equality_resolution,[],[f86])).
% 1.75/0.58  fof(f86,plain,(
% 1.75/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.75/0.58    inference(cnf_transformation,[],[f56])).
% 1.75/0.58  fof(f56,plain,(
% 1.75/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.75/0.58    inference(flattening,[],[f55])).
% 1.75/0.58  fof(f55,plain,(
% 1.75/0.58    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.75/0.58    inference(nnf_transformation,[],[f2])).
% 1.75/0.58  fof(f2,axiom,(
% 1.75/0.58    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.75/0.58  fof(f98,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f37])).
% 1.75/0.58  fof(f37,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f15])).
% 1.75/0.58  fof(f15,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.75/0.58  fof(f519,plain,(
% 1.75/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | ~spl9_46),
% 1.75/0.58    inference(avatar_component_clause,[],[f517])).
% 1.75/0.58  fof(f517,plain,(
% 1.75/0.58    spl9_46 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_46])])).
% 1.75/0.58  fof(f468,plain,(
% 1.75/0.58    ~v5_relat_1(sK3,sK4) | spl9_40),
% 1.75/0.58    inference(avatar_component_clause,[],[f466])).
% 1.75/0.58  fof(f466,plain,(
% 1.75/0.58    spl9_40 <=> v5_relat_1(sK3,sK4)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 1.75/0.58  fof(f520,plain,(
% 1.75/0.58    spl9_46 | ~spl9_4 | ~spl9_32),
% 1.75/0.58    inference(avatar_split_clause,[],[f512,f394,f139,f517])).
% 1.75/0.58  fof(f139,plain,(
% 1.75/0.58    spl9_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.75/0.58  fof(f394,plain,(
% 1.75/0.58    spl9_32 <=> k1_xboole_0 = sK1),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 1.75/0.58  fof(f512,plain,(
% 1.75/0.58    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl9_4 | ~spl9_32)),
% 1.75/0.58    inference(forward_demodulation,[],[f507,f114])).
% 1.75/0.58  fof(f114,plain,(
% 1.75/0.58    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.75/0.58    inference(equality_resolution,[],[f87])).
% 1.75/0.58  fof(f87,plain,(
% 1.75/0.58    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 1.75/0.58    inference(cnf_transformation,[],[f56])).
% 1.75/0.58  fof(f507,plain,(
% 1.75/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) | (~spl9_4 | ~spl9_32)),
% 1.75/0.58    inference(backward_demodulation,[],[f141,f396])).
% 1.75/0.58  fof(f396,plain,(
% 1.75/0.58    k1_xboole_0 = sK1 | ~spl9_32),
% 1.75/0.58    inference(avatar_component_clause,[],[f394])).
% 1.75/0.58  fof(f141,plain,(
% 1.75/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_4),
% 1.75/0.58    inference(avatar_component_clause,[],[f139])).
% 1.75/0.58  fof(f504,plain,(
% 1.75/0.58    sK0 != k1_relat_1(sK3) | r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.75/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.75/0.58  fof(f502,plain,(
% 1.75/0.58    spl9_41 | ~spl9_39),
% 1.75/0.58    inference(avatar_split_clause,[],[f475,f461,f479])).
% 1.75/0.58  fof(f479,plain,(
% 1.75/0.58    spl9_41 <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 1.75/0.58  fof(f461,plain,(
% 1.75/0.58    spl9_39 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 1.75/0.58  fof(f475,plain,(
% 1.75/0.58    m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl9_39),
% 1.75/0.58    inference(resolution,[],[f463,f79])).
% 1.75/0.58  fof(f79,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f26])).
% 1.75/0.58  fof(f26,plain,(
% 1.75/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.75/0.58    inference(ennf_transformation,[],[f4])).
% 1.75/0.58  fof(f4,axiom,(
% 1.75/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 1.75/0.58  fof(f463,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl9_39),
% 1.75/0.58    inference(avatar_component_clause,[],[f461])).
% 1.75/0.58  fof(f482,plain,(
% 1.75/0.58    ~spl9_41 | ~spl9_21 | ~spl9_29),
% 1.75/0.58    inference(avatar_split_clause,[],[f376,f364,f306,f479])).
% 1.75/0.58  fof(f306,plain,(
% 1.75/0.58    spl9_21 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 1.75/0.58  fof(f364,plain,(
% 1.75/0.58    spl9_29 <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_29])])).
% 1.75/0.58  fof(f376,plain,(
% 1.75/0.58    ~m1_subset_1(sK7(sK3,sK2,sK4),sK0) | (~spl9_21 | ~spl9_29)),
% 1.75/0.58    inference(subsumption_resolution,[],[f375,f308])).
% 1.75/0.58  fof(f308,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl9_21),
% 1.75/0.58    inference(avatar_component_clause,[],[f306])).
% 1.75/0.58  fof(f375,plain,(
% 1.75/0.58    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl9_29),
% 1.75/0.58    inference(trivial_inequality_removal,[],[f373])).
% 1.75/0.58  fof(f373,plain,(
% 1.75/0.58    sK4 != sK4 | ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl9_29),
% 1.75/0.58    inference(superposition,[],[f66,f366])).
% 1.75/0.58  fof(f366,plain,(
% 1.75/0.58    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl9_29),
% 1.75/0.58    inference(avatar_component_clause,[],[f364])).
% 1.75/0.58  fof(f66,plain,(
% 1.75/0.58    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f45])).
% 1.75/0.58  fof(f45,plain,(
% 1.75/0.58    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.75/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f22,f44,f43])).
% 1.75/0.58  fof(f43,plain,(
% 1.75/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f44,plain,(
% 1.75/0.58    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f22,plain,(
% 1.75/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.75/0.58    inference(flattening,[],[f21])).
% 1.75/0.58  fof(f21,plain,(
% 1.75/0.58    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.75/0.58    inference(ennf_transformation,[],[f20])).
% 1.75/0.58  fof(f20,negated_conjecture,(
% 1.75/0.58    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.75/0.58    inference(negated_conjecture,[],[f19])).
% 1.75/0.58  fof(f19,conjecture,(
% 1.75/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 1.75/0.58  fof(f469,plain,(
% 1.75/0.58    ~spl9_40 | ~spl9_6 | spl9_35),
% 1.75/0.58    inference(avatar_split_clause,[],[f459,f433,f156,f466])).
% 1.75/0.58  fof(f156,plain,(
% 1.75/0.58    spl9_6 <=> v1_relat_1(sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.75/0.58  fof(f433,plain,(
% 1.75/0.58    spl9_35 <=> r1_tarski(k2_relat_1(sK3),sK4)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 1.75/0.58  fof(f459,plain,(
% 1.75/0.58    ~v5_relat_1(sK3,sK4) | (~spl9_6 | spl9_35)),
% 1.75/0.58    inference(subsumption_resolution,[],[f458,f158])).
% 1.75/0.58  fof(f158,plain,(
% 1.75/0.58    v1_relat_1(sK3) | ~spl9_6),
% 1.75/0.58    inference(avatar_component_clause,[],[f156])).
% 1.75/0.58  fof(f458,plain,(
% 1.75/0.58    ~v5_relat_1(sK3,sK4) | ~v1_relat_1(sK3) | spl9_35),
% 1.75/0.58    inference(resolution,[],[f435,f77])).
% 1.75/0.58  fof(f77,plain,(
% 1.75/0.58    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f52])).
% 1.75/0.58  fof(f52,plain,(
% 1.75/0.58    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(nnf_transformation,[],[f25])).
% 1.75/0.58  fof(f25,plain,(
% 1.75/0.58    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.75/0.58    inference(ennf_transformation,[],[f7])).
% 1.75/0.58  fof(f7,axiom,(
% 1.75/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.75/0.58  fof(f435,plain,(
% 1.75/0.58    ~r1_tarski(k2_relat_1(sK3),sK4) | spl9_35),
% 1.75/0.58    inference(avatar_component_clause,[],[f433])).
% 1.75/0.58  fof(f444,plain,(
% 1.75/0.58    spl9_36 | ~spl9_11 | ~spl9_33),
% 1.75/0.58    inference(avatar_split_clause,[],[f437,f398,f206,f441])).
% 1.75/0.58  fof(f441,plain,(
% 1.75/0.58    spl9_36 <=> sK0 = k1_relat_1(sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 1.75/0.58  fof(f206,plain,(
% 1.75/0.58    spl9_11 <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.75/0.58  fof(f398,plain,(
% 1.75/0.58    spl9_33 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 1.75/0.58  fof(f437,plain,(
% 1.75/0.58    sK0 = k1_relat_1(sK3) | (~spl9_11 | ~spl9_33)),
% 1.75/0.58    inference(forward_demodulation,[],[f208,f400])).
% 1.75/0.58  fof(f400,plain,(
% 1.75/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_33),
% 1.75/0.58    inference(avatar_component_clause,[],[f398])).
% 1.75/0.58  fof(f208,plain,(
% 1.75/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl9_11),
% 1.75/0.58    inference(avatar_component_clause,[],[f206])).
% 1.75/0.58  fof(f436,plain,(
% 1.75/0.58    ~spl9_35 | ~spl9_31),
% 1.75/0.58    inference(avatar_split_clause,[],[f427,f389,f433])).
% 1.75/0.58  fof(f389,plain,(
% 1.75/0.58    spl9_31 <=> r2_hidden(sK4,k2_relat_1(sK3))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 1.75/0.58  fof(f427,plain,(
% 1.75/0.58    ~r1_tarski(k2_relat_1(sK3),sK4) | ~spl9_31),
% 1.75/0.58    inference(resolution,[],[f391,f88])).
% 1.75/0.58  fof(f88,plain,(
% 1.75/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f31])).
% 1.75/0.58  fof(f31,plain,(
% 1.75/0.58    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.75/0.58    inference(ennf_transformation,[],[f13])).
% 1.75/0.58  fof(f13,axiom,(
% 1.75/0.58    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.75/0.58  fof(f391,plain,(
% 1.75/0.58    r2_hidden(sK4,k2_relat_1(sK3)) | ~spl9_31),
% 1.75/0.58    inference(avatar_component_clause,[],[f389])).
% 1.75/0.58  fof(f401,plain,(
% 1.75/0.58    spl9_32 | spl9_33 | ~spl9_2 | ~spl9_4),
% 1.75/0.58    inference(avatar_split_clause,[],[f253,f139,f127,f398,f394])).
% 1.75/0.58  fof(f127,plain,(
% 1.75/0.58    spl9_2 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.75/0.58  fof(f253,plain,(
% 1.75/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | (~spl9_2 | ~spl9_4)),
% 1.75/0.58    inference(subsumption_resolution,[],[f250,f141])).
% 1.75/0.58  fof(f250,plain,(
% 1.75/0.58    sK0 = k1_relset_1(sK0,sK1,sK3) | k1_xboole_0 = sK1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_2),
% 1.75/0.58    inference(resolution,[],[f99,f129])).
% 1.75/0.58  fof(f129,plain,(
% 1.75/0.58    v1_funct_2(sK3,sK0,sK1) | ~spl9_2),
% 1.75/0.58    inference(avatar_component_clause,[],[f127])).
% 1.75/0.58  fof(f99,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.75/0.58    inference(cnf_transformation,[],[f61])).
% 1.75/0.58  fof(f61,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(nnf_transformation,[],[f39])).
% 1.75/0.58  fof(f39,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(flattening,[],[f38])).
% 1.75/0.58  fof(f38,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f18])).
% 1.75/0.58  fof(f18,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.75/0.58  fof(f392,plain,(
% 1.75/0.58    spl9_31 | ~spl9_6 | ~spl9_30),
% 1.75/0.58    inference(avatar_split_clause,[],[f387,f369,f156,f389])).
% 1.75/0.58  fof(f369,plain,(
% 1.75/0.58    spl9_30 <=> r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 1.75/0.58  fof(f387,plain,(
% 1.75/0.58    r2_hidden(sK4,k2_relat_1(sK3)) | (~spl9_6 | ~spl9_30)),
% 1.75/0.58    inference(subsumption_resolution,[],[f381,f158])).
% 1.75/0.58  fof(f381,plain,(
% 1.75/0.58    r2_hidden(sK4,k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~spl9_30),
% 1.75/0.58    inference(resolution,[],[f371,f90])).
% 1.75/0.58  fof(f90,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k2_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f33])).
% 1.75/0.58  fof(f33,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(flattening,[],[f32])).
% 1.75/0.58  fof(f32,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(ennf_transformation,[],[f11])).
% 1.75/0.58  fof(f11,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_relat_1)).
% 1.75/0.58  fof(f371,plain,(
% 1.75/0.58    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~spl9_30),
% 1.75/0.58    inference(avatar_component_clause,[],[f369])).
% 1.75/0.58  fof(f372,plain,(
% 1.75/0.58    spl9_30 | ~spl9_6 | ~spl9_18),
% 1.75/0.58    inference(avatar_split_clause,[],[f281,f262,f156,f369])).
% 1.75/0.58  fof(f262,plain,(
% 1.75/0.58    spl9_18 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 1.75/0.58  fof(f281,plain,(
% 1.75/0.58    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | (~spl9_6 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f269,f158])).
% 1.75/0.58  fof(f269,plain,(
% 1.75/0.58    r2_hidden(k4_tarski(sK8(sK4,sK2,sK3),sK4),sK3) | ~v1_relat_1(sK3) | ~spl9_18),
% 1.75/0.58    inference(resolution,[],[f264,f92])).
% 1.75/0.58  fof(f92,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,k9_relat_1(X2,X1)) | r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) | ~v1_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f60])).
% 1.75/0.58  fof(f60,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).
% 1.75/0.58  fof(f59,plain,(
% 1.75/0.58    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK8(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X2),X0),X2) & r2_hidden(sK8(X0,X1,X2),k1_relat_1(X2))))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f58,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(rectify,[],[f57])).
% 1.75/0.58  fof(f57,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(nnf_transformation,[],[f34])).
% 1.75/0.58  fof(f34,plain,(
% 1.75/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.75/0.58    inference(ennf_transformation,[],[f9])).
% 1.75/0.58  fof(f9,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 1.75/0.58  fof(f264,plain,(
% 1.75/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl9_18),
% 1.75/0.58    inference(avatar_component_clause,[],[f262])).
% 1.75/0.58  fof(f367,plain,(
% 1.75/0.58    spl9_29 | ~spl9_1 | ~spl9_6 | ~spl9_18),
% 1.75/0.58    inference(avatar_split_clause,[],[f276,f262,f156,f122,f364])).
% 1.75/0.58  fof(f122,plain,(
% 1.75/0.58    spl9_1 <=> v1_funct_1(sK3)),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.75/0.58  fof(f276,plain,(
% 1.75/0.58    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl9_1 | ~spl9_6 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f275,f158])).
% 1.75/0.58  fof(f275,plain,(
% 1.75/0.58    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f266,f124])).
% 1.75/0.58  fof(f124,plain,(
% 1.75/0.58    v1_funct_1(sK3) | ~spl9_1),
% 1.75/0.58    inference(avatar_component_clause,[],[f122])).
% 1.75/0.58  fof(f266,plain,(
% 1.75/0.58    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl9_18),
% 1.75/0.58    inference(resolution,[],[f264,f109])).
% 1.75/0.58  fof(f109,plain,(
% 1.75/0.58    ( ! [X6,X0,X1] : (~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(equality_resolution,[],[f70])).
% 1.75/0.58  fof(f70,plain,(
% 1.75/0.58    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f51])).
% 1.75/0.58  fof(f51,plain,(
% 1.75/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f50,f49,f48])).
% 1.75/0.58  fof(f48,plain,(
% 1.75/0.58    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK5(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f49,plain,(
% 1.75/0.58    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK5(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2)) & r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0))))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f50,plain,(
% 1.75/0.58    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK7(X0,X1,X6)) = X6 & r2_hidden(sK7(X0,X1,X6),X1) & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))))),
% 1.75/0.58    introduced(choice_axiom,[])).
% 1.75/0.58  fof(f47,plain,(
% 1.75/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(rectify,[],[f46])).
% 1.75/0.58  fof(f46,plain,(
% 1.75/0.58    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(nnf_transformation,[],[f24])).
% 1.75/0.58  fof(f24,plain,(
% 1.75/0.58    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.75/0.58    inference(flattening,[],[f23])).
% 1.75/0.58  fof(f23,plain,(
% 1.75/0.58    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.75/0.58    inference(ennf_transformation,[],[f12])).
% 1.75/0.58  fof(f12,axiom,(
% 1.75/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).
% 1.75/0.58  fof(f330,plain,(
% 1.75/0.58    spl9_24 | ~spl9_1 | ~spl9_6 | ~spl9_18),
% 1.75/0.58    inference(avatar_split_clause,[],[f278,f262,f156,f122,f327])).
% 1.75/0.58  fof(f327,plain,(
% 1.75/0.58    spl9_24 <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.75/0.58  fof(f278,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | (~spl9_1 | ~spl9_6 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f277,f158])).
% 1.75/0.58  fof(f277,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f267,f124])).
% 1.75/0.58  fof(f267,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl9_18),
% 1.75/0.58    inference(resolution,[],[f264,f111])).
% 1.75/0.58  fof(f111,plain,(
% 1.75/0.58    ( ! [X6,X0,X1] : (~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(equality_resolution,[],[f68])).
% 1.75/0.58  fof(f68,plain,(
% 1.75/0.58    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f51])).
% 1.75/0.58  fof(f309,plain,(
% 1.75/0.58    spl9_21 | ~spl9_1 | ~spl9_6 | ~spl9_18),
% 1.75/0.58    inference(avatar_split_clause,[],[f280,f262,f156,f122,f306])).
% 1.75/0.58  fof(f280,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),sK2) | (~spl9_1 | ~spl9_6 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f279,f158])).
% 1.75/0.58  fof(f279,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~v1_relat_1(sK3) | (~spl9_1 | ~spl9_18)),
% 1.75/0.58    inference(subsumption_resolution,[],[f268,f124])).
% 1.75/0.58  fof(f268,plain,(
% 1.75/0.58    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl9_18),
% 1.75/0.58    inference(resolution,[],[f264,f110])).
% 1.75/0.58  fof(f110,plain,(
% 1.75/0.58    ( ! [X6,X0,X1] : (~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK7(X0,X1,X6),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(equality_resolution,[],[f69])).
% 1.75/0.58  fof(f69,plain,(
% 1.75/0.58    ( ! [X6,X2,X0,X1] : (r2_hidden(sK7(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f51])).
% 1.75/0.58  fof(f265,plain,(
% 1.75/0.58    spl9_18 | ~spl9_4 | ~spl9_5),
% 1.75/0.58    inference(avatar_split_clause,[],[f256,f145,f139,f262])).
% 1.75/0.58  fof(f145,plain,(
% 1.75/0.58    spl9_5 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.75/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.75/0.58  fof(f256,plain,(
% 1.75/0.58    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl9_4 | ~spl9_5)),
% 1.75/0.58    inference(backward_demodulation,[],[f147,f211])).
% 1.75/0.58  fof(f211,plain,(
% 1.75/0.58    ( ! [X3] : (k7_relset_1(sK0,sK1,sK3,X3) = k9_relat_1(sK3,X3)) ) | ~spl9_4),
% 1.75/0.58    inference(resolution,[],[f106,f141])).
% 1.75/0.58  fof(f106,plain,(
% 1.75/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f42])).
% 1.75/0.58  fof(f42,plain,(
% 1.75/0.58    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f17])).
% 1.75/0.58  fof(f17,axiom,(
% 1.75/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.75/0.58  fof(f147,plain,(
% 1.75/0.58    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl9_5),
% 1.75/0.58    inference(avatar_component_clause,[],[f145])).
% 1.75/0.58  fof(f209,plain,(
% 1.75/0.58    spl9_11 | ~spl9_4),
% 1.75/0.58    inference(avatar_split_clause,[],[f201,f139,f206])).
% 1.75/0.58  fof(f201,plain,(
% 1.75/0.58    k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) | ~spl9_4),
% 1.75/0.58    inference(resolution,[],[f96,f141])).
% 1.75/0.58  fof(f96,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(X2) = k1_relset_1(X0,X1,X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f36])).
% 1.75/0.58  fof(f36,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f16])).
% 1.75/0.58  fof(f16,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.75/0.58  fof(f159,plain,(
% 1.75/0.58    spl9_6 | ~spl9_4),
% 1.75/0.58    inference(avatar_split_clause,[],[f152,f139,f156])).
% 1.75/0.58  fof(f152,plain,(
% 1.75/0.58    v1_relat_1(sK3) | ~spl9_4),
% 1.75/0.58    inference(resolution,[],[f95,f141])).
% 1.75/0.58  fof(f95,plain,(
% 1.75/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.75/0.58    inference(cnf_transformation,[],[f35])).
% 1.75/0.58  fof(f35,plain,(
% 1.75/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.75/0.58    inference(ennf_transformation,[],[f14])).
% 1.75/0.58  fof(f14,axiom,(
% 1.75/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.75/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.75/0.58  fof(f148,plain,(
% 1.75/0.58    spl9_5),
% 1.75/0.58    inference(avatar_split_clause,[],[f65,f145])).
% 1.75/0.58  fof(f65,plain,(
% 1.75/0.58    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.75/0.58    inference(cnf_transformation,[],[f45])).
% 1.75/0.58  fof(f142,plain,(
% 1.75/0.58    spl9_4),
% 1.75/0.58    inference(avatar_split_clause,[],[f64,f139])).
% 1.75/0.58  fof(f64,plain,(
% 1.75/0.58    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.75/0.58    inference(cnf_transformation,[],[f45])).
% 1.75/0.58  fof(f130,plain,(
% 1.75/0.58    spl9_2),
% 1.75/0.58    inference(avatar_split_clause,[],[f63,f127])).
% 1.75/0.58  fof(f63,plain,(
% 1.75/0.58    v1_funct_2(sK3,sK0,sK1)),
% 1.75/0.58    inference(cnf_transformation,[],[f45])).
% 1.75/0.58  fof(f125,plain,(
% 1.75/0.58    spl9_1),
% 1.75/0.58    inference(avatar_split_clause,[],[f62,f122])).
% 1.75/0.58  fof(f62,plain,(
% 1.75/0.58    v1_funct_1(sK3)),
% 1.75/0.58    inference(cnf_transformation,[],[f45])).
% 1.75/0.58  % SZS output end Proof for theBenchmark
% 1.75/0.58  % (28467)------------------------------
% 1.75/0.58  % (28467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.58  % (28467)Termination reason: Refutation
% 1.75/0.58  
% 1.75/0.58  % (28467)Memory used [KB]: 6524
% 1.75/0.58  % (28467)Time elapsed: 0.153 s
% 1.75/0.58  % (28467)------------------------------
% 1.75/0.58  % (28467)------------------------------
% 1.75/0.59  % (28464)Success in time 0.245 s
%------------------------------------------------------------------------------
