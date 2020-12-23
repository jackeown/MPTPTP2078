%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:06:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 232 expanded)
%              Number of leaves         :   36 ( 104 expanded)
%              Depth                    :   10
%              Number of atoms          :  502 (1062 expanded)
%              Number of equality atoms :   97 ( 208 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f595,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f119,f123,f127,f131,f142,f153,f193,f202,f329,f336,f358,f369,f377,f389,f393,f557,f564,f591,f592,f594])).

fof(f594,plain,(
    ~ spl12_59 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | ~ spl12_59 ),
    inference(resolution,[],[f590,f132])).

fof(f132,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f86,f67])).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f590,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl12_59 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl12_59
  <=> r2_hidden(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f592,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK10(sK3,sK2,sK4),sK0)
    | ~ r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f591,plain,
    ( spl12_59
    | ~ spl12_25
    | ~ spl12_53 ),
    inference(avatar_split_clause,[],[f571,f554,f356,f589])).

fof(f356,plain,
    ( spl12_25
  <=> r2_hidden(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).

fof(f554,plain,
    ( spl12_53
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).

fof(f571,plain,
    ( r2_hidden(sK4,k1_xboole_0)
    | ~ spl12_25
    | ~ spl12_53 ),
    inference(superposition,[],[f357,f555])).

fof(f555,plain,
    ( k1_xboole_0 = sK1
    | ~ spl12_53 ),
    inference(avatar_component_clause,[],[f554])).

fof(f357,plain,
    ( r2_hidden(sK4,sK1)
    | ~ spl12_25 ),
    inference(avatar_component_clause,[],[f356])).

fof(f564,plain,
    ( ~ spl12_2
    | spl12_54
    | ~ spl12_52 ),
    inference(avatar_split_clause,[],[f559,f551,f561,f121])).

fof(f121,plain,
    ( spl12_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f561,plain,
    ( spl12_54
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f551,plain,
    ( spl12_52
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).

fof(f559,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_52 ),
    inference(superposition,[],[f92,f552])).

fof(f552,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl12_52 ),
    inference(avatar_component_clause,[],[f551])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f557,plain,
    ( spl12_52
    | spl12_53
    | ~ spl12_3
    | ~ spl12_2 ),
    inference(avatar_split_clause,[],[f549,f121,f125,f554,f551])).

fof(f125,plain,
    ( spl12_3
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f549,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl12_2 ),
    inference(resolution,[],[f94,f122])).

fof(f122,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f121])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
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
    inference(nnf_transformation,[],[f38])).

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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f393,plain,
    ( ~ spl12_6
    | ~ spl12_4
    | ~ spl12_5
    | spl12_23 ),
    inference(avatar_split_clause,[],[f391,f349,f140,f129,f145])).

fof(f145,plain,
    ( spl12_6
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f129,plain,
    ( spl12_4
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f140,plain,
    ( spl12_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).

% (30681)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
fof(f349,plain,
    ( spl12_23
  <=> r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).

fof(f391,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl12_23 ),
    inference(resolution,[],[f350,f110])).

fof(f110,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK8(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK8(X0,X1,X2),X2) )
              & ( ( sK8(X0,X1,X2) = k1_funct_1(X0,sK9(X0,X1,X2))
                  & r2_hidden(sK9(X0,X1,X2),X1)
                  & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
                    & r2_hidden(sK10(X0,X1,X6),X1)
                    & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f52,f55,f54,f53])).

fof(f53,plain,(
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
              ( k1_funct_1(X0,X4) != sK8(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK8(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK8(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK8(X0,X1,X2) = k1_funct_1(X0,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
        & r2_hidden(sK10(X0,X1,X6),X1)
        & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f350,plain,
    ( ~ r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3))
    | spl12_23 ),
    inference(avatar_component_clause,[],[f349])).

fof(f389,plain,
    ( ~ spl12_32
    | spl12_27 ),
    inference(avatar_split_clause,[],[f385,f364,f387])).

fof(f387,plain,
    ( spl12_32
  <=> r2_hidden(sK10(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f364,plain,
    ( spl12_27
  <=> m1_subset_1(sK10(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f385,plain,
    ( ~ r2_hidden(sK10(sK3,sK2,sK4),sK0)
    | spl12_27 ),
    inference(resolution,[],[f365,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f365,plain,
    ( ~ m1_subset_1(sK10(sK3,sK2,sK4),sK0)
    | spl12_27 ),
    inference(avatar_component_clause,[],[f364])).

fof(f377,plain,
    ( ~ spl12_5
    | ~ spl12_15
    | spl12_28 ),
    inference(avatar_split_clause,[],[f374,f367,f191,f140])).

fof(f191,plain,
    ( spl12_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK10(sK3,X1,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f367,plain,
    ( spl12_28
  <=> r2_hidden(sK10(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f374,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl12_15
    | spl12_28 ),
    inference(resolution,[],[f368,f192])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK10(sK3,X1,X0),X1)
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f191])).

fof(f368,plain,
    ( ~ r2_hidden(sK10(sK3,sK2,sK4),sK2)
    | spl12_28 ),
    inference(avatar_component_clause,[],[f367])).

fof(f369,plain,
    ( ~ spl12_27
    | ~ spl12_28
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f347,f334,f367,f364])).

fof(f334,plain,
    ( spl12_21
  <=> sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).

fof(f347,plain,
    ( ~ r2_hidden(sK10(sK3,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK3,sK2,sK4),sK0)
    | ~ spl12_21 ),
    inference(trivial_inequality_removal,[],[f345])).

fof(f345,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK10(sK3,sK2,sK4),sK2)
    | ~ m1_subset_1(sK10(sK3,sK2,sK4),sK0)
    | ~ spl12_21 ),
    inference(superposition,[],[f66,f335])).

fof(f335,plain,
    ( sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4))
    | ~ spl12_21 ),
    inference(avatar_component_clause,[],[f334])).

fof(f66,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ m1_subset_1(X5,sK0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ m1_subset_1(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).

fof(f358,plain,
    ( ~ spl12_23
    | spl12_25
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_21 ),
    inference(avatar_split_clause,[],[f343,f334,f200,f121,f356,f349])).

fof(f200,plain,
    ( spl12_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | ~ v5_relat_1(sK3,X1)
        | r2_hidden(k1_funct_1(sK3,X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f343,plain,
    ( r2_hidden(sK4,sK1)
    | ~ r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl12_2
    | ~ spl12_16
    | ~ spl12_21 ),
    inference(superposition,[],[f212,f335])).

fof(f212,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK1)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl12_2
    | ~ spl12_16 ),
    inference(resolution,[],[f209,f122])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl12_16 ),
    inference(resolution,[],[f201,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(sK3,X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),X1) )
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f200])).

fof(f336,plain,
    ( spl12_21
    | ~ spl12_5
    | ~ spl12_20 ),
    inference(avatar_split_clause,[],[f331,f327,f140,f334])).

fof(f327,plain,
    ( spl12_20
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).

fof(f331,plain,
    ( sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4))
    | ~ spl12_5
    | ~ spl12_20 ),
    inference(resolution,[],[f328,f141])).

fof(f141,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl12_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0 )
    | ~ spl12_20 ),
    inference(avatar_component_clause,[],[f327])).

fof(f329,plain,
    ( ~ spl12_6
    | spl12_20
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f325,f129,f327,f145])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl12_4 ),
    inference(resolution,[],[f108,f130])).

fof(f130,plain,
    ( v1_funct_1(sK3)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f129])).

fof(f108,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK10(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK10(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f202,plain,
    ( ~ spl12_6
    | spl12_16
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f198,f129,f200,f145])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ v5_relat_1(sK3,X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl12_4 ),
    inference(resolution,[],[f85,f130])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

fof(f193,plain,
    ( ~ spl12_6
    | spl12_15
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f189,f129,f191,f145])).

fof(f189,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | r2_hidden(sK10(sK3,X1,X0),X1)
        | ~ v1_relat_1(sK3) )
    | ~ spl12_4 ),
    inference(resolution,[],[f109,f130])).

fof(f109,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | r2_hidden(sK10(X0,X1,X6),X1)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK10(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f153,plain,
    ( ~ spl12_2
    | spl12_6 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl12_2
    | spl12_6 ),
    inference(subsumption_resolution,[],[f122,f151])).

fof(f151,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl12_6 ),
    inference(resolution,[],[f146,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f146,plain,
    ( ~ v1_relat_1(sK3)
    | spl12_6 ),
    inference(avatar_component_clause,[],[f145])).

fof(f142,plain,
    ( ~ spl12_2
    | spl12_5
    | ~ spl12_1 ),
    inference(avatar_split_clause,[],[f137,f117,f140,f121])).

fof(f117,plain,
    ( spl12_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f137,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl12_1 ),
    inference(superposition,[],[f118,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f118,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f117])).

fof(f131,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f62,f129])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f127,plain,(
    spl12_3 ),
    inference(avatar_split_clause,[],[f63,f125])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f123,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f64,f121])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f119,plain,(
    spl12_1 ),
    inference(avatar_split_clause,[],[f65,f117])).

fof(f65,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:43:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (30674)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (30682)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (30672)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (30670)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (30673)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (30678)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (30674)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f595,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f119,f123,f127,f131,f142,f153,f193,f202,f329,f336,f358,f369,f377,f389,f393,f557,f564,f591,f592,f594])).
% 0.21/0.52  fof(f594,plain,(
% 0.21/0.52    ~spl12_59),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f593])).
% 0.21/0.52  fof(f593,plain,(
% 0.21/0.52    $false | ~spl12_59),
% 0.21/0.52    inference(resolution,[],[f590,f132])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(resolution,[],[f86,f67])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.52  fof(f590,plain,(
% 0.21/0.52    r2_hidden(sK4,k1_xboole_0) | ~spl12_59),
% 0.21/0.52    inference(avatar_component_clause,[],[f589])).
% 0.21/0.52  fof(f589,plain,(
% 0.21/0.52    spl12_59 <=> r2_hidden(sK4,k1_xboole_0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).
% 0.21/0.52  fof(f592,plain,(
% 0.21/0.52    sK0 != k1_relat_1(sK3) | r2_hidden(sK10(sK3,sK2,sK4),sK0) | ~r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f591,plain,(
% 0.21/0.52    spl12_59 | ~spl12_25 | ~spl12_53),
% 0.21/0.52    inference(avatar_split_clause,[],[f571,f554,f356,f589])).
% 0.21/0.52  fof(f356,plain,(
% 0.21/0.52    spl12_25 <=> r2_hidden(sK4,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_25])])).
% 0.21/0.52  fof(f554,plain,(
% 0.21/0.52    spl12_53 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_53])])).
% 0.21/0.52  fof(f571,plain,(
% 0.21/0.52    r2_hidden(sK4,k1_xboole_0) | (~spl12_25 | ~spl12_53)),
% 0.21/0.52    inference(superposition,[],[f357,f555])).
% 0.21/0.52  fof(f555,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl12_53),
% 0.21/0.52    inference(avatar_component_clause,[],[f554])).
% 0.21/0.52  fof(f357,plain,(
% 0.21/0.52    r2_hidden(sK4,sK1) | ~spl12_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f356])).
% 0.21/0.52  fof(f564,plain,(
% 0.21/0.52    ~spl12_2 | spl12_54 | ~spl12_52),
% 0.21/0.52    inference(avatar_split_clause,[],[f559,f551,f561,f121])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    spl12_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 0.21/0.52  fof(f561,plain,(
% 0.21/0.52    spl12_54 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).
% 0.21/0.52  fof(f551,plain,(
% 0.21/0.52    spl12_52 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_52])])).
% 0.21/0.52  fof(f559,plain,(
% 0.21/0.52    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_52),
% 0.21/0.52    inference(superposition,[],[f92,f552])).
% 0.21/0.52  fof(f552,plain,(
% 0.21/0.52    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl12_52),
% 0.21/0.52    inference(avatar_component_clause,[],[f551])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.52  fof(f557,plain,(
% 0.21/0.52    spl12_52 | spl12_53 | ~spl12_3 | ~spl12_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f549,f121,f125,f554,f551])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    spl12_3 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 0.21/0.52  fof(f549,plain,(
% 0.21/0.52    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl12_2),
% 0.21/0.52    inference(resolution,[],[f94,f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f121])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f61])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(flattening,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.52  fof(f393,plain,(
% 0.21/0.52    ~spl12_6 | ~spl12_4 | ~spl12_5 | spl12_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f391,f349,f140,f129,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl12_6 <=> v1_relat_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    spl12_4 <=> v1_funct_1(sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl12_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_5])])).
% 0.21/0.52  % (30681)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  fof(f349,plain,(
% 0.21/0.52    spl12_23 <=> r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl12_23])])).
% 0.21/0.52  fof(f391,plain,(
% 0.21/0.52    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl12_23),
% 0.21/0.52    inference(resolution,[],[f350,f110])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ( ! [X6,X0,X1] : (r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f74])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    ( ! [X6,X2,X0,X1] : (r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK8(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK8(X0,X1,X2),X2)) & ((sK8(X0,X1,X2) = k1_funct_1(X0,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK10(X0,X1,X6)) = X6 & r2_hidden(sK10(X0,X1,X6),X1) & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f52,f55,f54,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK8(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK8(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = sK8(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (sK8(X0,X1,X2) = k1_funct_1(X0,sK9(X0,X1,X2)) & r2_hidden(sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),k1_relat_1(X0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK10(X0,X1,X6)) = X6 & r2_hidden(sK10(X0,X1,X6),X1) & r2_hidden(sK10(X0,X1,X6),k1_relat_1(X0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(rectify,[],[f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.53  fof(f350,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3)) | spl12_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f349])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    ~spl12_32 | spl12_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f385,f364,f387])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    spl12_32 <=> r2_hidden(sK10(sK3,sK2,sK4),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).
% 0.21/0.53  fof(f364,plain,(
% 0.21/0.53    spl12_27 <=> m1_subset_1(sK10(sK3,sK2,sK4),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK3,sK2,sK4),sK0) | spl12_27),
% 0.21/0.53    inference(resolution,[],[f365,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    ~m1_subset_1(sK10(sK3,sK2,sK4),sK0) | spl12_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f364])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    ~spl12_5 | ~spl12_15 | spl12_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f374,f367,f191,f140])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    spl12_15 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK10(sK3,X1,X0),X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).
% 0.21/0.53  fof(f367,plain,(
% 0.21/0.53    spl12_28 <=> r2_hidden(sK10(sK3,sK2,sK4),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl12_15 | spl12_28)),
% 0.21/0.53    inference(resolution,[],[f368,f192])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK10(sK3,X1,X0),X1) | ~r2_hidden(X0,k9_relat_1(sK3,X1))) ) | ~spl12_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f191])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK3,sK2,sK4),sK2) | spl12_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f367])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~spl12_27 | ~spl12_28 | ~spl12_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f347,f334,f367,f364])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    spl12_21 <=> sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_21])])).
% 0.21/0.53  fof(f347,plain,(
% 0.21/0.53    ~r2_hidden(sK10(sK3,sK2,sK4),sK2) | ~m1_subset_1(sK10(sK3,sK2,sK4),sK0) | ~spl12_21),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f345])).
% 0.21/0.53  fof(f345,plain,(
% 0.21/0.53    sK4 != sK4 | ~r2_hidden(sK10(sK3,sK2,sK4),sK2) | ~m1_subset_1(sK10(sK3,sK2,sK4),sK0) | ~spl12_21),
% 0.21/0.53    inference(superposition,[],[f66,f335])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4)) | ~spl12_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f334])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f21,f43,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ? [X4] : (! [X5] : (k1_funct_1(sK3,X5) != X4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))) => (! [X5] : (k1_funct_1(sK3,X5) != sK4 | ~r2_hidden(X5,sK2) | ~m1_subset_1(X5,sK0)) & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.53    inference(ennf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.53    inference(negated_conjecture,[],[f16])).
% 0.21/0.53  fof(f16,conjecture,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_funct_2)).
% 0.21/0.53  fof(f358,plain,(
% 0.21/0.53    ~spl12_23 | spl12_25 | ~spl12_2 | ~spl12_16 | ~spl12_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f343,f334,f200,f121,f356,f349])).
% 0.21/0.53  fof(f200,plain,(
% 0.21/0.53    spl12_16 <=> ! [X1,X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | ~v5_relat_1(sK3,X1) | r2_hidden(k1_funct_1(sK3,X0),X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).
% 0.21/0.53  fof(f343,plain,(
% 0.21/0.53    r2_hidden(sK4,sK1) | ~r2_hidden(sK10(sK3,sK2,sK4),k1_relat_1(sK3)) | (~spl12_2 | ~spl12_16 | ~spl12_21)),
% 0.21/0.53    inference(superposition,[],[f212,f335])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK1) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | (~spl12_2 | ~spl12_16)),
% 0.21/0.53    inference(resolution,[],[f209,f122])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl12_16),
% 0.21/0.53    inference(resolution,[],[f201,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.53  fof(f201,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v5_relat_1(sK3,X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),X1)) ) | ~spl12_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f200])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    spl12_21 | ~spl12_5 | ~spl12_20),
% 0.21/0.53    inference(avatar_split_clause,[],[f331,f327,f140,f334])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    spl12_20 <=> ! [X1,X0] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_20])])).
% 0.21/0.53  fof(f331,plain,(
% 0.21/0.53    sK4 = k1_funct_1(sK3,sK10(sK3,sK2,sK4)) | (~spl12_5 | ~spl12_20)),
% 0.21/0.53    inference(resolution,[],[f328,f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl12_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f140])).
% 0.21/0.53  fof(f328,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0) ) | ~spl12_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f327])).
% 0.21/0.53  fof(f329,plain,(
% 0.21/0.53    ~spl12_6 | spl12_20 | ~spl12_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f325,f129,f327,f145])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | k1_funct_1(sK3,sK10(sK3,X1,X0)) = X0 | ~v1_relat_1(sK3)) ) | ~spl12_4),
% 0.21/0.53    inference(resolution,[],[f108,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    v1_funct_1(sK3) | ~spl12_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | k1_funct_1(X0,sK10(X0,X1,X6)) = X6 | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK10(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f56])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ~spl12_6 | spl12_16 | ~spl12_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f198,f129,f200,f145])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1) | ~v1_relat_1(sK3)) ) | ~spl12_4),
% 0.21/0.53    inference(resolution,[],[f85,f130])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~r2_hidden(X2,k1_relat_1(X1)) | r2_hidden(k1_funct_1(X1,X2),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.53    inference(flattening,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~spl12_6 | spl12_15 | ~spl12_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f189,f129,f191,f145])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k9_relat_1(sK3,X1)) | r2_hidden(sK10(sK3,X1,X0),X1) | ~v1_relat_1(sK3)) ) | ~spl12_4),
% 0.21/0.53    inference(resolution,[],[f109,f130])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X6,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | r2_hidden(sK10(X0,X1,X6),X1) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X6,X2,X0,X1] : (r2_hidden(sK10(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f56])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    ~spl12_2 | spl12_6),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    $false | (~spl12_2 | spl12_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl12_6),
% 0.21/0.53    inference(resolution,[],[f146,f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~v1_relat_1(sK3) | spl12_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f145])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    ~spl12_2 | spl12_5 | ~spl12_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f137,f117,f140,f121])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl12_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl12_1),
% 0.21/0.53    inference(superposition,[],[f118,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl12_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f117])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    spl12_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f62,f129])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    v1_funct_1(sK3)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl12_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f63,f125])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    spl12_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f64,f121])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl12_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f65,f117])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.53    inference(cnf_transformation,[],[f44])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (30674)------------------------------
% 0.21/0.53  % (30674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30674)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (30674)Memory used [KB]: 11001
% 0.21/0.53  % (30674)Time elapsed: 0.093 s
% 0.21/0.53  % (30674)------------------------------
% 0.21/0.53  % (30674)------------------------------
% 0.21/0.53  % (30683)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.53  % (30667)Success in time 0.169 s
%------------------------------------------------------------------------------
