%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t115_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:29 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 170 expanded)
%              Number of leaves         :   22 (  65 expanded)
%              Depth                    :    9
%              Number of atoms          :  277 ( 524 expanded)
%              Number of equality atoms :   24 (  57 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f81,f91,f95,f102,f118,f135,f139,f144,f194,f274,f290,f322,f326])).

fof(f326,plain,
    ( spl9_61
    | spl9_67
    | ~ spl9_72 ),
    inference(avatar_contradiction_clause,[],[f325])).

fof(f325,plain,
    ( $false
    | ~ spl9_61
    | ~ spl9_67
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f324,f273])).

fof(f273,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_61 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl9_61
  <=> ~ r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_61])])).

fof(f324,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_67
    | ~ spl9_72 ),
    inference(subsumption_resolution,[],[f323,f289])).

fof(f289,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_67 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl9_67
  <=> ~ v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_67])])).

fof(f323,plain,
    ( v1_xboole_0(sK0)
    | r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_72 ),
    inference(resolution,[],[f321,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',t2_subset)).

fof(f321,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_72 ),
    inference(avatar_component_clause,[],[f320])).

fof(f320,plain,
    ( spl9_72
  <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_72])])).

fof(f322,plain,
    ( spl9_72
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f311,f192,f142,f320])).

fof(f142,plain,
    ( spl9_22
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f192,plain,
    ( spl9_40
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f311,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(resolution,[],[f201,f143])).

fof(f143,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl9_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f201,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X1))
        | m1_subset_1(sK7(sK3,sK2,sK4),X1) )
    | ~ spl9_40 ),
    inference(resolution,[],[f193,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',t4_subset)).

fof(f193,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl9_40 ),
    inference(avatar_component_clause,[],[f192])).

fof(f290,plain,
    ( ~ spl9_67
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(avatar_split_clause,[],[f286,f192,f142,f288])).

fof(f286,plain,
    ( ~ v1_xboole_0(sK0)
    | ~ spl9_22
    | ~ spl9_40 ),
    inference(resolution,[],[f202,f143])).

fof(f202,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl9_40 ),
    inference(resolution,[],[f193,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',t5_subset)).

fof(f274,plain,
    ( ~ spl9_61
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f152,f133,f116,f272])).

fof(f116,plain,
    ( spl9_12
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f133,plain,
    ( spl9_18
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f152,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl9_12
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f146,f121])).

fof(f121,plain,
    ( k1_funct_1(sK3,sK7(sK3,sK2,sK4)) = sK4
    | ~ spl9_12 ),
    inference(resolution,[],[f117,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k1_funct_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',d12_funct_1)).

fof(f117,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f146,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | k1_funct_1(sK3,sK7(sK3,sK2,sK4)) != sK4
    | ~ spl9_18 ),
    inference(resolution,[],[f134,f46])).

fof(f46,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | k1_funct_1(sK3,X5) != sK4 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',t115_funct_2)).

fof(f134,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f133])).

fof(f194,plain,
    ( spl9_40
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f119,f116,f192])).

fof(f119,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl9_12 ),
    inference(resolution,[],[f117,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f144,plain,
    ( spl9_22
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f140,f137,f79,f142])).

fof(f79,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f137,plain,
    ( spl9_20
  <=> m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f140,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl9_2
    | ~ spl9_20 ),
    inference(forward_demodulation,[],[f138,f84])).

fof(f84,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',redefinition_k1_relset_1)).

fof(f80,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f138,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f137])).

fof(f139,plain,
    ( spl9_20
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f82,f79,f137])).

fof(f82,plain,
    ( m1_subset_1(k1_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK0))
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',dt_k1_relset_1)).

fof(f135,plain,
    ( spl9_18
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f120,f116,f133])).

fof(f120,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl9_12 ),
    inference(resolution,[],[f117,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f118,plain,
    ( spl9_12
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f110,f100,f89,f75,f116])).

fof(f75,plain,
    ( spl9_0
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_0])])).

fof(f89,plain,
    ( spl9_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f100,plain,
    ( spl9_8
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f110,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl9_0
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f109,f90])).

fof(f90,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f109,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_0
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f103,f76])).

fof(f76,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_0 ),
    inference(avatar_component_clause,[],[f75])).

fof(f103,plain,
    ( ~ v1_funct_1(sK3)
    | sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f101,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f101,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f102,plain,
    ( spl9_8
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f96,f93,f79,f100])).

fof(f93,plain,
    ( spl9_6
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f96,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl9_2
    | ~ spl9_6 ),
    inference(forward_demodulation,[],[f94,f86])).

fof(f86,plain,
    ( ! [X1] : k7_relset_1(sK0,sK1,sK3,X1) = k9_relat_1(sK3,X1)
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',redefinition_k7_relset_1)).

fof(f94,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f95,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f47,f93])).

fof(f47,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f29])).

fof(f91,plain,
    ( spl9_4
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f83,f79,f89])).

fof(f83,plain,
    ( v1_relat_1(sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f80,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/funct_2__t115_funct_2.p',cc1_relset_1)).

fof(f81,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f49,f79])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    spl9_0 ),
    inference(avatar_split_clause,[],[f48,f75])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
