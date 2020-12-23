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
% DateTime   : Thu Dec  3 13:06:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 151 expanded)
%              Number of leaves         :   20 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  246 ( 477 expanded)
%              Number of equality atoms :   20 (  53 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f142,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f62,f66,f71,f75,f84,f92,f103,f109,f127,f131,f141])).

fof(f141,plain,
    ( ~ spl8_10
    | ~ spl8_12
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl8_10
    | ~ spl8_12
    | spl8_13 ),
    inference(subsumption_resolution,[],[f139,f130])).

fof(f130,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl8_13
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f139,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_10
    | ~ spl8_12 ),
    inference(resolution,[],[f105,f126])).

fof(f126,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_12 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_12
  <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(X0,sK0) )
    | ~ spl8_10 ),
    inference(resolution,[],[f102,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f102,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl8_10
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f131,plain,
    ( ~ spl8_13
    | ~ spl8_7
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f123,f107,f82,f129])).

fof(f82,plain,
    ( spl8_7
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f107,plain,
    ( spl8_11
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f123,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_7
    | ~ spl8_11 ),
    inference(subsumption_resolution,[],[f122,f87])).

fof(f87,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_7 ),
    inference(resolution,[],[f83,f29])).

fof(f29,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | k1_funct_1(X0,sK7(X0,X1,X3)) = X3 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).

fof(f83,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f122,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_11 ),
    inference(resolution,[],[f108,f21])).

fof(f21,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).

fof(f108,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f107])).

fof(f127,plain,
    ( spl8_12
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f85,f82,f125])).

fof(f85,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))
    | ~ spl8_7 ),
    inference(resolution,[],[f83,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f109,plain,
    ( spl8_11
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f86,f82,f107])).

fof(f86,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_7 ),
    inference(resolution,[],[f83,f28])).

fof(f28,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f103,plain,
    ( spl8_10
    | ~ spl8_8 ),
    inference(avatar_split_clause,[],[f98,f90,f101])).

fof(f90,plain,
    ( spl8_8
  <=> r1_tarski(k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f98,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl8_8 ),
    inference(resolution,[],[f91,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f91,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f92,plain,
    ( spl8_8
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f80,f73,f60,f90])).

fof(f60,plain,
    ( spl8_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f73,plain,
    ( spl8_6
  <=> v4_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f80,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ spl8_3
    | ~ spl8_6 ),
    inference(subsumption_resolution,[],[f79,f61])).

fof(f61,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f79,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f74,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f74,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f73])).

fof(f84,plain,
    ( spl8_7
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f78,f69,f60,f45,f82])).

fof(f45,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f69,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f78,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f77,f61])).

fof(f77,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f76,f46])).

fof(f46,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f76,plain,
    ( ~ v1_funct_1(sK3)
    | sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f70,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f75,plain,
    ( spl8_6
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f53,f50,f73])).

fof(f50,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f53,plain,
    ( v4_relat_1(sK3,sK0)
    | ~ spl8_2 ),
    inference(resolution,[],[f51,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f50])).

fof(f71,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f67,f64,f50,f69])).

fof(f64,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f67,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f65,f55])).

fof(f55,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl8_2 ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f65,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f66,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f22,f64])).

fof(f22,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f62,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f54,f50,f60])).

fof(f54,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f51,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f52,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f24,f50])).

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f47,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:36:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4383)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (4395)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (4391)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (4379)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (4384)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (4375)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (4375)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f47,f52,f62,f66,f71,f75,f84,f92,f103,f109,f127,f131,f141])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    ~spl8_10 | ~spl8_12 | spl8_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f140])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    $false | (~spl8_10 | ~spl8_12 | spl8_13)),
% 0.21/0.50    inference(subsumption_resolution,[],[f139,f130])).
% 0.21/0.50  fof(f130,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | spl8_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f129])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl8_13 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK0) | (~spl8_10 | ~spl8_12)),
% 0.21/0.50    inference(resolution,[],[f105,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~spl8_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    spl8_12 <=> r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X0,sK0)) ) | ~spl8_10),
% 0.21/0.50    inference(resolution,[],[f102,f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl8_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl8_10 <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    ~spl8_13 | ~spl8_7 | ~spl8_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f123,f107,f82,f129])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl8_7 <=> sP6(sK4,sK2,sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl8_11 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | (~spl8_7 | ~spl8_11)),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_7),
% 0.21/0.50    inference(resolution,[],[f83,f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | k1_funct_1(X0,sK7(X0,X1,X3)) = X3) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_funct_1)).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    sP6(sK4,sK2,sK3) | ~spl8_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK0) | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_11),
% 0.21/0.50    inference(resolution,[],[f108,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X5] : (~r2_hidden(X5,sK2) | ~r2_hidden(X5,sK0) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.21/0.50  fof(f9,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.50    inference(negated_conjecture,[],[f8])).
% 0.21/0.50  fof(f8,conjecture,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t115_funct_2)).
% 0.21/0.50  fof(f108,plain,(
% 0.21/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    spl8_12 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f85,f82,f125])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    r2_hidden(sK7(sK3,sK2,sK4),k1_relat_1(sK3)) | ~spl8_7),
% 0.21/0.50    inference(resolution,[],[f83,f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),k1_relat_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl8_11 | ~spl8_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f86,f82,f107])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_7),
% 0.21/0.50    inference(resolution,[],[f83,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl8_10 | ~spl8_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f98,f90,f101])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    spl8_8 <=> r1_tarski(k1_relat_1(sK3),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) | ~spl8_8),
% 0.21/0.50    inference(resolution,[],[f91,f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK3),sK0) | ~spl8_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f90])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    spl8_8 | ~spl8_3 | ~spl8_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f80,f73,f60,f90])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl8_3 <=> v1_relat_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    spl8_6 <=> v4_relat_1(sK3,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK3),sK0) | (~spl8_3 | ~spl8_6)),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl8_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    r1_tarski(k1_relat_1(sK3),sK0) | ~v1_relat_1(sK3) | ~spl8_6),
% 0.21/0.50    inference(resolution,[],[f74,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    v4_relat_1(sK3,sK0) | ~spl8_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f73])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl8_7 | ~spl8_1 | ~spl8_3 | ~spl8_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f78,f69,f60,f45,f82])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl8_1 <=> v1_funct_1(sK3)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    spl8_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    sP6(sK4,sK2,sK3) | (~spl8_1 | ~spl8_3 | ~spl8_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f77,f61])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_5)),
% 0.21/0.50    inference(subsumption_resolution,[],[f76,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    v1_funct_1(sK3) | ~spl8_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ~v1_funct_1(sK3) | sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | ~spl8_5),
% 0.21/0.50    inference(resolution,[],[f70,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f69])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl8_6 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f50,f73])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    v4_relat_1(sK3,sK0) | ~spl8_2),
% 0.21/0.50    inference(resolution,[],[f51,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f50])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    spl8_5 | ~spl8_2 | ~spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f64,f50,f69])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_2 | ~spl8_4)),
% 0.21/0.50    inference(forward_demodulation,[],[f65,f55])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0] : (k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)) ) | ~spl8_2),
% 0.21/0.50    inference(resolution,[],[f51,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl8_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f64])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl8_3 | ~spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f50,f60])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v1_relat_1(sK3) | ~spl8_2),
% 0.21/0.50    inference(resolution,[],[f51,f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl8_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f50])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl8_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f23,f45])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    v1_funct_1(sK3)),
% 0.21/0.50    inference(cnf_transformation,[],[f13])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (4375)------------------------------
% 0.21/0.50  % (4375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4375)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (4375)Memory used [KB]: 6140
% 0.21/0.50  % (4375)Time elapsed: 0.083 s
% 0.21/0.50  % (4375)------------------------------
% 0.21/0.50  % (4375)------------------------------
% 0.21/0.50  % (4390)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (4386)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (4376)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (4376)Refutation not found, incomplete strategy% (4376)------------------------------
% 0.21/0.50  % (4376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4376)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4376)Memory used [KB]: 10618
% 0.21/0.50  % (4376)Time elapsed: 0.092 s
% 0.21/0.50  % (4376)------------------------------
% 0.21/0.50  % (4376)------------------------------
% 0.21/0.50  % (4382)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (4377)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (4395)Refutation not found, incomplete strategy% (4395)------------------------------
% 0.21/0.50  % (4395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (4395)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (4395)Memory used [KB]: 10618
% 0.21/0.50  % (4395)Time elapsed: 0.088 s
% 0.21/0.50  % (4395)------------------------------
% 0.21/0.50  % (4395)------------------------------
% 0.21/0.50  % (4389)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (4374)Success in time 0.143 s
%------------------------------------------------------------------------------
