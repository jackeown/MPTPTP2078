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
% DateTime   : Thu Dec  3 13:06:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 143 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  237 ( 425 expanded)
%              Number of equality atoms :   24 (  44 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f58,f62,f68,f76,f87,f99,f157,f163,f219,f335,f376])).

fof(f376,plain,
    ( ~ spl8_8
    | ~ spl8_15
    | ~ spl8_29 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | ~ spl8_8
    | ~ spl8_15
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f374,f156])).

fof(f156,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl8_15
  <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f374,plain,
    ( sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_8
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f373,f86])).

fof(f86,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl8_8
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f373,plain,
    ( ~ r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_29 ),
    inference(resolution,[],[f334,f20])).

fof(f20,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,sK0)
      | ~ r2_hidden(X5,sK2)
      | sK4 != k1_funct_1(sK3,X5) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
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
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f334,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl8_29
  <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f335,plain,
    ( spl8_29
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f225,f217,f333])).

fof(f217,plain,
    ( spl8_22
  <=> r2_hidden(sK7(sK3,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f225,plain,
    ( m1_subset_1(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_22 ),
    inference(resolution,[],[f218,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f218,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl8_22
    | ~ spl8_16 ),
    inference(avatar_split_clause,[],[f168,f161,f217])).

fof(f161,plain,
    ( spl8_16
  <=> r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).

fof(f168,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK0)
    | ~ spl8_16 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f162,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_16 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl8_16
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f103,f97,f49,f161])).

fof(f49,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f97,plain,
    ( spl8_10
  <=> r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f103,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1))
    | ~ spl8_2
    | ~ spl8_10 ),
    inference(resolution,[],[f98,f54])).

fof(f54,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3)
        | r2_hidden(X1,k2_zfmisc_1(sK0,sK1)) )
    | ~ spl8_2 ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f50,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f98,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f157,plain,
    ( spl8_15
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f110,f97,f56,f45,f155])).

fof(f45,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f56,plain,
    ( spl8_3
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f110,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ spl8_1
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f109,f57])).

fof(f57,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f56])).

fof(f109,plain,
    ( sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl8_1
    | ~ spl8_10 ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f46,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f101,plain,
    ( ~ v1_funct_1(sK3)
    | sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))
    | ~ v1_relat_1(sK3)
    | ~ spl8_10 ),
    inference(resolution,[],[f98,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).

fof(f99,plain,
    ( spl8_10
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f77,f74,f97])).

fof(f74,plain,
    ( spl8_6
  <=> sP6(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f77,plain,
    ( r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3)
    | ~ spl8_6 ),
    inference(resolution,[],[f75,f26])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).

fof(f75,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f87,plain,
    ( spl8_8
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f78,f74,f85])).

fof(f78,plain,
    ( r2_hidden(sK7(sK3,sK2,sK4),sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(sK7(X0,X1,X3),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,
    ( spl8_6
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(avatar_split_clause,[],[f72,f66,f56,f74])).

fof(f66,plain,
    ( spl8_5
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f72,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f69,f57])).

fof(f69,plain,
    ( sP6(sK4,sK2,sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_5 ),
    inference(resolution,[],[f67,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k9_relat_1(X0,X1))
      | sP6(X3,X1,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f67,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f68,plain,
    ( spl8_5
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f63,f60,f49,f66])).

fof(f60,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f63,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f61,f53])).

fof(f53,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl8_2 ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f61,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f60])).

% (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1406)Termination reason: Refutation not found, incomplete strategy

% (1406)Memory used [KB]: 1663
% (1406)Time elapsed: 0.090 s
% (1406)------------------------------
% (1406)------------------------------
fof(f62,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f58,plain,
    ( spl8_3
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f52,f49,f56])).

fof(f52,plain,
    ( v1_relat_1(sK3)
    | ~ spl8_2 ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f51,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f22,f45])).

fof(f22,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:42:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (1413)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (1398)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (1405)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (1406)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (1413)Refutation not found, incomplete strategy% (1413)------------------------------
% 0.22/0.48  % (1413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (1413)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (1413)Memory used [KB]: 10618
% 0.22/0.48  % (1413)Time elapsed: 0.067 s
% 0.22/0.48  % (1413)------------------------------
% 0.22/0.48  % (1413)------------------------------
% 0.22/0.48  % (1408)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.48  % (1393)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (1403)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.49  % (1399)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (1393)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (1407)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f377,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f47,f51,f58,f62,f68,f76,f87,f99,f157,f163,f219,f335,f376])).
% 0.22/0.50  fof(f376,plain,(
% 0.22/0.50    ~spl8_8 | ~spl8_15 | ~spl8_29),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f375])).
% 0.22/0.50  fof(f375,plain,(
% 0.22/0.50    $false | (~spl8_8 | ~spl8_15 | ~spl8_29)),
% 0.22/0.50    inference(subsumption_resolution,[],[f374,f156])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f155])).
% 0.22/0.50  fof(f155,plain,(
% 0.22/0.50    spl8_15 <=> sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.22/0.50  fof(f374,plain,(
% 0.22/0.50    sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl8_8 | ~spl8_29)),
% 0.22/0.50    inference(subsumption_resolution,[],[f373,f86])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl8_8 <=> r2_hidden(sK7(sK3,sK2,sK4),sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.22/0.50  fof(f373,plain,(
% 0.22/0.50    ~r2_hidden(sK7(sK3,sK2,sK4),sK2) | sK4 != k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~spl8_29),
% 0.22/0.50    inference(resolution,[],[f334,f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ( ! [X5] : (~m1_subset_1(X5,sK0) | ~r2_hidden(X5,sK2) | sK4 != k1_funct_1(sK3,X5)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,plain,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    inference(pure_predicate_removal,[],[f9])).
% 0.22/0.50  fof(f9,negated_conjecture,(
% 0.22/0.50    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    inference(negated_conjecture,[],[f8])).
% 0.22/0.50  fof(f8,conjecture,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t116_funct_2)).
% 0.22/0.50  fof(f334,plain,(
% 0.22/0.50    m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl8_29),
% 0.22/0.50    inference(avatar_component_clause,[],[f333])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    spl8_29 <=> m1_subset_1(sK7(sK3,sK2,sK4),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.22/0.50  fof(f335,plain,(
% 0.22/0.50    spl8_29 | ~spl8_22),
% 0.22/0.50    inference(avatar_split_clause,[],[f225,f217,f333])).
% 0.22/0.50  fof(f217,plain,(
% 0.22/0.50    spl8_22 <=> r2_hidden(sK7(sK3,sK2,sK4),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    m1_subset_1(sK7(sK3,sK2,sK4),sK0) | ~spl8_22),
% 0.22/0.50    inference(resolution,[],[f218,f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f218,plain,(
% 0.22/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl8_22),
% 0.22/0.50    inference(avatar_component_clause,[],[f217])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    spl8_22 | ~spl8_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f168,f161,f217])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl8_16 <=> r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_16])])).
% 0.22/0.50  fof(f168,plain,(
% 0.22/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK0) | ~spl8_16),
% 0.22/0.50    inference(resolution,[],[f162,f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1)) | ~spl8_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl8_16 | ~spl8_2 | ~spl8_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f103,f97,f49,f161])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl8_10 <=> r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),k2_zfmisc_1(sK0,sK1)) | (~spl8_2 | ~spl8_10)),
% 0.22/0.50    inference(resolution,[],[f98,f54])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ( ! [X1] : (~r2_hidden(X1,sK3) | r2_hidden(X1,k2_zfmisc_1(sK0,sK1))) ) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f50,f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl8_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f49])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3) | ~spl8_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl8_15 | ~spl8_1 | ~spl8_3 | ~spl8_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f110,f97,f56,f45,f155])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    spl8_1 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    spl8_3 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | (~spl8_1 | ~spl8_3 | ~spl8_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f109,f57])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_relat_1(sK3) | ~spl8_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f56])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~v1_relat_1(sK3) | (~spl8_1 | ~spl8_10)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl8_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f45])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~v1_funct_1(sK3) | sK4 = k1_funct_1(sK3,sK7(sK3,sK2,sK4)) | ~v1_relat_1(sK3) | ~spl8_10),
% 0.22/0.50    inference(resolution,[],[f98,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | k1_funct_1(X2,X0) = X1 | ~v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_funct_1)).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl8_10 | ~spl8_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f77,f74,f97])).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    spl8_6 <=> sP6(sK4,sK2,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    r2_hidden(k4_tarski(sK7(sK3,sK2,sK4),sK4),sK3) | ~spl8_6),
% 0.22/0.50    inference(resolution,[],[f75,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(k4_tarski(sK7(X0,X1,X3),X3),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    sP6(sK4,sK2,sK3) | ~spl8_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f74])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    spl8_8 | ~spl8_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f78,f74,f85])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    r2_hidden(sK7(sK3,sK2,sK4),sK2) | ~spl8_6),
% 0.22/0.50    inference(resolution,[],[f75,f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(sK7(X0,X1,X3),X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    spl8_6 | ~spl8_3 | ~spl8_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f72,f66,f56,f74])).
% 0.22/0.50  fof(f66,plain,(
% 0.22/0.50    spl8_5 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    sP6(sK4,sK2,sK3) | (~spl8_3 | ~spl8_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f69,f57])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    sP6(sK4,sK2,sK3) | ~v1_relat_1(sK3) | ~spl8_5),
% 0.22/0.50    inference(resolution,[],[f67,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,k9_relat_1(X0,X1)) | sP6(X3,X1,X0) | ~v1_relat_1(X0)) )),
% 0.22/0.50    inference(equality_resolution,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | ~spl8_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f66])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl8_5 | ~spl8_2 | ~spl8_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f60,f49,f66])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl8_4 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (~spl8_2 | ~spl8_4)),
% 0.22/0.50    inference(forward_demodulation,[],[f61,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f50,f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | ~spl8_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f60])).
% 0.22/0.50  % (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% 0.22/0.50  % (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1406)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (1406)Memory used [KB]: 1663
% 0.22/0.50  % (1406)Time elapsed: 0.090 s
% 0.22/0.50  % (1406)------------------------------
% 0.22/0.50  % (1406)------------------------------
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    spl8_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f21,f60])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    spl8_3 | ~spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f52,f49,f56])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    v1_relat_1(sK3) | ~spl8_2),
% 0.22/0.50    inference(resolution,[],[f50,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl8_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f23,f49])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    spl8_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f22,f45])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (1393)------------------------------
% 0.22/0.50  % (1393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1393)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (1393)Memory used [KB]: 6396
% 0.22/0.50  % (1393)Time elapsed: 0.083 s
% 0.22/0.50  % (1393)------------------------------
% 0.22/0.50  % (1393)------------------------------
% 0.22/0.50  % (1392)Success in time 0.137 s
%------------------------------------------------------------------------------
