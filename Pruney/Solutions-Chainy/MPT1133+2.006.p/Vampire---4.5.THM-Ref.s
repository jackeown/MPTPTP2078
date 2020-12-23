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
% DateTime   : Thu Dec  3 13:09:27 EST 2020

% Result     : Theorem 6.32s
% Output     : Refutation 6.32s
% Verified   : 
% Statistics : Number of formulae       :  197 (4906 expanded)
%              Number of leaves         :   34 (1821 expanded)
%              Depth                    :   24
%              Number of atoms          :  909 (61499 expanded)
%              Number of equality atoms :   65 (5072 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f196,f197,f1664,f1665,f1666,f2658,f2879,f3052,f3053,f3082,f4493,f4805,f4832,f4835,f4836])).

fof(f4836,plain,
    ( ~ spl11_7
    | spl11_1
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f4833,f4483,f1660,f1656,f502,f189,f506])).

fof(f506,plain,
    ( spl11_7
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f189,plain,
    ( spl11_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f502,plain,
    ( spl11_6
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f1656,plain,
    ( spl11_18
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f1660,plain,
    ( spl11_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f4483,plain,
    ( spl11_20
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f4833,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl11_1
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f4484,f191,f1657,f1661,f313,f503,f184])).

fof(f184,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f503,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f502])).

fof(f313,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f216,f253,f181])).

fof(f181,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ sP10(X3,X2) ) ),
    inference(general_splitting,[],[f167,f180_D])).

fof(f180,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | sP10(X3,X2) ) ),
    inference(cnf_transformation,[],[f180_D])).

fof(f180_D,plain,(
    ! [X2,X3] :
      ( ! [X0] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    <=> ~ sP10(X3,X2) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).

fof(f167,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f253,plain,(
    r1_tarski(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f211,f223,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f223,plain,(
    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) ),
    inference(unit_resulting_resolution,[],[f198,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f198,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f111,f112])).

fof(f112,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,
    ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | ~ v5_pre_topc(sK2,sK0,sK1) )
    & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
      | v5_pre_topc(sK2,sK0,sK1) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f71,f75,f74,f73,f72])).

fof(f72,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK0,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK0,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | ~ v5_pre_topc(X2,sK0,sK1) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
                | v5_pre_topc(X2,sK0,sK1) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | ~ v5_pre_topc(X2,sK0,sK1) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
              | v5_pre_topc(X2,sK0,sK1) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | ~ v5_pre_topc(sK2,sK0,sK1) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
            | v5_pre_topc(sK2,sK0,sK1) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | ~ v5_pre_topc(sK2,sK0,sK1) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
          | v5_pre_topc(sK2,sK0,sK1) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ v5_pre_topc(sK2,sK0,sK1) )
      & ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | v5_pre_topc(sK2,sK0,sK1) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
      & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f111,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f76])).

fof(f211,plain,(
    v1_relat_1(sK2) ),
    inference(unit_resulting_resolution,[],[f108,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f108,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f216,plain,(
    sP10(sK2,u1_struct_0(sK1)) ),
    inference(unit_resulting_resolution,[],[f108,f180])).

fof(f1661,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f1660])).

fof(f1657,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f191,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f4484,plain,
    ( v1_funct_1(sK2)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f4483])).

fof(f105,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f104,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f103,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f102,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f76])).

fof(f4835,plain,
    ( spl11_7
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_20 ),
    inference(avatar_split_clause,[],[f4834,f4483,f502,f193,f506])).

fof(f193,plain,
    ( spl11_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f4834,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl11_2
    | ~ spl11_6
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f105,f4484,f104,f203,f247,f313,f3083,f199,f198,f503,f182])).

fof(f182,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f199,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f110,f112])).

fof(f110,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f76])).

fof(f3083,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f194,f112])).

fof(f194,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f193])).

fof(f247,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f202,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f202,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f103,f118])).

fof(f118,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f203,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(unit_resulting_resolution,[],[f102,f103,f123])).

fof(f123,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f4832,plain,
    ( spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f4831])).

fof(f4831,plain,
    ( $false
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_18
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f4830,f1648])).

fof(f1648,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl11_17 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f1647,plain,
    ( spl11_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).

fof(f4830,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl11_1
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_18
    | ~ spl11_19
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f4484,f191,f1657,f1661,f1644,f1630,f182])).

fof(f1630,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1629,plain,
    ( spl11_14
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f1644,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f1643,plain,
    ( spl11_16
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f4805,plain,
    ( ~ spl11_2
    | spl11_14
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f4804])).

fof(f4804,plain,
    ( $false
    | ~ spl11_2
    | spl11_14
    | ~ spl11_16
    | ~ spl11_17
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f4803,f1648])).

fof(f4803,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl11_2
    | spl11_14
    | ~ spl11_16
    | ~ spl11_20 ),
    inference(unit_resulting_resolution,[],[f102,f103,f4484,f206,f249,f1631,f3083,f199,f198,f1644,f184])).

fof(f1631,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl11_14 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f249,plain,(
    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f205,f137])).

fof(f205,plain,(
    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(unit_resulting_resolution,[],[f105,f118])).

fof(f206,plain,(
    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(unit_resulting_resolution,[],[f104,f105,f123])).

fof(f4493,plain,(
    spl11_20 ),
    inference(avatar_split_clause,[],[f200,f4483])).

fof(f200,plain,(
    v1_funct_1(sK2) ),
    inference(forward_demodulation,[],[f109,f112])).

fof(f109,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

fof(f3082,plain,
    ( spl11_2
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_17 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | spl11_2
    | ~ spl11_14
    | ~ spl11_16
    | ~ spl11_17 ),
    inference(subsumption_resolution,[],[f3080,f1648])).

fof(f3080,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | spl11_2
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f102,f103,f200,f206,f249,f1630,f1640,f199,f198,f1644,f185])).

fof(f185,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1640,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl11_2 ),
    inference(forward_demodulation,[],[f195,f112])).

fof(f195,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f193])).

fof(f3053,plain,
    ( spl11_7
    | ~ spl11_1
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_19 ),
    inference(avatar_split_clause,[],[f3050,f1660,f1656,f502,f189,f506])).

fof(f3050,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl11_1
    | ~ spl11_6
    | ~ spl11_18
    | ~ spl11_19 ),
    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f200,f190,f1657,f1661,f313,f503,f185])).

fof(f190,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f189])).

fof(f3052,plain,
    ( ~ spl11_7
    | spl11_2
    | ~ spl11_6 ),
    inference(avatar_split_clause,[],[f3051,f502,f193,f506])).

fof(f3051,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl11_2
    | ~ spl11_6 ),
    inference(unit_resulting_resolution,[],[f105,f200,f104,f203,f247,f1640,f313,f199,f198,f503,f183])).

fof(f183,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f2879,plain,
    ( ~ spl11_1
    | spl11_6
    | spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f2878])).

fof(f2878,plain,
    ( $false
    | ~ spl11_1
    | spl11_6
    | spl11_14
    | ~ spl11_16
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f2877,f2660])).

fof(f2660,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl11_6
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f2659,f2147])).

fof(f2147,plain,
    ( k1_xboole_0 = sK2
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f2113,f131])).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f87])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK6(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).

fof(f2113,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2)
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f2100,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f166,f178_D])).

fof(f178,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f178_D])).

fof(f178_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ v1_xboole_0(X2)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f2100,plain,
    ( sP9(sK2)
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f115,f2087,f178])).

fof(f2087,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl11_6 ),
    inference(forward_demodulation,[],[f2027,f175])).

fof(f175,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f150])).

fof(f150,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2027,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | spl11_6 ),
    inference(backward_demodulation,[],[f198,f2023])).

fof(f2023,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f200,f199,f198,f2011,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f2011,plain,
    ( ~ v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))
    | spl11_6 ),
    inference(unit_resulting_resolution,[],[f200,f313,f504,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f504,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl11_6 ),
    inference(avatar_component_clause,[],[f502])).

fof(f115,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2659,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl11_6
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f1644,f2023])).

fof(f2877,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl11_1
    | spl11_6
    | spl11_14
    | ~ spl11_18 ),
    inference(forward_demodulation,[],[f2870,f2023])).

fof(f2870,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl11_1
    | spl11_6
    | spl11_14
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f2159,f2158,f2200,f116,f116,f2197,f183])).

fof(f2197,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl11_6
    | spl11_14 ),
    inference(backward_demodulation,[],[f1631,f2147])).

fof(f116,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f2200,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl11_6
    | ~ spl11_18 ),
    inference(backward_demodulation,[],[f1657,f2147])).

fof(f2158,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl11_1
    | spl11_6 ),
    inference(backward_demodulation,[],[f190,f2147])).

fof(f2159,plain,
    ( v1_funct_1(k1_xboole_0)
    | spl11_6 ),
    inference(backward_demodulation,[],[f200,f2147])).

fof(f2658,plain,
    ( spl11_6
    | spl11_16
    | ~ spl11_18 ),
    inference(avatar_contradiction_clause,[],[f2657])).

fof(f2657,plain,
    ( $false
    | spl11_6
    | spl11_16
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f2646,f2195])).

fof(f2195,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl11_6 ),
    inference(backward_demodulation,[],[f504,f2147])).

fof(f2646,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl11_6
    | spl11_16
    | ~ spl11_18 ),
    inference(unit_resulting_resolution,[],[f2159,f2200,f116,f2627,f2257])).

fof(f2257,plain,
    ( ! [X2,X0,X1] :
        ( v1_partfun1(X1,X2)
        | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X1,X2,X0)
        | ~ v1_funct_1(X1) )
    | spl11_6 ),
    inference(backward_demodulation,[],[f2107,f2147])).

fof(f2107,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0)
        | v1_partfun1(X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
        | ~ v1_funct_2(X1,X2,X0)
        | ~ v1_funct_1(X1) )
    | spl11_6 ),
    inference(superposition,[],[f2028,f187])).

fof(f2028,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | spl11_6 ),
    inference(backward_demodulation,[],[f199,f2023])).

fof(f2627,plain,
    ( ~ v1_partfun1(k1_xboole_0,u1_struct_0(sK0))
    | spl11_6
    | spl11_16 ),
    inference(unit_resulting_resolution,[],[f2159,f116,f2236,f162])).

fof(f2236,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | spl11_6
    | spl11_16 ),
    inference(backward_demodulation,[],[f2069,f2147])).

fof(f2069,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | spl11_6
    | spl11_16 ),
    inference(backward_demodulation,[],[f1645,f2023])).

fof(f1645,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl11_16 ),
    inference(avatar_component_clause,[],[f1643])).

fof(f1666,plain,(
    spl11_18 ),
    inference(avatar_split_clause,[],[f107,f1656])).

fof(f107,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f76])).

fof(f1665,plain,(
    spl11_19 ),
    inference(avatar_split_clause,[],[f108,f1660])).

fof(f1664,plain,(
    spl11_17 ),
    inference(avatar_split_clause,[],[f287,f1647])).

fof(f287,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(unit_resulting_resolution,[],[f226,f241,f181])).

fof(f241,plain,(
    r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f211,f213,f134])).

fof(f213,plain,(
    v4_relat_1(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f108,f158])).

fof(f226,plain,(
    sP10(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(unit_resulting_resolution,[],[f198,f180])).

fof(f197,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f113,f193,f189])).

fof(f113,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).

fof(f196,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f114,f193,f189])).

fof(f114,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (27600)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.45  % (27600)Refutation not found, incomplete strategy% (27600)------------------------------
% 0.21/0.45  % (27600)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (27600)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (27600)Memory used [KB]: 11129
% 0.21/0.45  % (27600)Time elapsed: 0.042 s
% 0.21/0.45  % (27600)------------------------------
% 0.21/0.45  % (27600)------------------------------
% 0.21/0.49  % (27581)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (27653)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 0.21/0.51  % (27599)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (27582)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (27653)Refutation not found, incomplete strategy% (27653)------------------------------
% 0.21/0.51  % (27653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (27653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (27653)Memory used [KB]: 6652
% 0.21/0.51  % (27653)Time elapsed: 0.011 s
% 0.21/0.51  % (27653)------------------------------
% 0.21/0.51  % (27653)------------------------------
% 0.21/0.51  % (27585)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (27580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (27607)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (27592)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (27579)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (27578)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (27601)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (27590)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (27596)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.53  % (27586)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (27599)Refutation not found, incomplete strategy% (27599)------------------------------
% 0.21/0.53  % (27599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (27599)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (27599)Memory used [KB]: 1918
% 0.21/0.53  % (27599)Time elapsed: 0.135 s
% 0.21/0.53  % (27576)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (27599)------------------------------
% 0.21/0.53  % (27599)------------------------------
% 0.21/0.53  % (27583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (27605)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (27604)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (27602)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (27585)Refutation not found, incomplete strategy% (27585)------------------------------
% 0.21/0.54  % (27585)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (27585)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (27585)Memory used [KB]: 10874
% 0.21/0.54  % (27585)Time elapsed: 0.111 s
% 0.21/0.54  % (27585)------------------------------
% 0.21/0.54  % (27585)------------------------------
% 0.21/0.54  % (27584)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (27594)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (27591)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (27606)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (27696)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 0.21/0.55  % (27575)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (27597)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (27595)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (27586)Refutation not found, incomplete strategy% (27586)------------------------------
% 0.21/0.55  % (27586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (27586)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (27586)Memory used [KB]: 10874
% 0.21/0.55  % (27586)Time elapsed: 0.114 s
% 0.21/0.55  % (27586)------------------------------
% 0.21/0.55  % (27586)------------------------------
% 0.21/0.56  % (27589)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (27587)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.56  % (27603)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (27593)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.61/0.57  % (27594)Refutation not found, incomplete strategy% (27594)------------------------------
% 1.61/0.57  % (27594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (27594)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  
% 1.61/0.57  % (27594)Memory used [KB]: 10746
% 1.61/0.57  % (27594)Time elapsed: 0.158 s
% 1.61/0.57  % (27594)------------------------------
% 1.61/0.57  % (27594)------------------------------
% 1.61/0.58  % (27587)Refutation not found, incomplete strategy% (27587)------------------------------
% 1.61/0.58  % (27587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.58  % (27587)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.58  
% 1.61/0.58  % (27587)Memory used [KB]: 10874
% 1.61/0.58  % (27587)Time elapsed: 0.180 s
% 1.61/0.58  % (27587)------------------------------
% 1.61/0.58  % (27587)------------------------------
% 1.78/0.60  % (27575)Refutation not found, incomplete strategy% (27575)------------------------------
% 1.78/0.60  % (27575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.61  % (27575)Termination reason: Refutation not found, incomplete strategy
% 1.78/0.61  
% 1.78/0.61  % (27575)Memory used [KB]: 2046
% 1.78/0.61  % (27575)Time elapsed: 0.192 s
% 1.78/0.61  % (27575)------------------------------
% 1.78/0.61  % (27575)------------------------------
% 2.07/0.63  % (27706)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.07/0.64  % (27714)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.14/0.67  % (27696)Refutation not found, incomplete strategy% (27696)------------------------------
% 2.14/0.67  % (27696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.68  % (27696)Termination reason: Refutation not found, incomplete strategy
% 2.14/0.68  
% 2.14/0.68  % (27696)Memory used [KB]: 6268
% 2.14/0.68  % (27696)Time elapsed: 0.132 s
% 2.14/0.68  % (27696)------------------------------
% 2.14/0.68  % (27696)------------------------------
% 2.14/0.68  % (27719)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.14/0.70  % (27727)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.64/0.71  % (27732)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.64/0.74  % (27739)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 3.05/0.79  % (27754)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.05/0.81  % (27581)Time limit reached!
% 3.05/0.81  % (27581)------------------------------
% 3.05/0.81  % (27581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.81  % (27581)Termination reason: Time limit
% 3.05/0.81  % (27581)Termination phase: Saturation
% 3.05/0.81  
% 3.05/0.81  % (27581)Memory used [KB]: 8571
% 3.05/0.81  % (27581)Time elapsed: 0.400 s
% 3.05/0.81  % (27581)------------------------------
% 3.05/0.81  % (27581)------------------------------
% 3.81/0.90  % (27589)Time limit reached!
% 3.81/0.90  % (27589)------------------------------
% 3.81/0.90  % (27589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.92  % (27589)Termination reason: Time limit
% 3.81/0.92  % (27589)Termination phase: Saturation
% 3.81/0.92  
% 3.81/0.92  % (27589)Memory used [KB]: 8315
% 3.81/0.92  % (27589)Time elapsed: 0.500 s
% 3.81/0.92  % (27589)------------------------------
% 3.81/0.92  % (27589)------------------------------
% 4.18/0.94  % (27576)Time limit reached!
% 4.18/0.94  % (27576)------------------------------
% 4.18/0.94  % (27576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.94  % (27576)Termination reason: Time limit
% 4.18/0.94  
% 4.18/0.94  % (27576)Memory used [KB]: 7291
% 4.18/0.94  % (27576)Time elapsed: 0.526 s
% 4.18/0.94  % (27576)------------------------------
% 4.18/0.94  % (27576)------------------------------
% 4.18/0.95  % (27578)Refutation not found, incomplete strategy% (27578)------------------------------
% 4.18/0.95  % (27578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.95  % (27578)Termination reason: Refutation not found, incomplete strategy
% 4.18/0.95  
% 4.18/0.95  % (27578)Memory used [KB]: 14328
% 4.18/0.95  % (27578)Time elapsed: 0.523 s
% 4.18/0.95  % (27578)------------------------------
% 4.18/0.95  % (27578)------------------------------
% 4.18/0.96  % (27805)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 4.18/0.97  % (27714)Time limit reached!
% 4.18/0.97  % (27714)------------------------------
% 4.18/0.97  % (27714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.18/0.97  % (27714)Termination reason: Time limit
% 4.18/0.97  % (27714)Termination phase: Saturation
% 4.18/0.97  
% 4.18/0.97  % (27714)Memory used [KB]: 8059
% 4.18/0.97  % (27714)Time elapsed: 0.400 s
% 4.18/0.97  % (27714)------------------------------
% 4.18/0.97  % (27714)------------------------------
% 4.58/1.01  % (27719)Time limit reached!
% 4.58/1.01  % (27719)------------------------------
% 4.58/1.01  % (27719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.02  % (27606)Time limit reached!
% 4.58/1.02  % (27606)------------------------------
% 4.58/1.02  % (27606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.02  % (27583)Time limit reached!
% 4.58/1.02  % (27583)------------------------------
% 4.58/1.02  % (27583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.02  % (27583)Termination reason: Time limit
% 4.58/1.02  % (27583)Termination phase: Saturation
% 4.58/1.02  
% 4.58/1.02  % (27583)Memory used [KB]: 10490
% 4.58/1.02  % (27583)Time elapsed: 0.600 s
% 4.58/1.02  % (27583)------------------------------
% 4.58/1.02  % (27583)------------------------------
% 4.58/1.03  % (27719)Termination reason: Time limit
% 4.58/1.03  
% 4.58/1.03  % (27719)Memory used [KB]: 13304
% 4.58/1.03  % (27719)Time elapsed: 0.433 s
% 4.58/1.03  % (27719)------------------------------
% 4.58/1.03  % (27719)------------------------------
% 4.58/1.03  % (27593)Time limit reached!
% 4.58/1.03  % (27593)------------------------------
% 4.58/1.03  % (27593)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.58/1.03  % (27593)Termination reason: Time limit
% 4.58/1.03  % (27593)Termination phase: Saturation
% 4.58/1.03  
% 4.58/1.03  % (27593)Memory used [KB]: 16119
% 4.58/1.03  % (27593)Time elapsed: 0.600 s
% 4.58/1.03  % (27593)------------------------------
% 4.58/1.03  % (27593)------------------------------
% 4.58/1.04  % (27606)Termination reason: Time limit
% 4.58/1.04  
% 4.58/1.04  % (27606)Memory used [KB]: 7419
% 4.58/1.04  % (27606)Time elapsed: 0.620 s
% 4.58/1.04  % (27606)------------------------------
% 4.58/1.04  % (27606)------------------------------
% 4.58/1.05  % (27816)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.58/1.05  % (27815)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.62/1.08  % (27817)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.62/1.10  % (27818)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.62/1.13  % (27819)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.62/1.15  % (27820)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 5.62/1.16  % (27821)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.32/1.17  % (27822)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 6.32/1.18  % (27604)Refutation found. Thanks to Tanya!
% 6.32/1.18  % SZS status Theorem for theBenchmark
% 6.32/1.18  % SZS output start Proof for theBenchmark
% 6.32/1.18  fof(f4837,plain,(
% 6.32/1.18    $false),
% 6.32/1.18    inference(avatar_sat_refutation,[],[f196,f197,f1664,f1665,f1666,f2658,f2879,f3052,f3053,f3082,f4493,f4805,f4832,f4835,f4836])).
% 6.32/1.18  fof(f4836,plain,(
% 6.32/1.18    ~spl11_7 | spl11_1 | ~spl11_6 | ~spl11_18 | ~spl11_19 | ~spl11_20),
% 6.32/1.18    inference(avatar_split_clause,[],[f4833,f4483,f1660,f1656,f502,f189,f506])).
% 6.32/1.18  fof(f506,plain,(
% 6.32/1.18    spl11_7 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).
% 6.32/1.18  fof(f189,plain,(
% 6.32/1.18    spl11_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 6.32/1.18  fof(f502,plain,(
% 6.32/1.18    spl11_6 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).
% 6.32/1.18  fof(f1656,plain,(
% 6.32/1.18    spl11_18 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).
% 6.32/1.18  fof(f1660,plain,(
% 6.32/1.18    spl11_19 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).
% 6.32/1.18  fof(f4483,plain,(
% 6.32/1.18    spl11_20 <=> v1_funct_1(sK2)),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).
% 6.32/1.18  fof(f4833,plain,(
% 6.32/1.18    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl11_1 | ~spl11_6 | ~spl11_18 | ~spl11_19 | ~spl11_20)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f4484,f191,f1657,f1661,f313,f503,f184])).
% 6.32/1.18  fof(f184,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(duplicate_literal_removal,[],[f170])).
% 6.32/1.18  fof(f170,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(equality_resolution,[],[f128])).
% 6.32/1.18  fof(f128,plain,(
% 6.32/1.18    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f82])).
% 6.32/1.18  fof(f82,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.32/1.18    inference(nnf_transformation,[],[f49])).
% 6.32/1.18  fof(f49,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.32/1.18    inference(flattening,[],[f48])).
% 6.32/1.18  fof(f48,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.32/1.18    inference(ennf_transformation,[],[f28])).
% 6.32/1.18  fof(f28,axiom,(
% 6.32/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 6.32/1.18  fof(f503,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~spl11_6),
% 6.32/1.18    inference(avatar_component_clause,[],[f502])).
% 6.32/1.18  fof(f313,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f216,f253,f181])).
% 6.32/1.18  fof(f181,plain,(
% 6.32/1.18    ( ! [X2,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~sP10(X3,X2)) )),
% 6.32/1.18    inference(general_splitting,[],[f167,f180_D])).
% 6.32/1.18  fof(f180,plain,(
% 6.32/1.18    ( ! [X2,X0,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | sP10(X3,X2)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f180_D])).
% 6.32/1.18  fof(f180_D,plain,(
% 6.32/1.18    ( ! [X2,X3] : (( ! [X0] : ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) <=> ~sP10(X3,X2)) )),
% 6.32/1.18    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP10])])).
% 6.32/1.18  fof(f167,plain,(
% 6.32/1.18    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f69])).
% 6.32/1.18  fof(f69,plain,(
% 6.32/1.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 6.32/1.18    inference(flattening,[],[f68])).
% 6.32/1.18  fof(f68,plain,(
% 6.32/1.18    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 6.32/1.18    inference(ennf_transformation,[],[f16])).
% 6.32/1.18  fof(f16,axiom,(
% 6.32/1.18    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).
% 6.32/1.18  fof(f253,plain,(
% 6.32/1.18    r1_tarski(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f211,f223,f134])).
% 6.32/1.18  fof(f134,plain,(
% 6.32/1.18    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f89])).
% 6.32/1.18  fof(f89,plain,(
% 6.32/1.18    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 6.32/1.18    inference(nnf_transformation,[],[f51])).
% 6.32/1.18  fof(f51,plain,(
% 6.32/1.18    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.32/1.18    inference(ennf_transformation,[],[f10])).
% 6.32/1.18  fof(f10,axiom,(
% 6.32/1.18    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 6.32/1.18  fof(f223,plain,(
% 6.32/1.18    v4_relat_1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f198,f158])).
% 6.32/1.18  fof(f158,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f59])).
% 6.32/1.18  fof(f59,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.32/1.18    inference(ennf_transformation,[],[f35])).
% 6.32/1.18  fof(f35,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.32/1.18    inference(pure_predicate_removal,[],[f13])).
% 6.32/1.18  fof(f13,axiom,(
% 6.32/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.32/1.18  fof(f198,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.32/1.18    inference(forward_demodulation,[],[f111,f112])).
% 6.32/1.18  fof(f112,plain,(
% 6.32/1.18    sK2 = sK3),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f76,plain,(
% 6.32/1.18    ((((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.32/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f71,f75,f74,f73,f72])).
% 6.32/1.18  fof(f72,plain,(
% 6.32/1.18    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.32/1.18    introduced(choice_axiom,[])).
% 6.32/1.18  fof(f73,plain,(
% 6.32/1.18    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 6.32/1.18    introduced(choice_axiom,[])).
% 6.32/1.18  fof(f74,plain,(
% 6.32/1.18    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(X2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(X2,sK0,sK1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 6.32/1.18    introduced(choice_axiom,[])).
% 6.32/1.18  fof(f75,plain,(
% 6.32/1.18    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)) & (v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) & v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) & v1_funct_1(sK3))),
% 6.32/1.18    introduced(choice_axiom,[])).
% 6.32/1.18  fof(f71,plain,(
% 6.32/1.18    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.32/1.18    inference(flattening,[],[f70])).
% 6.32/1.18  fof(f70,plain,(
% 6.32/1.18    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.32/1.18    inference(nnf_transformation,[],[f37])).
% 6.32/1.18  fof(f37,plain,(
% 6.32/1.18    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.32/1.18    inference(flattening,[],[f36])).
% 6.32/1.18  fof(f36,plain,(
% 6.32/1.18    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.32/1.18    inference(ennf_transformation,[],[f31])).
% 6.32/1.18  fof(f31,negated_conjecture,(
% 6.32/1.18    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 6.32/1.18    inference(negated_conjecture,[],[f30])).
% 6.32/1.18  fof(f30,conjecture,(
% 6.32/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 6.32/1.18  fof(f111,plain,(
% 6.32/1.18    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f211,plain,(
% 6.32/1.18    v1_relat_1(sK2)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f108,f156])).
% 6.32/1.18  fof(f156,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f57])).
% 6.32/1.18  fof(f57,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.32/1.18    inference(ennf_transformation,[],[f12])).
% 6.32/1.18  fof(f12,axiom,(
% 6.32/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 6.32/1.18  fof(f108,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f216,plain,(
% 6.32/1.18    sP10(sK2,u1_struct_0(sK1))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f108,f180])).
% 6.32/1.18  fof(f1661,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl11_19),
% 6.32/1.18    inference(avatar_component_clause,[],[f1660])).
% 6.32/1.18  fof(f1657,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl11_18),
% 6.32/1.18    inference(avatar_component_clause,[],[f1656])).
% 6.32/1.18  fof(f191,plain,(
% 6.32/1.18    ~v5_pre_topc(sK2,sK0,sK1) | spl11_1),
% 6.32/1.18    inference(avatar_component_clause,[],[f189])).
% 6.32/1.18  fof(f4484,plain,(
% 6.32/1.18    v1_funct_1(sK2) | ~spl11_20),
% 6.32/1.18    inference(avatar_component_clause,[],[f4483])).
% 6.32/1.18  fof(f105,plain,(
% 6.32/1.18    l1_pre_topc(sK1)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f104,plain,(
% 6.32/1.18    v2_pre_topc(sK1)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f103,plain,(
% 6.32/1.18    l1_pre_topc(sK0)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f102,plain,(
% 6.32/1.18    v2_pre_topc(sK0)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f4835,plain,(
% 6.32/1.18    spl11_7 | ~spl11_2 | ~spl11_6 | ~spl11_20),
% 6.32/1.18    inference(avatar_split_clause,[],[f4834,f4483,f502,f193,f506])).
% 6.32/1.18  fof(f193,plain,(
% 6.32/1.18    spl11_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 6.32/1.18  fof(f4834,plain,(
% 6.32/1.18    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl11_2 | ~spl11_6 | ~spl11_20)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f105,f4484,f104,f203,f247,f313,f3083,f199,f198,f503,f182])).
% 6.32/1.18  fof(f182,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(duplicate_literal_removal,[],[f168])).
% 6.32/1.18  fof(f168,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(equality_resolution,[],[f126])).
% 6.32/1.18  fof(f126,plain,(
% 6.32/1.18    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f81])).
% 6.32/1.18  fof(f81,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.32/1.18    inference(nnf_transformation,[],[f47])).
% 6.32/1.18  fof(f47,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.32/1.18    inference(flattening,[],[f46])).
% 6.32/1.18  fof(f46,plain,(
% 6.32/1.18    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.32/1.18    inference(ennf_transformation,[],[f29])).
% 6.32/1.18  fof(f29,axiom,(
% 6.32/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 6.32/1.18  fof(f199,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.32/1.18    inference(forward_demodulation,[],[f110,f112])).
% 6.32/1.18  fof(f110,plain,(
% 6.32/1.18    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f3083,plain,(
% 6.32/1.18    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl11_2),
% 6.32/1.18    inference(forward_demodulation,[],[f194,f112])).
% 6.32/1.18  fof(f194,plain,(
% 6.32/1.18    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl11_2),
% 6.32/1.18    inference(avatar_component_clause,[],[f193])).
% 6.32/1.18  fof(f247,plain,(
% 6.32/1.18    l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f202,f137])).
% 6.32/1.18  fof(f137,plain,(
% 6.32/1.18    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f53])).
% 6.32/1.18  fof(f53,plain,(
% 6.32/1.18    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 6.32/1.18    inference(ennf_transformation,[],[f33])).
% 6.32/1.18  fof(f33,plain,(
% 6.32/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 6.32/1.18    inference(pure_predicate_removal,[],[f25])).
% 6.32/1.18  fof(f25,axiom,(
% 6.32/1.18    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 6.32/1.18  fof(f202,plain,(
% 6.32/1.18    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f103,f118])).
% 6.32/1.18  fof(f118,plain,(
% 6.32/1.18    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f39])).
% 6.32/1.18  fof(f39,plain,(
% 6.32/1.18    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.32/1.18    inference(ennf_transformation,[],[f26])).
% 6.32/1.18  fof(f26,axiom,(
% 6.32/1.18    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 6.32/1.18  fof(f203,plain,(
% 6.32/1.18    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f123])).
% 6.32/1.18  fof(f123,plain,(
% 6.32/1.18    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f43])).
% 6.32/1.18  fof(f43,plain,(
% 6.32/1.18    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.32/1.18    inference(flattening,[],[f42])).
% 6.32/1.18  fof(f42,plain,(
% 6.32/1.18    ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.32/1.18    inference(ennf_transformation,[],[f32])).
% 6.32/1.18  fof(f32,plain,(
% 6.32/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 6.32/1.18    inference(pure_predicate_removal,[],[f27])).
% 6.32/1.18  fof(f27,axiom,(
% 6.32/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 6.32/1.18  fof(f4832,plain,(
% 6.32/1.18    spl11_1 | ~spl11_14 | ~spl11_16 | ~spl11_17 | ~spl11_18 | ~spl11_19 | ~spl11_20),
% 6.32/1.18    inference(avatar_contradiction_clause,[],[f4831])).
% 6.32/1.18  fof(f4831,plain,(
% 6.32/1.18    $false | (spl11_1 | ~spl11_14 | ~spl11_16 | ~spl11_17 | ~spl11_18 | ~spl11_19 | ~spl11_20)),
% 6.32/1.18    inference(subsumption_resolution,[],[f4830,f1648])).
% 6.32/1.18  fof(f1648,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl11_17),
% 6.32/1.18    inference(avatar_component_clause,[],[f1647])).
% 6.32/1.18  fof(f1647,plain,(
% 6.32/1.18    spl11_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_17])])).
% 6.32/1.18  fof(f4830,plain,(
% 6.32/1.18    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl11_1 | ~spl11_14 | ~spl11_16 | ~spl11_18 | ~spl11_19 | ~spl11_20)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f4484,f191,f1657,f1661,f1644,f1630,f182])).
% 6.32/1.18  fof(f1630,plain,(
% 6.32/1.18    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl11_14),
% 6.32/1.18    inference(avatar_component_clause,[],[f1629])).
% 6.32/1.18  fof(f1629,plain,(
% 6.32/1.18    spl11_14 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).
% 6.32/1.18  fof(f1644,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl11_16),
% 6.32/1.18    inference(avatar_component_clause,[],[f1643])).
% 6.32/1.18  fof(f1643,plain,(
% 6.32/1.18    spl11_16 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.32/1.18    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).
% 6.32/1.18  fof(f4805,plain,(
% 6.32/1.18    ~spl11_2 | spl11_14 | ~spl11_16 | ~spl11_17 | ~spl11_20),
% 6.32/1.18    inference(avatar_contradiction_clause,[],[f4804])).
% 6.32/1.18  fof(f4804,plain,(
% 6.32/1.18    $false | (~spl11_2 | spl11_14 | ~spl11_16 | ~spl11_17 | ~spl11_20)),
% 6.32/1.18    inference(subsumption_resolution,[],[f4803,f1648])).
% 6.32/1.18  fof(f4803,plain,(
% 6.32/1.18    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl11_2 | spl11_14 | ~spl11_16 | ~spl11_20)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f4484,f206,f249,f1631,f3083,f199,f198,f1644,f184])).
% 6.32/1.18  fof(f1631,plain,(
% 6.32/1.18    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl11_14),
% 6.32/1.18    inference(avatar_component_clause,[],[f1629])).
% 6.32/1.18  fof(f249,plain,(
% 6.32/1.18    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f205,f137])).
% 6.32/1.18  fof(f205,plain,(
% 6.32/1.18    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f105,f118])).
% 6.32/1.18  fof(f206,plain,(
% 6.32/1.18    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f104,f105,f123])).
% 6.32/1.18  fof(f4493,plain,(
% 6.32/1.18    spl11_20),
% 6.32/1.18    inference(avatar_split_clause,[],[f200,f4483])).
% 6.32/1.18  fof(f200,plain,(
% 6.32/1.18    v1_funct_1(sK2)),
% 6.32/1.18    inference(forward_demodulation,[],[f109,f112])).
% 6.32/1.18  fof(f109,plain,(
% 6.32/1.18    v1_funct_1(sK3)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f3082,plain,(
% 6.32/1.18    spl11_2 | ~spl11_14 | ~spl11_16 | ~spl11_17),
% 6.32/1.18    inference(avatar_contradiction_clause,[],[f3081])).
% 6.32/1.18  fof(f3081,plain,(
% 6.32/1.18    $false | (spl11_2 | ~spl11_14 | ~spl11_16 | ~spl11_17)),
% 6.32/1.18    inference(subsumption_resolution,[],[f3080,f1648])).
% 6.32/1.18  fof(f3080,plain,(
% 6.32/1.18    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (spl11_2 | ~spl11_14 | ~spl11_16)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f200,f206,f249,f1630,f1640,f199,f198,f1644,f185])).
% 6.32/1.18  fof(f185,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(duplicate_literal_removal,[],[f171])).
% 6.32/1.18  fof(f171,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(equality_resolution,[],[f127])).
% 6.32/1.18  fof(f127,plain,(
% 6.32/1.18    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f82])).
% 6.32/1.18  fof(f1640,plain,(
% 6.32/1.18    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl11_2),
% 6.32/1.18    inference(forward_demodulation,[],[f195,f112])).
% 6.32/1.18  fof(f195,plain,(
% 6.32/1.18    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl11_2),
% 6.32/1.18    inference(avatar_component_clause,[],[f193])).
% 6.32/1.18  fof(f3053,plain,(
% 6.32/1.18    spl11_7 | ~spl11_1 | ~spl11_6 | ~spl11_18 | ~spl11_19),
% 6.32/1.18    inference(avatar_split_clause,[],[f3050,f1660,f1656,f502,f189,f506])).
% 6.32/1.18  fof(f3050,plain,(
% 6.32/1.18    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl11_1 | ~spl11_6 | ~spl11_18 | ~spl11_19)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f200,f190,f1657,f1661,f313,f503,f185])).
% 6.32/1.18  fof(f190,plain,(
% 6.32/1.18    v5_pre_topc(sK2,sK0,sK1) | ~spl11_1),
% 6.32/1.18    inference(avatar_component_clause,[],[f189])).
% 6.32/1.18  fof(f3052,plain,(
% 6.32/1.18    ~spl11_7 | spl11_2 | ~spl11_6),
% 6.32/1.18    inference(avatar_split_clause,[],[f3051,f502,f193,f506])).
% 6.32/1.18  fof(f3051,plain,(
% 6.32/1.18    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (spl11_2 | ~spl11_6)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f105,f200,f104,f203,f247,f1640,f313,f199,f198,f503,f183])).
% 6.32/1.18  fof(f183,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(duplicate_literal_removal,[],[f169])).
% 6.32/1.18  fof(f169,plain,(
% 6.32/1.18    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(equality_resolution,[],[f125])).
% 6.32/1.18  fof(f125,plain,(
% 6.32/1.18    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f81])).
% 6.32/1.18  fof(f2879,plain,(
% 6.32/1.18    ~spl11_1 | spl11_6 | spl11_14 | ~spl11_16 | ~spl11_18),
% 6.32/1.18    inference(avatar_contradiction_clause,[],[f2878])).
% 6.32/1.18  fof(f2878,plain,(
% 6.32/1.18    $false | (~spl11_1 | spl11_6 | spl11_14 | ~spl11_16 | ~spl11_18)),
% 6.32/1.18    inference(subsumption_resolution,[],[f2877,f2660])).
% 6.32/1.18  fof(f2660,plain,(
% 6.32/1.18    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (spl11_6 | ~spl11_16)),
% 6.32/1.18    inference(forward_demodulation,[],[f2659,f2147])).
% 6.32/1.18  fof(f2147,plain,(
% 6.32/1.18    k1_xboole_0 = sK2 | spl11_6),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f2113,f131])).
% 6.32/1.18  fof(f131,plain,(
% 6.32/1.18    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 6.32/1.18    inference(cnf_transformation,[],[f88])).
% 6.32/1.18  fof(f88,plain,(
% 6.32/1.18    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 6.32/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f50,f87])).
% 6.32/1.18  fof(f87,plain,(
% 6.32/1.18    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK6(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK6(X0),X0)))),
% 6.32/1.18    introduced(choice_axiom,[])).
% 6.32/1.18  fof(f50,plain,(
% 6.32/1.18    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 6.32/1.18    inference(ennf_transformation,[],[f18])).
% 6.32/1.18  fof(f18,axiom,(
% 6.32/1.18    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_mcart_1)).
% 6.32/1.18  fof(f2113,plain,(
% 6.32/1.18    ( ! [X0] : (~r2_hidden(X0,sK2)) ) | spl11_6),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f2100,f179])).
% 6.32/1.18  fof(f179,plain,(
% 6.32/1.18    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 6.32/1.18    inference(general_splitting,[],[f166,f178_D])).
% 6.32/1.18  fof(f178,plain,(
% 6.32/1.18    ( ! [X2,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | sP9(X1)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f178_D])).
% 6.32/1.18  fof(f178_D,plain,(
% 6.32/1.18    ( ! [X1] : (( ! [X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2))) ) <=> ~sP9(X1)) )),
% 6.32/1.18    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 6.32/1.18  fof(f166,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f67])).
% 6.32/1.18  fof(f67,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 6.32/1.18    inference(ennf_transformation,[],[f9])).
% 6.32/1.18  fof(f9,axiom,(
% 6.32/1.18    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 6.32/1.18  fof(f2100,plain,(
% 6.32/1.18    sP9(sK2) | spl11_6),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f115,f2087,f178])).
% 6.32/1.18  fof(f2087,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl11_6),
% 6.32/1.18    inference(forward_demodulation,[],[f2027,f175])).
% 6.32/1.18  fof(f175,plain,(
% 6.32/1.18    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.32/1.18    inference(equality_resolution,[],[f150])).
% 6.32/1.18  fof(f150,plain,(
% 6.32/1.18    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 6.32/1.18    inference(cnf_transformation,[],[f99])).
% 6.32/1.18  fof(f99,plain,(
% 6.32/1.18    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.32/1.18    inference(flattening,[],[f98])).
% 6.32/1.18  fof(f98,plain,(
% 6.32/1.18    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 6.32/1.18    inference(nnf_transformation,[],[f5])).
% 6.32/1.18  fof(f5,axiom,(
% 6.32/1.18    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 6.32/1.18  fof(f2027,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | spl11_6),
% 6.32/1.18    inference(backward_demodulation,[],[f198,f2023])).
% 6.32/1.18  fof(f2023,plain,(
% 6.32/1.18    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl11_6),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f200,f199,f198,f2011,f187])).
% 6.32/1.18  fof(f187,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.32/1.18    inference(duplicate_literal_removal,[],[f163])).
% 6.32/1.18  fof(f163,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 6.32/1.18    inference(cnf_transformation,[],[f64])).
% 6.32/1.18  fof(f64,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 6.32/1.18    inference(flattening,[],[f63])).
% 6.32/1.18  fof(f63,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 6.32/1.18    inference(ennf_transformation,[],[f22])).
% 6.32/1.18  fof(f22,axiom,(
% 6.32/1.18    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 6.32/1.18  fof(f2011,plain,(
% 6.32/1.18    ~v1_partfun1(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))) | spl11_6),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f200,f313,f504,f162])).
% 6.32/1.18  fof(f162,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f62])).
% 6.32/1.18  fof(f62,plain,(
% 6.32/1.18    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.32/1.18    inference(flattening,[],[f61])).
% 6.32/1.18  fof(f61,plain,(
% 6.32/1.18    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.32/1.18    inference(ennf_transformation,[],[f19])).
% 6.32/1.18  fof(f19,axiom,(
% 6.32/1.18    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).
% 6.32/1.18  fof(f504,plain,(
% 6.32/1.18    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl11_6),
% 6.32/1.18    inference(avatar_component_clause,[],[f502])).
% 6.32/1.18  fof(f115,plain,(
% 6.32/1.18    v1_xboole_0(k1_xboole_0)),
% 6.32/1.18    inference(cnf_transformation,[],[f3])).
% 6.32/1.18  fof(f3,axiom,(
% 6.32/1.18    v1_xboole_0(k1_xboole_0)),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 6.32/1.18  fof(f2659,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl11_6 | ~spl11_16)),
% 6.32/1.18    inference(forward_demodulation,[],[f1644,f2023])).
% 6.32/1.18  fof(f2877,plain,(
% 6.32/1.18    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl11_1 | spl11_6 | spl11_14 | ~spl11_18)),
% 6.32/1.18    inference(forward_demodulation,[],[f2870,f2023])).
% 6.32/1.18  fof(f2870,plain,(
% 6.32/1.18    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl11_1 | spl11_6 | spl11_14 | ~spl11_18)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f102,f103,f104,f105,f2159,f2158,f2200,f116,f116,f2197,f183])).
% 6.32/1.18  fof(f2197,plain,(
% 6.32/1.18    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl11_6 | spl11_14)),
% 6.32/1.18    inference(backward_demodulation,[],[f1631,f2147])).
% 6.32/1.18  fof(f116,plain,(
% 6.32/1.18    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 6.32/1.18    inference(cnf_transformation,[],[f6])).
% 6.32/1.18  fof(f6,axiom,(
% 6.32/1.18    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 6.32/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 6.32/1.18  fof(f2200,plain,(
% 6.32/1.18    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (spl11_6 | ~spl11_18)),
% 6.32/1.18    inference(backward_demodulation,[],[f1657,f2147])).
% 6.32/1.18  fof(f2158,plain,(
% 6.32/1.18    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl11_1 | spl11_6)),
% 6.32/1.18    inference(backward_demodulation,[],[f190,f2147])).
% 6.32/1.18  fof(f2159,plain,(
% 6.32/1.18    v1_funct_1(k1_xboole_0) | spl11_6),
% 6.32/1.18    inference(backward_demodulation,[],[f200,f2147])).
% 6.32/1.18  fof(f2658,plain,(
% 6.32/1.18    spl11_6 | spl11_16 | ~spl11_18),
% 6.32/1.18    inference(avatar_contradiction_clause,[],[f2657])).
% 6.32/1.18  fof(f2657,plain,(
% 6.32/1.18    $false | (spl11_6 | spl11_16 | ~spl11_18)),
% 6.32/1.18    inference(subsumption_resolution,[],[f2646,f2195])).
% 6.32/1.18  fof(f2195,plain,(
% 6.32/1.18    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl11_6),
% 6.32/1.18    inference(backward_demodulation,[],[f504,f2147])).
% 6.32/1.18  fof(f2646,plain,(
% 6.32/1.18    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (spl11_6 | spl11_16 | ~spl11_18)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f2159,f2200,f116,f2627,f2257])).
% 6.32/1.18  fof(f2257,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_partfun1(X1,X2) | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1)) ) | spl11_6),
% 6.32/1.18    inference(backward_demodulation,[],[f2107,f2147])).
% 6.32/1.18  fof(f2107,plain,(
% 6.32/1.18    ( ! [X2,X0,X1] : (v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),X0) | v1_partfun1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1)) ) | spl11_6),
% 6.32/1.18    inference(superposition,[],[f2028,f187])).
% 6.32/1.18  fof(f2028,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | spl11_6),
% 6.32/1.18    inference(backward_demodulation,[],[f199,f2023])).
% 6.32/1.18  fof(f2627,plain,(
% 6.32/1.18    ~v1_partfun1(k1_xboole_0,u1_struct_0(sK0)) | (spl11_6 | spl11_16)),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f2159,f116,f2236,f162])).
% 6.32/1.18  fof(f2236,plain,(
% 6.32/1.18    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (spl11_6 | spl11_16)),
% 6.32/1.18    inference(backward_demodulation,[],[f2069,f2147])).
% 6.32/1.18  fof(f2069,plain,(
% 6.32/1.18    ~v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (spl11_6 | spl11_16)),
% 6.32/1.18    inference(backward_demodulation,[],[f1645,f2023])).
% 6.32/1.18  fof(f1645,plain,(
% 6.32/1.18    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl11_16),
% 6.32/1.18    inference(avatar_component_clause,[],[f1643])).
% 6.32/1.18  fof(f1666,plain,(
% 6.32/1.18    spl11_18),
% 6.32/1.18    inference(avatar_split_clause,[],[f107,f1656])).
% 6.32/1.18  fof(f107,plain,(
% 6.32/1.18    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f1665,plain,(
% 6.32/1.18    spl11_19),
% 6.32/1.18    inference(avatar_split_clause,[],[f108,f1660])).
% 6.32/1.18  fof(f1664,plain,(
% 6.32/1.18    spl11_17),
% 6.32/1.18    inference(avatar_split_clause,[],[f287,f1647])).
% 6.32/1.18  fof(f287,plain,(
% 6.32/1.18    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f226,f241,f181])).
% 6.32/1.18  fof(f241,plain,(
% 6.32/1.18    r1_tarski(k1_relat_1(sK2),u1_struct_0(sK0))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f211,f213,f134])).
% 6.32/1.18  fof(f213,plain,(
% 6.32/1.18    v4_relat_1(sK2,u1_struct_0(sK0))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f108,f158])).
% 6.32/1.18  fof(f226,plain,(
% 6.32/1.18    sP10(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.32/1.18    inference(unit_resulting_resolution,[],[f198,f180])).
% 6.32/1.18  fof(f197,plain,(
% 6.32/1.18    spl11_1 | spl11_2),
% 6.32/1.18    inference(avatar_split_clause,[],[f113,f193,f189])).
% 6.32/1.18  fof(f113,plain,(
% 6.32/1.18    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  fof(f196,plain,(
% 6.32/1.18    ~spl11_1 | ~spl11_2),
% 6.32/1.18    inference(avatar_split_clause,[],[f114,f193,f189])).
% 6.32/1.18  fof(f114,plain,(
% 6.32/1.18    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 6.32/1.18    inference(cnf_transformation,[],[f76])).
% 6.32/1.18  % SZS output end Proof for theBenchmark
% 6.32/1.18  % (27604)------------------------------
% 6.32/1.18  % (27604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.32/1.18  % (27604)Termination reason: Refutation
% 6.32/1.18  
% 6.32/1.18  % (27604)Memory used [KB]: 13048
% 6.32/1.18  % (27604)Time elapsed: 0.748 s
% 6.32/1.18  % (27604)------------------------------
% 6.32/1.18  % (27604)------------------------------
% 6.32/1.18  % (27572)Success in time 0.813 s
%------------------------------------------------------------------------------
