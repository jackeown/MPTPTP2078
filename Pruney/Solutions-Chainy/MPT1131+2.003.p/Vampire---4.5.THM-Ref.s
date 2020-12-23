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
% DateTime   : Thu Dec  3 13:09:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 473 expanded)
%              Number of leaves         :   26 ( 139 expanded)
%              Depth                    :   10
%              Number of atoms          :  489 (3366 expanded)
%              Number of equality atoms :   10 ( 222 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f242,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f54,f89,f108,f115,f120,f135,f169,f174,f182,f198,f201,f210,f216,f218,f220,f223,f225,f232,f233,f236,f239,f241])).

fof(f241,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | spl5_7 ),
    inference(avatar_split_clause,[],[f240,f118,f99,f96])).

fof(f96,plain,
    ( spl5_4
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f99,plain,
    ( spl5_5
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f118,plain,
    ( spl5_7
  <=> ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f240,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ) ),
    inference(global_subsumption,[],[f26,f30,f31,f32,f57,f58,f199])).

fof(f199,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ) ),
    inference(superposition,[],[f113,f62])).

fof(f62,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f44,f58])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),X2,X3),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),X2,X3),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ),
    inference(resolution,[],[f67,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | ~ l1_pre_topc(X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f67,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3,X4,X5),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3,X4,X5),X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3))) ) ),
    inference(resolution,[],[f39,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(forward_demodulation,[],[f24,f25])).

fof(f25,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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

fof(f24,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f23,f25])).

fof(f23,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f30,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f26,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f239,plain,(
    spl5_21 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl5_21 ),
    inference(resolution,[],[f228,f28])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f11])).

fof(f228,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl5_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f236,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl5_22 ),
    inference(resolution,[],[f231,f27])).

fof(f27,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f231,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl5_22
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f233,plain,
    ( spl5_1
    | ~ spl5_14
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_19
    | ~ spl5_20
    | spl5_10 ),
    inference(avatar_split_clause,[],[f141,f133,f196,f193,f230,f227,f162,f46])).

fof(f46,plain,
    ( spl5_1
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f162,plain,
    ( spl5_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f193,plain,
    ( spl5_19
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f196,plain,
    ( spl5_20
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f133,plain,
    ( spl5_10
  <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl5_10 ),
    inference(resolution,[],[f134,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f134,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f232,plain,
    ( spl5_1
    | ~ spl5_14
    | ~ spl5_21
    | ~ spl5_22
    | ~ spl5_19
    | ~ spl5_20
    | spl5_9 ),
    inference(avatar_split_clause,[],[f146,f130,f196,f193,f230,f227,f162,f46])).

fof(f130,plain,
    ( spl5_9
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f146,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | spl5_9 ),
    inference(resolution,[],[f131,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f131,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f225,plain,
    ( spl5_2
    | ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl5_2
    | ~ spl5_4 ),
    inference(resolution,[],[f122,f127])).

fof(f127,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_2 ),
    inference(forward_demodulation,[],[f50,f25])).

fof(f50,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl5_2
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f122,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f223,plain,(
    spl5_17 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl5_17 ),
    inference(resolution,[],[f188,f58])).

fof(f188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_17
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f220,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | spl5_15 ),
    inference(avatar_split_clause,[],[f219,f177,f196,f193,f190,f187,f99,f96])).

fof(f190,plain,
    ( spl5_18
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f177,plain,
    ( spl5_15
  <=> m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_15 ),
    inference(resolution,[],[f178,f35])).

fof(f178,plain,
    ( ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f218,plain,(
    spl5_11 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | spl5_11 ),
    inference(resolution,[],[f154,f65])).

fof(f65,plain,(
    ! [X0] : m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f28,f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ) ),
    inference(superposition,[],[f43,f61])).

fof(f61,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f44,f28])).

fof(f154,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl5_11
  <=> m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f216,plain,(
    spl5_18 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl5_18 ),
    inference(resolution,[],[f191,f57])).

fof(f191,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f210,plain,(
    spl5_20 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl5_20 ),
    inference(resolution,[],[f197,f30])).

fof(f197,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f196])).

fof(f201,plain,(
    spl5_19 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | spl5_19 ),
    inference(resolution,[],[f194,f26])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f193])).

fof(f198,plain,
    ( spl5_4
    | ~ spl5_5
    | ~ spl5_17
    | ~ spl5_18
    | ~ spl5_19
    | ~ spl5_20
    | spl5_16 ),
    inference(avatar_split_clause,[],[f185,f180,f196,f193,f190,f187,f99,f96])).

fof(f180,plain,
    ( spl5_16
  <=> v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f185,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_16 ),
    inference(resolution,[],[f181,f36])).

fof(f181,plain,
    ( ~ v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f180])).

fof(f182,plain,
    ( ~ spl5_15
    | ~ spl5_16
    | ~ spl5_7
    | spl5_12 ),
    inference(avatar_split_clause,[],[f175,f156,f118,f180,f177])).

fof(f156,plain,
    ( spl5_12
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f175,plain,
    ( ~ v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl5_7
    | spl5_12 ),
    inference(resolution,[],[f157,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
        | ~ v4_pre_topc(X0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f157,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f156])).

fof(f174,plain,(
    spl5_14 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl5_14 ),
    inference(resolution,[],[f163,f32])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f162])).

fof(f169,plain,
    ( ~ spl5_12
    | spl5_4
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f168,f153,f99,f96,f156])).

fof(f168,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) ),
    inference(global_subsumption,[],[f26,f30,f31,f32,f57,f58,f166])).

fof(f166,plain,
    ( ~ m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1) ),
    inference(superposition,[],[f82,f62])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f37,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f135,plain,
    ( ~ spl5_9
    | ~ spl5_10
    | spl5_3
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f128,f118,f87,f133,f130])).

fof(f87,plain,
    ( spl5_3
  <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f128,plain,
    ( ~ v4_pre_topc(sK4(sK0,sK1,sK2),sK1)
    | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl5_3
    | ~ spl5_7 ),
    inference(resolution,[],[f119,f88])).

fof(f88,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f120,plain,
    ( ~ spl5_1
    | spl5_7 ),
    inference(avatar_split_clause,[],[f116,f118,f46])).

fof(f116,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(global_subsumption,[],[f26,f30,f32,f27,f28,f91])).

fof(f91,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v5_pre_topc(sK2,sK0,sK1) ) ),
    inference(superposition,[],[f34,f61])).

fof(f115,plain,
    ( ~ spl5_2
    | spl5_4 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | ~ spl5_2
    | spl5_4 ),
    inference(resolution,[],[f97,f56])).

fof(f56,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f53,f25])).

fof(f53,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f97,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f108,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f105,f32])).

fof(f105,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_5 ),
    inference(resolution,[],[f100,f59])).

fof(f59,plain,(
    ! [X0] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f42,f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f100,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f89,plain,
    ( spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f85,f87,f46])).

fof(f85,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(global_subsumption,[],[f26,f30,f32,f27,f28,f83])).

fof(f83,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(superposition,[],[f37,f61])).

fof(f54,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f20,f49,f46])).

fof(f20,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f21,f49,f46])).

fof(f21,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (23949)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.43  % (23949)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f242,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f51,f54,f89,f108,f115,f120,f135,f169,f174,f182,f198,f201,f210,f216,f218,f220,f223,f225,f232,f233,f236,f239,f241])).
% 0.20/0.43  fof(f241,plain,(
% 0.20/0.43    ~spl5_4 | ~spl5_5 | spl5_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f240,f118,f99,f96])).
% 0.20/0.43  fof(f96,plain,(
% 0.20/0.43    spl5_4 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    spl5_5 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    spl5_7 <=> ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.43  fof(f240,plain,(
% 0.20/0.43    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) )),
% 0.20/0.43    inference(global_subsumption,[],[f26,f30,f31,f32,f57,f58,f199])).
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)) )),
% 0.20/0.43    inference(superposition,[],[f113,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X1] : (k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)) )),
% 0.20/0.43    inference(resolution,[],[f44,f58])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),X2,X3),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f109])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1),X2,X3),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(X2,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) )),
% 0.20/0.43    inference(resolution,[],[f67,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | ~l1_pre_topc(X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    ( ! [X4,X2,X5,X3] : (~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3,X4,X5),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3,X4,X5),X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),X3)))) )),
% 0.20/0.43    inference(resolution,[],[f39,f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v4_pre_topc(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.20/0.43    inference(forward_demodulation,[],[f24,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    sK2 = sK3),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.20/0.43    inference(negated_conjecture,[],[f7])).
% 0.20/0.43  fof(f7,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.20/0.43    inference(forward_demodulation,[],[f23,f25])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    v2_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    l1_pre_topc(sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    v1_funct_1(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f239,plain,(
% 0.20/0.43    spl5_21),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f238])).
% 0.20/0.43  fof(f238,plain,(
% 0.20/0.43    $false | spl5_21),
% 0.20/0.43    inference(resolution,[],[f228,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | spl5_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f227])).
% 0.20/0.43  fof(f227,plain,(
% 0.20/0.43    spl5_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.20/0.43  fof(f236,plain,(
% 0.20/0.43    spl5_22),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.43  fof(f235,plain,(
% 0.20/0.43    $false | spl5_22),
% 0.20/0.43    inference(resolution,[],[f231,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f231,plain,(
% 0.20/0.43    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | spl5_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f230])).
% 0.20/0.43  fof(f230,plain,(
% 0.20/0.43    spl5_22 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.43  fof(f233,plain,(
% 0.20/0.43    spl5_1 | ~spl5_14 | ~spl5_21 | ~spl5_22 | ~spl5_19 | ~spl5_20 | spl5_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f141,f133,f196,f193,f230,f227,f162,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    spl5_1 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.43  fof(f162,plain,(
% 0.20/0.43    spl5_14 <=> l1_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.43  fof(f193,plain,(
% 0.20/0.43    spl5_19 <=> v1_funct_1(sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.20/0.43  fof(f196,plain,(
% 0.20/0.43    spl5_20 <=> l1_pre_topc(sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    spl5_10 <=> v4_pre_topc(sK4(sK0,sK1,sK2),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | v5_pre_topc(sK2,sK0,sK1) | spl5_10),
% 0.20/0.43    inference(resolution,[],[f134,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (v4_pre_topc(sK4(X0,X1,X2),X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    ~v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | spl5_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f133])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    spl5_1 | ~spl5_14 | ~spl5_21 | ~spl5_22 | ~spl5_19 | ~spl5_20 | spl5_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f146,f130,f196,f193,f230,f227,f162,f46])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    spl5_9 <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.43  fof(f146,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | v5_pre_topc(sK2,sK0,sK1) | spl5_9),
% 0.20/0.43    inference(resolution,[],[f131,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f130])).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    spl5_2 | ~spl5_4),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f224])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    $false | (spl5_2 | ~spl5_4)),
% 0.20/0.43    inference(resolution,[],[f122,f127])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_2),
% 0.20/0.43    inference(forward_demodulation,[],[f50,f25])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl5_2 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f96])).
% 0.20/0.43  fof(f223,plain,(
% 0.20/0.43    spl5_17),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f222])).
% 0.20/0.43  fof(f222,plain,(
% 0.20/0.43    $false | spl5_17),
% 0.20/0.43    inference(resolution,[],[f188,f58])).
% 0.20/0.43  fof(f188,plain,(
% 0.20/0.43    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | spl5_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f187])).
% 0.20/0.43  fof(f187,plain,(
% 0.20/0.43    spl5_17 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.43  fof(f220,plain,(
% 0.20/0.43    spl5_4 | ~spl5_5 | ~spl5_17 | ~spl5_18 | ~spl5_19 | ~spl5_20 | spl5_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f219,f177,f196,f193,f190,f187,f99,f96])).
% 0.20/0.43  fof(f190,plain,(
% 0.20/0.43    spl5_18 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.20/0.43  fof(f177,plain,(
% 0.20/0.43    spl5_15 <=> m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_15),
% 0.20/0.43    inference(resolution,[],[f178,f35])).
% 0.20/0.43  fof(f178,plain,(
% 0.20/0.43    ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | spl5_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f177])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    spl5_11),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.43  fof(f217,plain,(
% 0.20/0.43    $false | spl5_11),
% 0.20/0.43    inference(resolution,[],[f154,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.43    inference(global_subsumption,[],[f28,f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))) )),
% 0.20/0.43    inference(superposition,[],[f43,f61])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.20/0.43    inference(resolution,[],[f44,f28])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    ~m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f153])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    spl5_11 <=> m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.43  fof(f216,plain,(
% 0.20/0.43    spl5_18),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.43  fof(f215,plain,(
% 0.20/0.43    $false | spl5_18),
% 0.20/0.43    inference(resolution,[],[f191,f57])).
% 0.20/0.43  fof(f191,plain,(
% 0.20/0.43    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | spl5_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f190])).
% 0.20/0.43  fof(f210,plain,(
% 0.20/0.43    spl5_20),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f209])).
% 0.20/0.43  fof(f209,plain,(
% 0.20/0.43    $false | spl5_20),
% 0.20/0.43    inference(resolution,[],[f197,f30])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | spl5_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f196])).
% 0.20/0.43  fof(f201,plain,(
% 0.20/0.43    spl5_19),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.43  fof(f200,plain,(
% 0.20/0.43    $false | spl5_19),
% 0.20/0.43    inference(resolution,[],[f194,f26])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    ~v1_funct_1(sK2) | spl5_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f193])).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    spl5_4 | ~spl5_5 | ~spl5_17 | ~spl5_18 | ~spl5_19 | ~spl5_20 | spl5_16),
% 0.20/0.43    inference(avatar_split_clause,[],[f185,f180,f196,f193,f190,f187,f99,f96])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    spl5_16 <=> v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_16),
% 0.20/0.43    inference(resolution,[],[f181,f36])).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    ~v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) | spl5_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f180])).
% 0.20/0.43  fof(f182,plain,(
% 0.20/0.43    ~spl5_15 | ~spl5_16 | ~spl5_7 | spl5_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f175,f156,f118,f180,f177])).
% 0.20/0.43  fof(f156,plain,(
% 0.20/0.43    spl5_12 <=> v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.20/0.43  fof(f175,plain,(
% 0.20/0.43    ~v4_pre_topc(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),sK1) | ~m1_subset_1(sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (~spl5_7 | spl5_12)),
% 0.20/0.43    inference(resolution,[],[f157,f119])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) ) | ~spl5_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f118])).
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) | spl5_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f156])).
% 0.20/0.43  fof(f174,plain,(
% 0.20/0.43    spl5_14),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f173])).
% 0.20/0.43  fof(f173,plain,(
% 0.20/0.43    $false | spl5_14),
% 0.20/0.43    inference(resolution,[],[f163,f32])).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | spl5_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f162])).
% 0.20/0.43  fof(f169,plain,(
% 0.20/0.43    ~spl5_12 | spl5_4 | ~spl5_5 | ~spl5_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f168,f153,f99,f96,f156])).
% 0.20/0.44  fof(f168,plain,(
% 0.20/0.44    ~m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0)),
% 0.20/0.44    inference(global_subsumption,[],[f26,f30,f31,f32,f57,f58,f166])).
% 0.20/0.44  fof(f166,plain,(
% 0.20/0.44    ~m1_subset_1(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v4_pre_topc(k10_relat_1(sK2,sK4(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1,sK2)),sK0) | ~l1_pre_topc(sK1)),
% 0.20/0.44    inference(superposition,[],[f82,f62])).
% 0.20/0.44  fof(f82,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),k1_zfmisc_1(u1_struct_0(X2))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~v4_pre_topc(k8_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X0),X1,sK4(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X0,X1)),X2) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(resolution,[],[f37,f40])).
% 0.20/0.44  fof(f40,plain,(
% 0.20/0.44    ( ! [X0,X1] : (v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f16])).
% 0.20/0.44  fof(f37,plain,(
% 0.20/0.44    ( ! [X2,X0,X1] : (~v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)),X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f14])).
% 0.20/0.44  fof(f135,plain,(
% 0.20/0.44    ~spl5_9 | ~spl5_10 | spl5_3 | ~spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f128,f118,f87,f133,f130])).
% 0.20/0.44  fof(f87,plain,(
% 0.20/0.44    spl5_3 <=> v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0)),
% 0.20/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.44  fof(f128,plain,(
% 0.20/0.44    ~v4_pre_topc(sK4(sK0,sK1,sK2),sK1) | ~m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | (spl5_3 | ~spl5_7)),
% 0.20/0.44    inference(resolution,[],[f119,f88])).
% 0.20/0.44  fof(f88,plain,(
% 0.20/0.44    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | spl5_3),
% 0.20/0.44    inference(avatar_component_clause,[],[f87])).
% 0.20/0.44  fof(f120,plain,(
% 0.20/0.44    ~spl5_1 | spl5_7),
% 0.20/0.44    inference(avatar_split_clause,[],[f116,f118,f46])).
% 0.20/0.44  fof(f116,plain,(
% 0.20/0.44    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~v5_pre_topc(sK2,sK0,sK1)) )),
% 0.20/0.44    inference(global_subsumption,[],[f26,f30,f32,f27,f28,f91])).
% 0.20/0.44  fof(f91,plain,(
% 0.20/0.44    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | ~l1_pre_topc(sK0) | ~v5_pre_topc(sK2,sK0,sK1)) )),
% 0.20/0.44    inference(superposition,[],[f34,f61])).
% 0.20/0.44  fof(f115,plain,(
% 0.20/0.44    ~spl5_2 | spl5_4),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f114])).
% 0.20/0.44  fof(f114,plain,(
% 0.20/0.44    $false | (~spl5_2 | spl5_4)),
% 0.20/0.44    inference(resolution,[],[f97,f56])).
% 0.20/0.44  fof(f56,plain,(
% 0.20/0.44    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_2),
% 0.20/0.44    inference(forward_demodulation,[],[f53,f25])).
% 0.20/0.44  fof(f53,plain,(
% 0.20/0.44    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_2),
% 0.20/0.44    inference(avatar_component_clause,[],[f49])).
% 0.20/0.44  fof(f97,plain,(
% 0.20/0.44    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl5_4),
% 0.20/0.44    inference(avatar_component_clause,[],[f96])).
% 0.20/0.44  fof(f108,plain,(
% 0.20/0.44    spl5_5),
% 0.20/0.44    inference(avatar_contradiction_clause,[],[f107])).
% 0.20/0.44  fof(f107,plain,(
% 0.20/0.44    $false | spl5_5),
% 0.20/0.44    inference(resolution,[],[f105,f32])).
% 0.20/0.44  fof(f105,plain,(
% 0.20/0.44    ~l1_pre_topc(sK0) | spl5_5),
% 0.20/0.44    inference(resolution,[],[f100,f59])).
% 0.20/0.44  fof(f59,plain,(
% 0.20/0.44    ( ! [X0] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(resolution,[],[f42,f33])).
% 0.20/0.44  fof(f33,plain,(
% 0.20/0.44    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f12])).
% 0.20/0.44  fof(f12,plain,(
% 0.20/0.44    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f5])).
% 0.20/0.44  fof(f5,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.44  fof(f42,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 0.20/0.44    inference(cnf_transformation,[],[f17])).
% 0.20/0.44  fof(f17,plain,(
% 0.20/0.44    ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,plain,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => l1_pre_topc(g1_pre_topc(X0,X1)))),
% 0.20/0.44    inference(pure_predicate_removal,[],[f4])).
% 0.20/0.44  fof(f4,axiom,(
% 0.20/0.44    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 0.20/0.44  fof(f100,plain,(
% 0.20/0.44    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_5),
% 0.20/0.44    inference(avatar_component_clause,[],[f99])).
% 0.20/0.44  fof(f89,plain,(
% 0.20/0.44    spl5_1 | ~spl5_3),
% 0.20/0.44    inference(avatar_split_clause,[],[f85,f87,f46])).
% 0.20/0.44  fof(f85,plain,(
% 0.20/0.44    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.44    inference(global_subsumption,[],[f26,f30,f32,f27,f28,f83])).
% 0.20/0.44  fof(f83,plain,(
% 0.20/0.44    ~v4_pre_topc(k10_relat_1(sK2,sK4(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.44    inference(superposition,[],[f37,f61])).
% 0.20/0.44  fof(f54,plain,(
% 0.20/0.44    spl5_1 | spl5_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f20,f49,f46])).
% 0.20/0.44  fof(f20,plain,(
% 0.20/0.44    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f51,plain,(
% 0.20/0.44    ~spl5_1 | ~spl5_2),
% 0.20/0.44    inference(avatar_split_clause,[],[f21,f49,f46])).
% 0.20/0.44  fof(f21,plain,(
% 0.20/0.44    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v5_pre_topc(sK2,sK0,sK1)),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  % SZS output end Proof for theBenchmark
% 0.20/0.44  % (23949)------------------------------
% 0.20/0.44  % (23949)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.44  % (23949)Termination reason: Refutation
% 0.20/0.44  
% 0.20/0.44  % (23949)Memory used [KB]: 10874
% 0.20/0.44  % (23949)Time elapsed: 0.017 s
% 0.20/0.44  % (23949)------------------------------
% 0.20/0.44  % (23949)------------------------------
% 0.20/0.44  % (23935)Success in time 0.079 s
%------------------------------------------------------------------------------
