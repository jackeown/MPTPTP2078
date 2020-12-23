%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 922 expanded)
%              Number of leaves         :    5 ( 167 expanded)
%              Depth                    :   42
%              Number of atoms          : 1031 (8375 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f154,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f102,f153])).

fof(f153,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f151,f111])).

fof(f111,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1 ),
    inference(subsumption_resolution,[],[f12,f34])).

fof(f34,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl9_1
  <=> v5_pre_topc(sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f12,plain,
    ( ~ r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X1,X0)
              <~> ! [X3] :
                    ( r1_tmap_1(X1,X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                  & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                  & v1_funct_1(X2) )
               => ( v5_pre_topc(X2,X1,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X1,X0)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => r1_tmap_1(X1,X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).

fof(f151,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f150,f17])).

fof(f17,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f150,plain,
    ( v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f149,f139])).

fof(f139,plain,
    ( m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,
    ( m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f137,f17])).

fof(f137,plain,
    ( v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f136,f39])).

fof(f39,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl9_2
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f136,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f135,f16])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f6])).

fof(f135,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f134,f15])).

fof(f15,plain,(
    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f134,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f133,f14])).

fof(f14,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f133,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f132,f22])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f131,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f131,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f130,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f130,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f129,f19])).

fof(f19,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f129,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f117,f18])).

fof(f18,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f117,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f113,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(sK6(X0,X1,X2,X3,X4),X0,X3)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).

fof(f113,plain,
    ( m1_connsp_2(sK7(sK1,sK0,sK2,sK3),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f112,f111])).

fof(f112,plain,
    ( m1_connsp_2(sK7(sK1,sK0,sK2,sK3),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3))
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_2 ),
    inference(resolution,[],[f110,f39])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f109,f17])).

fof(f109,plain,(
    ! [X0] :
      ( v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f108,f15])).

fof(f108,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f107,f14])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f106,f22])).

fof(f106,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f105,f21])).

fof(f105,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f104,f20])).

fof(f104,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f103,f19])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(subsumption_resolution,[],[f63,f18])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
      | v2_struct_0(sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0))
      | r1_tmap_1(sK1,sK0,sK2,X0) ) ),
    inference(resolution,[],[f31,f16])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | r1_tmap_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) )
                        | ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_tmap_1(X0,X1,X2,X3)
                  <=> ! [X4] :
                        ( m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                       => ? [X5] :
                            ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4)
                            & m1_connsp_2(X5,X0,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).

fof(f149,plain,
    ( ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f148,f39])).

fof(f148,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f147,f16])).

fof(f147,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f146,f15])).

fof(f146,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f145,f14])).

fof(f145,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f144,f22])).

fof(f144,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f143,f21])).

fof(f143,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f142,f20])).

fof(f142,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f141,f19])).

fof(f141,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f140,f18])).

fof(f140,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3)
    | v2_struct_0(sK1)
    | r1_tmap_1(sK1,sK0,sK2,sK3)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f128,f28])).

fof(f28,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X5,X0,X3)
      | v2_struct_0(X0)
      | r1_tmap_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f128,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f126,f17])).

fof(f126,plain,
    ( v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f125,f39])).

fof(f125,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f124,f16])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f123,f15])).

fof(f123,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f122,f14])).

fof(f122,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f121,f22])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f120,f21])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f119,f20])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f118,f19])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f115,f18])).

fof(f115,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3))
    | ~ v5_pre_topc(sK2,sK1,sK0)
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(resolution,[],[f113,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X3,X4)),X4)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f102,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f35,plain,
    ( ~ v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f100,plain,
    ( v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f99,f17])).

fof(f99,plain,
    ( v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f98,f76])).

fof(f76,plain,
    ( m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f75,f52])).

fof(f52,plain,
    ( r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(resolution,[],[f51,f41])).

fof(f41,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK1))
        | r1_tmap_1(sK1,sK0,sK2,X3) )
    | spl9_1 ),
    inference(subsumption_resolution,[],[f13,f35])).

fof(f13,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK1))
      | r1_tmap_1(sK1,sK0,sK2,X3)
      | v5_pre_topc(sK2,sK1,sK0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f51,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f50,f35])).

fof(f50,plain,
    ( m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f49,f17])).

fof(f49,plain,
    ( v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f15])).

fof(f48,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f47,f14])).

fof(f47,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f46,f22])).

fof(f46,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f44,f20])).

fof(f44,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f43,f19])).

fof(f43,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f42,f18])).

fof(f42,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(resolution,[],[f27,f16])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f75,plain,
    ( m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f74,f17])).

fof(f74,plain,
    ( v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f73,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f72,f16])).

fof(f72,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f71,f15])).

fof(f71,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f70,f14])).

fof(f70,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f69,f22])).

fof(f69,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f68,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f65,f18])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(resolution,[],[f29,f62])).

fof(f62,plain,
    ( m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f61,f35])).

fof(f61,plain,
    ( m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f60,f17])).

fof(f60,plain,
    ( v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f59,f15])).

fof(f59,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f58,f14])).

fof(f58,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f21])).

fof(f56,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f55,f20])).

fof(f55,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f54,f19])).

fof(f54,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(subsumption_resolution,[],[f53,f18])).

fof(f53,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK1)
    | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2)))
    | v5_pre_topc(sK2,sK1,sK0) ),
    inference(resolution,[],[f26,f16])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X0)
      | m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(sK8(X0,X1,X2,X3,X4),X0,X3)
      | ~ r1_tmap_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f98,plain,
    ( ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f97,f16])).

fof(f97,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f96,f15])).

fof(f96,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f95,f14])).

fof(f95,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f94,f22])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f93,f21])).

fof(f93,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f92,f20])).

fof(f92,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f91,f19])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(subsumption_resolution,[],[f90,f18])).

fof(f90,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2))
    | v2_struct_0(sK1)
    | v5_pre_topc(sK2,sK1,sK0)
    | spl9_1 ),
    inference(resolution,[],[f89,f25])).

fof(f25,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_connsp_2(X5,X0,sK4(X0,X1,X2))
      | v2_struct_0(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f88,f52])).

fof(f88,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f87,f17])).

fof(f87,plain,
    ( v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f86,f51])).

fof(f86,plain,
    ( ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f85,f16])).

fof(f85,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f84,f15])).

fof(f84,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f83,f14])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f82,f22])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f81,f21])).

fof(f81,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f80,f20])).

fof(f80,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f79,f19])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(subsumption_resolution,[],[f78,f18])).

fof(f78,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2))
    | ~ r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2))
    | spl9_1 ),
    inference(resolution,[],[f30,f62])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X4)),X4)
      | ~ r1_tmap_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f40,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f11,f37,f33])).

fof(f11,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ v5_pre_topc(sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (30342)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.21/0.46  % (30354)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.46  % (30354)Refutation not found, incomplete strategy% (30354)------------------------------
% 0.21/0.46  % (30354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (30354)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (30354)Memory used [KB]: 5373
% 0.21/0.46  % (30354)Time elapsed: 0.053 s
% 0.21/0.46  % (30354)------------------------------
% 0.21/0.46  % (30354)------------------------------
% 0.21/0.47  % (30346)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (30346)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f40,f102,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~spl9_1 | ~spl9_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f152])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    $false | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f151,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ~r1_tmap_1(sK1,sK0,sK2,sK3) | ~spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f12,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    v5_pre_topc(sK2,sK1,sK0) | ~spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl9_1 <=> v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ~r1_tmap_1(sK1,sK0,sK2,sK3) | ~v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((v5_pre_topc(X2,X1,X0) <~> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f5])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((v5_pre_topc(X2,X1,X0) <~> ! [X3] : (r1_tmap_1(X1,X0,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f3])).
% 0.21/0.47  fof(f3,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X1,X0) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => r1_tmap_1(X1,X0,X2,X3))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tmap_1)).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f150,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ~v2_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f149,f139])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f138,f34])).
% 0.21/0.47  fof(f138,plain,(
% 0.21/0.47    m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f137,f17])).
% 0.21/0.47  fof(f137,plain,(
% 0.21/0.47    v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f136,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl9_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl9_2 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.47  fof(f136,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f135,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f134,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f134,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f133,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f132,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f129,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    l1_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f117,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    v2_pre_topc(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(resolution,[],[f113,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(sK6(X0,X1,X2,X3,X4),X0,X3) | ~v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) => ? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_borsuk_1)).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    m1_connsp_2(sK7(sK1,sK0,sK2,sK3),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f112,f111])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    m1_connsp_2(sK7(sK1,sK0,sK2,sK3),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK3)) | r1_tmap_1(sK1,sK0,sK2,sK3) | ~spl9_2),
% 0.21/0.47    inference(resolution,[],[f110,f39])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f109,f17])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f108,f15])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f107,f14])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f106,f22])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f105,f21])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f104,f20])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f103,f19])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f63,f18])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | ~m1_subset_1(X0,u1_struct_0(sK1)) | m1_connsp_2(sK7(sK1,sK0,sK2,X0),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,X0)) | r1_tmap_1(sK1,sK0,sK2,X0)) )),
% 0.21/0.47    inference(resolution,[],[f31,f16])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | m1_connsp_2(sK7(X0,X1,X2,X3),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | r1_tmap_1(X0,X1,X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3)) | ~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_tmap_1(X0,X1,X2,X3) <=> ! [X4] : (m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) => ? [X5] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),X4) & m1_connsp_2(X5,X0,X3))))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tmap_1)).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f148,f39])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f147,f16])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f146,f15])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f145,f14])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f144,f22])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f143,f21])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f142,f20])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f141,f19])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f18])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | ~m1_connsp_2(sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3)),sK1,sK3) | v2_struct_0(sK1) | r1_tmap_1(sK1,sK0,sK2,sK3) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(resolution,[],[f128,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X2,X0,X5,X3,X1] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK7(X0,X1,X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_connsp_2(X5,X0,X3) | v2_struct_0(X0) | r1_tmap_1(X0,X1,X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f127,f34])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f126,f17])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f39])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f124,f16])).
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f123,f15])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f122,f14])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f121,f22])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f21])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f20])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f19])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f115,f18])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK3,u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK6(sK1,sK0,sK2,sK3,sK7(sK1,sK0,sK2,sK3))),sK7(sK1,sK0,sK2,sK3)) | ~v5_pre_topc(sK2,sK1,sK0) | (~spl9_1 | ~spl9_2)),
% 0.21/0.47    inference(resolution,[],[f113,f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | v2_struct_0(X0) | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2,X3,X4)),X4) | ~v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    spl9_1),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f101])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    $false | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f100,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ~v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f100,plain,(
% 0.21/0.47    v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f99,f17])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f98,f76])).
% 0.21/0.47  fof(f76,plain,(
% 0.21/0.47    m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f75,f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(resolution,[],[f51,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X3)) ) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f13,f35])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK1)) | r1_tmap_1(sK1,sK0,sK2,X3) | v5_pre_topc(sK2,sK1,sK0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f35])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f17])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f15])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f47,f14])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f46,f22])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f45,f21])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f44,f20])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f43,f19])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f42,f18])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.47    inference(resolution,[],[f27,f16])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f74,f17])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f73,f51])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f72,f16])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.47    inference(subsumption_resolution,[],[f71,f15])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f14])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f69,f22])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f21])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f20])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f19])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f65,f18])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(resolution,[],[f29,f62])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f35])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f60,f17])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f15])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f14])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f22])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f21])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f55,f20])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f19])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f18])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | v2_struct_0(sK1) | m1_connsp_2(sK5(sK1,sK0,sK2),sK0,k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK4(sK1,sK0,sK2))) | v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f26,f16])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X0) | m1_connsp_2(sK5(X0,X1,X2),X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(sK8(X0,X1,X2,X3,X4),X0,X3) | ~r1_tmap_1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f16])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f96,f15])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f95,f14])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f94,f22])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f93,f21])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f92,f20])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f91,f19])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f90,f18])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_connsp_2(sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2)),sK1,sK4(sK1,sK0,sK2)) | v2_struct_0(sK1) | v5_pre_topc(sK2,sK1,sK0) | spl9_1),
% 0.21/0.48    inference(resolution,[],[f89,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X5,X1] : (~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X5),sK5(X0,X1,X2)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_connsp_2(X5,X0,sK4(X0,X1,X2)) | v2_struct_0(X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f8])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f52])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f17])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f86,f51])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f16])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f84,f15])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f83,f14])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f82,f22])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f81,f21])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f80,f20])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f79,f19])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f78,f18])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(sK4(sK1,sK0,sK2),u1_struct_0(sK1)) | v2_struct_0(sK1) | r1_tarski(k7_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),sK2,sK8(sK1,sK0,sK2,sK4(sK1,sK0,sK2),sK5(sK1,sK0,sK2))),sK5(sK1,sK0,sK2)) | ~r1_tmap_1(sK1,sK0,sK2,sK4(sK1,sK0,sK2)) | spl9_1),
% 0.21/0.48    inference(resolution,[],[f30,f62])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X3,X1] : (~m1_connsp_2(X4,X1,k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X0)) | v2_struct_0(X0) | r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK8(X0,X1,X2,X3,X4)),X4) | ~r1_tmap_1(X0,X1,X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~spl9_1 | spl9_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f11,f37,f33])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    m1_subset_1(sK3,u1_struct_0(sK1)) | ~v5_pre_topc(sK2,sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (30346)------------------------------
% 0.21/0.48  % (30346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (30346)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (30346)Memory used [KB]: 5373
% 0.21/0.48  % (30346)Time elapsed: 0.068 s
% 0.21/0.48  % (30346)------------------------------
% 0.21/0.48  % (30346)------------------------------
% 0.21/0.48  % (30339)Success in time 0.123 s
%------------------------------------------------------------------------------
