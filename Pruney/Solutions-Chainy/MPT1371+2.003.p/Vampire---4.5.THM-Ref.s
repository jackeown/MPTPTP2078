%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 (1529 expanded)
%              Number of leaves         :   14 ( 293 expanded)
%              Depth                    :   27
%              Number of atoms          :  718 (12428 expanded)
%              Number of equality atoms :  131 (1911 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f303,plain,(
    $false ),
    inference(global_subsumption,[],[f154,f294,f302])).

fof(f302,plain,(
    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f301,f161])).

fof(f161,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f143,f156])).

fof(f156,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f104,f148])).

fof(f148,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(X2,X0,X1)
              & v5_pre_topc(X2,X0,X1)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & v8_pre_topc(X1)
              & v1_compts_1(X0)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v5_pre_topc(X2,X0,X1)
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                    & v8_pre_topc(X1)
                    & v1_compts_1(X0) )
                 => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => v3_tops_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).

fof(f104,plain,(
    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f44,f103])).

fof(f103,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f82,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f82,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f53,f78])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f142,f102])).

fof(f102,plain,(
    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f45,f101])).

fof(f101,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f81,f70])).

fof(f81,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f51,f78])).

fof(f51,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f142,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f141,f101])).

fof(f141,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f140,f103])).

fof(f140,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f139,f104])).

fof(f139,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f138,f48])).

fof(f48,plain,(
    ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f138,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f137,f46])).

fof(f46,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f137,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f136,f41])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f53])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f134,f39])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f133,f51])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f110,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f40,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) )
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( v4_pre_topc(X3,X0)
                      <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f301,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(resolution,[],[f294,f165])).

fof(f165,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k9_relat_1(sK2,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2))) ) ),
    inference(backward_demodulation,[],[f153,f156])).

fof(f153,plain,(
    ! [X1] :
      ( v4_pre_topc(k9_relat_1(sK2,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0) ) ),
    inference(backward_demodulation,[],[f100,f147])).

fof(f147,plain,(
    ! [X2] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f41,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f100,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f99,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f99,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f98,f45])).

fof(f98,plain,(
    ! [X1] :
      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f97,f43])).

fof(f43,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f97,plain,(
    ! [X1] :
      ( ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f96,f42])).

fof(f42,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f96,plain,(
    ! [X1] :
      ( ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f95,f41])).

fof(f95,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X1] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f93,f39])).

fof(f93,plain,(
    ! [X1] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f92,f51])).

fof(f92,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f91,f50])).

fof(f50,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f91,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f90,f49])).

fof(f90,plain,(
    ! [X1] :
      ( v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f84,f53])).

fof(f84,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK1)
      | ~ v2_pre_topc(sK1)
      | ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(resolution,[],[f47,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_compts_1(X0)
      | ~ v8_pre_topc(X1)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v5_pre_topc(X2,X0,X1)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ v8_pre_topc(X1)
              | ~ v1_compts_1(X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v5_pre_topc(X2,X0,X1)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & v8_pre_topc(X1)
                  & v1_compts_1(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( v4_pre_topc(X3,X0)
                     => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).

fof(f47,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f294,plain,(
    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f292,f255])).

fof(f255,plain,(
    sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f254,f46])).

fof(f254,plain,
    ( ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f253,f144])).

fof(f144,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f41,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f253,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f252,f39])).

fof(f252,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(resolution,[],[f250,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f250,plain,(
    r1_tarski(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f161,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f292,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f291,f170])).

fof(f170,plain,(
    ! [X1] : m1_subset_1(k9_relat_1(sK2,X1),k1_zfmisc_1(k2_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f152,f167])).

fof(f167,plain,(
    u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(backward_demodulation,[],[f159,f166])).

fof(f166,plain,(
    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f149,f156])).

fof(f149,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f41,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

% (23267)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f159,plain,(
    u1_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f102,f156])).

fof(f152,plain,(
    ! [X1] : m1_subset_1(k9_relat_1(sK2,X1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f146,f147])).

fof(f146,plain,(
    ! [X1] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f41,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f291,plain,
    ( v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0)
    | ~ m1_subset_1(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_relat_1(sK2)))
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f169,f155])).

fof(f155,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f121,f147])).

fof(f121,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f120,f102])).

fof(f120,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f119,f101])).

fof(f119,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f118,f103])).

% (23268)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
fof(f118,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f117,f104])).

fof(f117,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f116,f48])).

fof(f116,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f46])).

fof(f115,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f114,f41])).

fof(f114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f53])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f112,f39])).

fof(f112,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f111,f51])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f108,f49])).

fof(f108,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f40,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1)
      | v4_pre_topc(sK3(X0,X1,X2),X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f169,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK2))) ) ),
    inference(backward_demodulation,[],[f151,f167])).

fof(f151,plain,(
    ! [X0] :
      ( v4_pre_topc(k10_relat_1(sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1) ) ),
    inference(backward_demodulation,[],[f89,f145])).

fof(f145,plain,(
    ! [X0] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(resolution,[],[f41,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f88,f53])).

fof(f88,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f40])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f51])).

fof(f83,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v4_pre_topc(X3,X1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f154,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f132,f147])).

fof(f132,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f131,f102])).

fof(f131,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f130,f101])).

fof(f130,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f129,f103])).

fof(f129,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f128,f104])).

fof(f128,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f127,f48])).

% (23275)Refutation not found, incomplete strategy% (23275)------------------------------
% (23275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23275)Termination reason: Refutation not found, incomplete strategy

% (23275)Memory used [KB]: 1791
% (23275)Time elapsed: 0.097 s
% (23275)------------------------------
% (23275)------------------------------
fof(f127,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f126,f46])).

fof(f126,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f125,f41])).

fof(f125,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f124,f53])).

fof(f124,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f123,f39])).

fof(f123,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f122,f51])).

fof(f122,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f109,f49])).

fof(f109,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1)
      | ~ v4_pre_topc(sK3(X0,X1,X2),X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (23271)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (23265)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.48  % (23269)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.48  % (23279)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.49  % (23265)Refutation not found, incomplete strategy% (23265)------------------------------
% 0.21/0.49  % (23265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23265)Memory used [KB]: 11129
% 0.21/0.49  % (23265)Time elapsed: 0.048 s
% 0.21/0.49  % (23265)------------------------------
% 0.21/0.49  % (23265)------------------------------
% 0.21/0.49  % (23270)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.49  % (23273)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (23262)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (23261)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (23275)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.50  % (23262)Refutation not found, incomplete strategy% (23262)------------------------------
% 0.21/0.50  % (23262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23262)Memory used [KB]: 10618
% 0.21/0.50  % (23262)Time elapsed: 0.085 s
% 0.21/0.50  % (23262)------------------------------
% 0.21/0.50  % (23262)------------------------------
% 0.21/0.50  % (23278)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (23260)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (23279)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(global_subsumption,[],[f154,f294,f302])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f301,f161])).
% 0.21/0.51  fof(f161,plain,(
% 0.21/0.51    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2)))),
% 0.21/0.51    inference(backward_demodulation,[],[f143,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f104,f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f41,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(X2,X0,X1) & (v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f15])).
% 0.21/0.51  fof(f15,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f44,f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f82,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f53,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f142,f102])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f45,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f81,f70])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f51,f78])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    l1_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f142,plain,(
% 0.21/0.51    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(forward_demodulation,[],[f141,f101])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f103])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(forward_demodulation,[],[f139,f104])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ~v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f136,f41])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f53])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f51])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f40,f58])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) | ~m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2)))),
% 0.21/0.51    inference(resolution,[],[f294,f165])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    ( ! [X1] : (~v4_pre_topc(X1,sK0) | v4_pre_topc(k9_relat_1(sK2,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f153,f156])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    ( ! [X1] : (v4_pre_topc(k9_relat_1(sK2,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f100,f147])).
% 0.21/0.51  fof(f147,plain,(
% 0.21/0.51    ( ! [X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k9_relat_1(sK2,X2)) )),
% 0.21/0.51    inference(resolution,[],[f41,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f99,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f98,f45])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X1] : (k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f97,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    v8_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ( ! [X1] : (~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f96,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    v1_compts_1(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f95,f41])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.51  fof(f94,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f93,f39])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    ( ! [X1] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f92,f51])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X1] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f91,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    v2_pre_topc(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ( ! [X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f90,f49])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ( ! [X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f84,f53])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 0.21/0.51    inference(resolution,[],[f47,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_compts_1(X0) | ~v8_pre_topc(X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f293])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f292,f255])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f254,f46])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f253,f144])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    v1_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f41,f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f252,f39])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 0.21/0.51    inference(resolution,[],[f250,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    r1_tarski(sK3(sK0,sK1,sK2),k1_relat_1(sK2))),
% 0.21/0.51    inference(resolution,[],[f161,f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.51    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f291,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k9_relat_1(sK2,X1),k1_zfmisc_1(k2_relat_1(sK2)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f152,f167])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f159,f166])).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f149,f156])).
% 0.21/0.51  fof(f149,plain,(
% 0.21/0.51    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.51    inference(resolution,[],[f41,f68])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  % (23267)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f159,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f102,f156])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k9_relat_1(sK2,X1),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f146,f147])).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    ( ! [X1] : (m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.21/0.51    inference(resolution,[],[f41,f72])).
% 0.21/0.51  fof(f72,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0) | ~m1_subset_1(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(k2_relat_1(sK2))) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(resolution,[],[f169,f155])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f121,f147])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f120,f102])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f119,f101])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f118,f103])).
% 0.21/0.51  % (23268)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f117,f104])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f116,f48])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f115,f46])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f41])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f53])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f112,f39])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f51])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f49])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f40,f56])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1) | v4_pre_topc(sK3(X0,X1,X2),X0) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    ( ! [X0] : (~v4_pre_topc(X0,sK1) | v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_relat_1(sK2)))) )),
% 0.21/0.51    inference(backward_demodulation,[],[f151,f167])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ( ! [X0] : (v4_pre_topc(k10_relat_1(sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f89,f145])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X0] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) )),
% 0.21/0.51    inference(resolution,[],[f41,f73])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f88,f53])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f41])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f86,f40])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f85,f39])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f83,f51])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 0.21/0.51    inference(resolution,[],[f47,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    ~v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f132,f147])).
% 0.21/0.51  fof(f132,plain,(
% 0.21/0.51    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f131,f102])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f130,f101])).
% 0.21/0.51  fof(f130,plain,(
% 0.21/0.51    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f129,f103])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f128,f104])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f48])).
% 0.21/0.51  % (23275)Refutation not found, incomplete strategy% (23275)------------------------------
% 0.21/0.51  % (23275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23275)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (23275)Memory used [KB]: 1791
% 0.21/0.51  % (23275)Time elapsed: 0.097 s
% 0.21/0.51  % (23275)------------------------------
% 0.21/0.51  % (23275)------------------------------
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f46])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f41])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f124,f53])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f123,f39])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f51])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f49])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.51    inference(resolution,[],[f40,f57])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1) | ~v4_pre_topc(sK3(X0,X1,X2),X0) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (23279)------------------------------
% 0.21/0.51  % (23279)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (23279)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (23279)Memory used [KB]: 6524
% 0.21/0.51  % (23279)Time elapsed: 0.082 s
% 0.21/0.51  % (23279)------------------------------
% 0.21/0.51  % (23279)------------------------------
% 0.21/0.51  % (23274)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (23263)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.51  % (23258)Success in time 0.157 s
%------------------------------------------------------------------------------
