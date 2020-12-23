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
% DateTime   : Thu Dec  3 13:14:39 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  180 (6131 expanded)
%              Number of leaves         :   11 (1224 expanded)
%              Depth                    :   32
%              Number of atoms          :  742 (27371 expanded)
%              Number of equality atoms :  159 (1887 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f292,plain,(
    $false ),
    inference(subsumption_resolution,[],[f291,f132])).

fof(f132,plain,(
    ~ v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f109,f131])).

fof(f131,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f130,f89])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f88,f60])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f32,f58])).

fof(f58,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f56,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f56,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f36,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              & v3_tops_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                 => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f87,f58])).

fof(f87,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f86,f59])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f31,f58])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f86,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f85,f58])).

fof(f85,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f84,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).

fof(f33,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f130,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f129,f107])).

fof(f107,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f82,f105])).

fof(f105,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f57,f49])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f52])).

fof(f82,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f81,f58])).

fof(f81,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f80,f60])).

fof(f80,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f79,f58])).

fof(f79,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f78,f59])).

fof(f78,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f77,f58])).

fof(f77,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f76,f37])).

fof(f76,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f75,f30])).

fof(f75,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f63,f36])).

fof(f63,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f128,f110])).

fof(f110,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f60,f105])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f30])).

fof(f115,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f111,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f111,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f59,f105])).

fof(f109,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f61,f105])).

fof(f61,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f34,f58])).

fof(f34,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f291,plain,(
    v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f290,f133])).

fof(f133,plain,(
    v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f106,f131])).

fof(f106,plain,(
    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f104,f105])).

fof(f104,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f103,f58])).

fof(f103,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f102,f60])).

fof(f102,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f101,f58])).

fof(f101,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f59])).

fof(f100,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f99,f58])).

fof(f99,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f98,f37])).

fof(f98,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f97,f30])).

fof(f97,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f66,f36])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f290,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f289,f235])).

fof(f235,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f234,f131])).

fof(f234,plain,(
    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f233,f89])).

fof(f233,plain,
    ( ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f232,f107])).

fof(f232,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f231,f110])).

fof(f231,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f230,f30])).

fof(f230,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f190,f111])).

% (17797)Refutation not found, incomplete strategy% (17797)------------------------------
% (17797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17797)Termination reason: Refutation not found, incomplete strategy

% (17797)Memory used [KB]: 1791
% (17797)Time elapsed: 0.138 s
% (17797)------------------------------
% (17797)------------------------------
% (17788)Termination reason: Refutation not found, incomplete strategy

% (17788)Memory used [KB]: 6268
% (17788)Time elapsed: 0.083 s
% (17788)------------------------------
% (17788)------------------------------
fof(f190,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f189,f57])).

fof(f189,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f147,f105])).

fof(f147,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X2,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK1),X2)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X3),k2_struct_0(sK1),X2)) ) ),
    inference(subsumption_resolution,[],[f139,f56])).

fof(f139,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X2,u1_struct_0(X3),k2_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK1),X2)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X3),k2_struct_0(sK1),X2)) ) ),
    inference(superposition,[],[f39,f58])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f289,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f288,f252])).

fof(f252,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f251,f131])).

fof(f251,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f250,f89])).

fof(f250,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f249,f107])).

fof(f249,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f248,f110])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f247,f30])).

fof(f247,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f208,f111])).

fof(f208,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f206,f57])).

fof(f206,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f155,f105])).

fof(f155,plain,(
    ! [X14,X15] :
      ( ~ v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1))
      | ~ v1_funct_1(X14)
      | ~ l1_struct_0(X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14)
      | ~ v2_funct_1(X14)
      | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14)) ) ),
    inference(subsumption_resolution,[],[f154,f56])).

fof(f154,plain,(
    ! [X14,X15] :
      ( ~ v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X14)
      | ~ l1_struct_0(X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14)
      | ~ v2_funct_1(X14)
      | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14)) ) ),
    inference(subsumption_resolution,[],[f145,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f145,plain,(
    ! [X14,X15] :
      ( ~ v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X14)
      | ~ l1_struct_0(X15)
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14)
      | ~ v2_funct_1(X14)
      | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14)) ) ),
    inference(superposition,[],[f51,f58])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f288,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f287,f246])).

fof(f246,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f245,f131])).

fof(f245,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f244,f89])).

fof(f244,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f243,f107])).

fof(f243,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f242,f110])).

fof(f242,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f241,f30])).

fof(f241,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f204,f111])).

fof(f204,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f202,f57])).

fof(f202,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f152,f105])).

fof(f152,plain,(
    ! [X10,X11] :
      ( ~ v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1))
      | ~ v1_funct_1(X10)
      | ~ l1_struct_0(X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10)
      | ~ v2_funct_1(X10)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10)) ) ),
    inference(subsumption_resolution,[],[f151,f56])).

fof(f151,plain,(
    ! [X10,X11] :
      ( ~ v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X10)
      | ~ l1_struct_0(X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10)
      | ~ v2_funct_1(X10)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10)) ) ),
    inference(subsumption_resolution,[],[f143,f35])).

fof(f143,plain,(
    ! [X10,X11] :
      ( ~ v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X10)
      | ~ l1_struct_0(X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10)
      | ~ v2_funct_1(X10)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10)) ) ),
    inference(superposition,[],[f50,f58])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f287,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f286,f127])).

fof(f127,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f126,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f125,f89])).

fof(f125,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f124,f110])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f111,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f286,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f285,f123])).

fof(f123,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f122,f107])).

fof(f122,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f121,f89])).

fof(f121,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f120,f110])).

fof(f120,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f113,f30])).

fof(f113,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f285,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f284,f119])).

fof(f119,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f118,f107])).

fof(f118,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f117,f89])).

fof(f117,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f116,f110])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f111,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f284,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f283,f96])).

fof(f96,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f95,f60])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f94,f58])).

fof(f94,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f93,f59])).

fof(f93,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f92,f58])).

fof(f92,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f91,f37])).

fof(f91,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f90,f30])).

fof(f90,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f33,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f283,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(superposition,[],[f279,f260])).

fof(f260,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f253])).

fof(f253,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f237,f252])).

fof(f237,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f235,f192])).

fof(f192,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f187,f191])).

fof(f191,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f135,f137])).

fof(f137,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f54])).

fof(f54,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f136,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f110,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f134,f30])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f89,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f187,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f186,f127])).

fof(f186,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f179,f119])).

fof(f179,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f123,f38])).

fof(f279,plain,(
    ! [X1] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X1),sK0,sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1)
      | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1)
      | ~ v2_funct_1(X1)
      | ~ v5_pre_topc(X1,sK1,sK0)
      | v3_tops_2(X1,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f277,f37])).

fof(f277,plain,(
    ! [X1] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X1),sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK1),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1)
      | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1)
      | ~ v2_funct_1(X1)
      | ~ v5_pre_topc(X1,sK1,sK0)
      | v3_tops_2(X1,sK1,sK0) ) ),
    inference(superposition,[],[f148,f105])).

fof(f148,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X4),X5),X4,sK1)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X4))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5)
      | k2_struct_0(X4) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5)
      | ~ v2_funct_1(X5)
      | ~ v5_pre_topc(X5,sK1,X4)
      | v3_tops_2(X5,sK1,X4) ) ),
    inference(subsumption_resolution,[],[f140,f36])).

fof(f140,plain,(
    ! [X4,X5] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X4),X5),X4,sK1)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k2_struct_0(sK1),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X4))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5)
      | k2_struct_0(X4) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5)
      | ~ v2_funct_1(X5)
      | ~ v5_pre_topc(X5,sK1,X4)
      | ~ l1_pre_topc(sK1)
      | v3_tops_2(X5,sK1,X4) ) ),
    inference(superposition,[],[f45,f58])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:58:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (17790)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (17802)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (17786)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.53  % (17799)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.53  % (17800)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (17804)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.53  % (17784)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.53  % (17803)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (17781)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.53  % (17783)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.53  % (17787)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.53  % (17784)Refutation not found, incomplete strategy% (17784)------------------------------
% 0.22/0.53  % (17784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17784)Memory used [KB]: 10618
% 0.22/0.53  % (17784)Time elapsed: 0.112 s
% 0.22/0.53  % (17784)------------------------------
% 0.22/0.53  % (17784)------------------------------
% 0.22/0.53  % (17796)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.53  % (17785)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.53  % (17789)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.54  % (17789)Refutation not found, incomplete strategy% (17789)------------------------------
% 0.22/0.54  % (17789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17789)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17789)Memory used [KB]: 10618
% 0.22/0.54  % (17789)Time elapsed: 0.111 s
% 0.22/0.54  % (17789)------------------------------
% 0.22/0.54  % (17789)------------------------------
% 0.22/0.54  % (17804)Refutation not found, incomplete strategy% (17804)------------------------------
% 0.22/0.54  % (17804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17804)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17804)Memory used [KB]: 10618
% 0.22/0.54  % (17804)Time elapsed: 0.068 s
% 0.22/0.54  % (17804)------------------------------
% 0.22/0.54  % (17804)------------------------------
% 0.22/0.54  % (17792)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.54  % (17788)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (17782)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.54  % (17795)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.55  % (17794)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.55  % (17791)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.55  % (17791)Refutation not found, incomplete strategy% (17791)------------------------------
% 0.22/0.55  % (17791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17791)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17791)Memory used [KB]: 10490
% 0.22/0.55  % (17791)Time elapsed: 0.124 s
% 0.22/0.55  % (17791)------------------------------
% 0.22/0.55  % (17791)------------------------------
% 0.22/0.55  % (17793)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.55  % (17788)Refutation not found, incomplete strategy% (17788)------------------------------
% 0.22/0.55  % (17788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17801)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.56  % (17797)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.56  % (17801)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f291,f132])).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    ~v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f109,f131])).
% 0.22/0.56  fof(f131,plain,(
% 0.22/0.56    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f130,f89])).
% 0.22/0.56  fof(f89,plain,(
% 0.22/0.56    v2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f88,f60])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f32,f58])).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f56,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    l1_struct_0(sK1)),
% 0.22/0.56    inference(resolution,[],[f36,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    l1_pre_topc(sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f13])).
% 0.22/0.56  fof(f13,plain,(
% 0.22/0.56    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,negated_conjecture,(
% 0.22/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.56    inference(negated_conjecture,[],[f11])).
% 0.22/0.56  fof(f11,conjecture,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f88,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f87,f58])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f86,f59])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f31,f58])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f86,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f85,f58])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f84,f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    l1_pre_topc(sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f84,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f83,f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f83,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f64,f36])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f33,f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_funct_1(X2) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(flattening,[],[f19])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    v3_tops_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f129,f107])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f82,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f57,f49])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    l1_struct_0(sK0)),
% 0.22/0.56    inference(resolution,[],[f37,f52])).
% 0.22/0.56  fof(f82,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f81,f58])).
% 0.22/0.56  fof(f81,plain,(
% 0.22/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f80,f60])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f79,f58])).
% 0.22/0.56  fof(f79,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f78,f59])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f77,f58])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f76,f37])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f75,f30])).
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f63,f36])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f33,f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f129,plain,(
% 0.22/0.56    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f128,f110])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.22/0.56    inference(backward_demodulation,[],[f60,f105])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f115,f30])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f111,f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f15])).
% 0.22/0.56  fof(f15,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.22/0.56  fof(f111,plain,(
% 0.22/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.22/0.56    inference(backward_demodulation,[],[f59,f105])).
% 0.22/0.56  fof(f109,plain,(
% 0.22/0.56    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f61,f105])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f34,f58])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f14])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f290,f133])).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    v5_pre_topc(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f106,f131])).
% 0.22/0.56  fof(f106,plain,(
% 0.22/0.56    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f104,f105])).
% 0.22/0.56  fof(f104,plain,(
% 0.22/0.56    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f103,f58])).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f102,f60])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f101,f58])).
% 0.22/0.56  fof(f101,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f100,f59])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(forward_demodulation,[],[f99,f58])).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f98,f37])).
% 0.22/0.56  fof(f98,plain,(
% 0.22/0.56    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f97,f30])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f66,f36])).
% 0.22/0.56  fof(f66,plain,(
% 0.22/0.56    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.22/0.56    inference(resolution,[],[f33,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f20])).
% 0.22/0.56  fof(f290,plain,(
% 0.22/0.56    ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.22/0.56    inference(subsumption_resolution,[],[f289,f235])).
% 0.22/0.56  fof(f235,plain,(
% 0.22/0.56    v2_funct_1(k2_funct_1(sK2))),
% 0.22/0.56    inference(forward_demodulation,[],[f234,f131])).
% 0.22/0.56  fof(f234,plain,(
% 0.22/0.56    v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f233,f89])).
% 0.22/0.56  fof(f233,plain,(
% 0.22/0.56    ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f232,f107])).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f231,f110])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(subsumption_resolution,[],[f230,f30])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.22/0.56    inference(resolution,[],[f190,f111])).
% 0.22/0.56  % (17797)Refutation not found, incomplete strategy% (17797)------------------------------
% 0.22/0.56  % (17797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (17797)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17797)Memory used [KB]: 1791
% 0.22/0.56  % (17797)Time elapsed: 0.138 s
% 0.22/0.56  % (17797)------------------------------
% 0.22/0.56  % (17797)------------------------------
% 0.22/0.56  % (17788)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (17788)Memory used [KB]: 6268
% 0.22/0.56  % (17788)Time elapsed: 0.083 s
% 0.22/0.56  % (17788)------------------------------
% 0.22/0.56  % (17788)------------------------------
% 1.69/0.58  fof(f190,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f189,f57])).
% 1.69/0.58  fof(f189,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(superposition,[],[f147,f105])).
% 1.69/0.58  fof(f147,plain,(
% 1.69/0.58    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(X3),k2_struct_0(sK1)) | ~v1_funct_1(X2) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK1),X2) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X3),k2_struct_0(sK1),X2))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f139,f56])).
% 1.69/0.58  fof(f139,plain,(
% 1.69/0.58    ( ! [X2,X3] : (~v1_funct_2(X2,u1_struct_0(X3),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(X2) | ~l1_struct_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X3),k2_struct_0(sK1),X2) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X3),k2_struct_0(sK1),X2))) )),
% 1.69/0.58    inference(superposition,[],[f39,f58])).
% 1.69/0.58  fof(f39,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f18])).
% 1.69/0.58  fof(f18,plain,(
% 1.69/0.58    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.69/0.58    inference(flattening,[],[f17])).
% 1.69/0.58  fof(f17,plain,(
% 1.69/0.58    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f10])).
% 1.69/0.58  fof(f10,axiom,(
% 1.69/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 1.69/0.58  fof(f289,plain,(
% 1.69/0.58    ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f288,f252])).
% 1.69/0.58  fof(f252,plain,(
% 1.69/0.58    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(forward_demodulation,[],[f251,f131])).
% 1.69/0.58  fof(f251,plain,(
% 1.69/0.58    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f250,f89])).
% 1.69/0.58  fof(f250,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f249,f107])).
% 1.69/0.58  fof(f249,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f248,f110])).
% 1.69/0.58  fof(f248,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f247,f30])).
% 1.69/0.58  fof(f247,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(resolution,[],[f208,f111])).
% 1.69/0.58  fof(f208,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f206,f57])).
% 1.69/0.58  fof(f206,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(superposition,[],[f155,f105])).
% 1.69/0.58  fof(f155,plain,(
% 1.69/0.58    ( ! [X14,X15] : (~v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1)) | ~v1_funct_1(X14) | ~l1_struct_0(X15) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14) | ~v2_funct_1(X14) | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f154,f56])).
% 1.69/0.58  fof(f154,plain,(
% 1.69/0.58    ( ! [X14,X15] : (~v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(X14) | ~l1_struct_0(X15) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14) | ~v2_funct_1(X14) | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f145,f35])).
% 1.69/0.58  fof(f35,plain,(
% 1.69/0.58    ~v2_struct_0(sK1)),
% 1.69/0.58    inference(cnf_transformation,[],[f14])).
% 1.69/0.58  fof(f145,plain,(
% 1.69/0.58    ( ! [X14,X15] : (~v1_funct_2(X14,u1_struct_0(X15),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X14) | ~l1_struct_0(X15) | ~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X15),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X15),k2_struct_0(sK1),X14) | ~v2_funct_1(X14) | k2_struct_0(X15) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X15),k2_tops_2(u1_struct_0(X15),k2_struct_0(sK1),X14))) )),
% 1.69/0.58    inference(superposition,[],[f51,f58])).
% 1.69/0.58  fof(f51,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f25])).
% 1.69/0.58  fof(f25,plain,(
% 1.69/0.58    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.69/0.58    inference(flattening,[],[f24])).
% 1.69/0.58  fof(f24,plain,(
% 1.69/0.58    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f9])).
% 1.69/0.58  fof(f9,axiom,(
% 1.69/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 1.69/0.58  fof(f288,plain,(
% 1.69/0.58    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f287,f246])).
% 1.69/0.58  fof(f246,plain,(
% 1.69/0.58    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(forward_demodulation,[],[f245,f131])).
% 1.69/0.58  fof(f245,plain,(
% 1.69/0.58    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f244,f89])).
% 1.69/0.58  fof(f244,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f243,f107])).
% 1.69/0.58  fof(f243,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f242,f110])).
% 1.69/0.58  fof(f242,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f241,f30])).
% 1.69/0.58  fof(f241,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 1.69/0.58    inference(resolution,[],[f204,f111])).
% 1.69/0.58  fof(f204,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f202,f57])).
% 1.69/0.58  fof(f202,plain,(
% 1.69/0.58    ( ! [X1] : (~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X1))) )),
% 1.69/0.58    inference(superposition,[],[f152,f105])).
% 1.69/0.58  fof(f152,plain,(
% 1.69/0.58    ( ! [X10,X11] : (~v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1)) | ~v1_funct_1(X10) | ~l1_struct_0(X11) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10) | ~v2_funct_1(X10) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f151,f56])).
% 1.69/0.58  fof(f151,plain,(
% 1.69/0.58    ( ! [X10,X11] : (~v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(X10) | ~l1_struct_0(X11) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10) | ~v2_funct_1(X10) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10))) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f143,f35])).
% 1.69/0.58  fof(f143,plain,(
% 1.69/0.58    ( ! [X10,X11] : (~v1_funct_2(X10,u1_struct_0(X11),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X10) | ~l1_struct_0(X11) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X11),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X11),k2_struct_0(sK1),X10) | ~v2_funct_1(X10) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X11),k2_tops_2(u1_struct_0(X11),k2_struct_0(sK1),X10))) )),
% 1.69/0.58    inference(superposition,[],[f50,f58])).
% 1.69/0.58  fof(f50,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f25])).
% 1.69/0.58  fof(f287,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f286,f127])).
% 1.69/0.58  fof(f127,plain,(
% 1.69/0.58    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f126,f107])).
% 1.69/0.58  fof(f126,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f125,f89])).
% 1.69/0.58  fof(f125,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f124,f110])).
% 1.69/0.58  fof(f124,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.69/0.58    inference(subsumption_resolution,[],[f114,f30])).
% 1.69/0.58  fof(f114,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 1.69/0.58    inference(resolution,[],[f111,f48])).
% 1.69/0.58  fof(f48,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f22,plain,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.69/0.58    inference(flattening,[],[f21])).
% 1.69/0.58  fof(f21,plain,(
% 1.69/0.58    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.69/0.58    inference(ennf_transformation,[],[f4])).
% 1.69/0.58  fof(f4,axiom,(
% 1.69/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.69/0.58  fof(f286,plain,(
% 1.69/0.58    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f285,f123])).
% 1.69/0.58  fof(f123,plain,(
% 1.69/0.58    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.69/0.58    inference(subsumption_resolution,[],[f122,f107])).
% 1.69/0.58  fof(f122,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.69/0.58    inference(subsumption_resolution,[],[f121,f89])).
% 1.69/0.58  fof(f121,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.69/0.58    inference(subsumption_resolution,[],[f120,f110])).
% 1.69/0.58  fof(f120,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.69/0.58    inference(subsumption_resolution,[],[f113,f30])).
% 1.69/0.58  fof(f113,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 1.69/0.58    inference(resolution,[],[f111,f47])).
% 1.69/0.58  fof(f47,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f285,plain,(
% 1.69/0.58    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f284,f119])).
% 1.69/0.58  fof(f119,plain,(
% 1.69/0.58    v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f118,f107])).
% 1.69/0.58  fof(f118,plain,(
% 1.69/0.58    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f117,f89])).
% 1.69/0.58  fof(f117,plain,(
% 1.69/0.58    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f116,f110])).
% 1.69/0.58  fof(f116,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f112,f30])).
% 1.69/0.58  fof(f112,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f111,f46])).
% 1.69/0.58  fof(f46,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f22])).
% 1.69/0.58  fof(f284,plain,(
% 1.69/0.58    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f283,f96])).
% 1.69/0.58  fof(f96,plain,(
% 1.69/0.58    v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f95,f60])).
% 1.69/0.58  fof(f95,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.58    inference(forward_demodulation,[],[f94,f58])).
% 1.69/0.58  fof(f94,plain,(
% 1.69/0.58    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f93,f59])).
% 1.69/0.58  fof(f93,plain,(
% 1.69/0.58    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.58    inference(forward_demodulation,[],[f92,f58])).
% 1.69/0.58  fof(f92,plain,(
% 1.69/0.58    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.69/0.58    inference(subsumption_resolution,[],[f91,f37])).
% 1.69/0.58  fof(f91,plain,(
% 1.69/0.58    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f90,f30])).
% 1.69/0.58  fof(f90,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.58    inference(subsumption_resolution,[],[f65,f36])).
% 1.69/0.58  fof(f65,plain,(
% 1.69/0.58    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.69/0.58    inference(resolution,[],[f33,f43])).
% 1.69/0.58  fof(f43,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f20])).
% 1.69/0.58  fof(f283,plain,(
% 1.69/0.58    ~v5_pre_topc(sK2,sK0,sK1) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.69/0.58    inference(superposition,[],[f279,f260])).
% 1.69/0.58  fof(f260,plain,(
% 1.69/0.58    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(trivial_inequality_removal,[],[f253])).
% 1.69/0.58  fof(f253,plain,(
% 1.69/0.58    k2_struct_0(sK0) != k2_struct_0(sK0) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(backward_demodulation,[],[f237,f252])).
% 1.69/0.58  fof(f237,plain,(
% 1.69/0.58    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f235,f192])).
% 1.69/0.58  fof(f192,plain,(
% 1.69/0.58    ~v2_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(backward_demodulation,[],[f187,f191])).
% 1.69/0.58  fof(f191,plain,(
% 1.69/0.58    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f135,f137])).
% 1.69/0.58  fof(f137,plain,(
% 1.69/0.58    v1_relat_1(sK2)),
% 1.69/0.58    inference(subsumption_resolution,[],[f136,f54])).
% 1.69/0.58  fof(f54,plain,(
% 1.69/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.69/0.58    inference(cnf_transformation,[],[f2])).
% 1.69/0.58  fof(f2,axiom,(
% 1.69/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.69/0.58  fof(f136,plain,(
% 1.69/0.58    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | v1_relat_1(sK2)),
% 1.69/0.58    inference(resolution,[],[f110,f55])).
% 1.69/0.58  fof(f55,plain,(
% 1.69/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f29])).
% 1.69/0.58  fof(f29,plain,(
% 1.69/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(ennf_transformation,[],[f1])).
% 1.69/0.58  fof(f1,axiom,(
% 1.69/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.69/0.58  fof(f135,plain,(
% 1.69/0.58    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f134,f30])).
% 1.69/0.58  fof(f134,plain,(
% 1.69/0.58    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f89,f53])).
% 1.69/0.58  fof(f53,plain,(
% 1.69/0.58    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.69/0.58    inference(cnf_transformation,[],[f28])).
% 1.69/0.58  fof(f28,plain,(
% 1.69/0.58    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.69/0.58    inference(flattening,[],[f27])).
% 1.69/0.58  fof(f27,plain,(
% 1.69/0.58    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.69/0.58    inference(ennf_transformation,[],[f3])).
% 1.69/0.58  fof(f3,axiom,(
% 1.69/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.69/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.69/0.58  fof(f187,plain,(
% 1.69/0.58    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f186,f127])).
% 1.69/0.58  fof(f186,plain,(
% 1.69/0.58    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(subsumption_resolution,[],[f179,f119])).
% 1.69/0.58  fof(f179,plain,(
% 1.69/0.58    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 1.69/0.58    inference(resolution,[],[f123,f38])).
% 1.69/0.58  fof(f279,plain,(
% 1.69/0.58    ( ! [X1] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X1),sK0,sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1) | ~v2_funct_1(X1) | ~v5_pre_topc(X1,sK1,sK0) | v3_tops_2(X1,sK1,sK0)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f277,f37])).
% 1.69/0.58  fof(f277,plain,(
% 1.69/0.58    ( ! [X1] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),X1),sK0,sK1) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),X1) | ~v2_funct_1(X1) | ~v5_pre_topc(X1,sK1,sK0) | v3_tops_2(X1,sK1,sK0)) )),
% 1.69/0.58    inference(superposition,[],[f148,f105])).
% 1.69/0.58  fof(f148,plain,(
% 1.69/0.58    ( ! [X4,X5] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X4),X5),X4,sK1) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k2_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X4)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5) | k2_struct_0(X4) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5) | ~v2_funct_1(X5) | ~v5_pre_topc(X5,sK1,X4) | v3_tops_2(X5,sK1,X4)) )),
% 1.69/0.58    inference(subsumption_resolution,[],[f140,f36])).
% 1.69/0.58  fof(f140,plain,(
% 1.69/0.58    ( ! [X4,X5] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X4),X5),X4,sK1) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k2_struct_0(sK1),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X4)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5) | k2_struct_0(X4) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X4),X5) | ~v2_funct_1(X5) | ~v5_pre_topc(X5,sK1,X4) | ~l1_pre_topc(sK1) | v3_tops_2(X5,sK1,X4)) )),
% 1.69/0.58    inference(superposition,[],[f45,f58])).
% 1.69/0.58  fof(f45,plain,(
% 1.69/0.58    ( ! [X2,X0,X1] : (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | ~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | v3_tops_2(X2,X0,X1)) )),
% 1.69/0.58    inference(cnf_transformation,[],[f20])).
% 1.69/0.58  % SZS output end Proof for theBenchmark
% 1.69/0.58  % (17801)------------------------------
% 1.69/0.58  % (17801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.58  % (17801)Termination reason: Refutation
% 1.69/0.58  
% 1.69/0.58  % (17801)Memory used [KB]: 6396
% 1.69/0.58  % (17801)Time elapsed: 0.145 s
% 1.69/0.58  % (17801)------------------------------
% 1.69/0.58  % (17801)------------------------------
% 1.69/0.58  % (17780)Success in time 0.222 s
%------------------------------------------------------------------------------
