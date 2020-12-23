%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  195 (8868 expanded)
%              Number of leaves         :   11 (1780 expanded)
%              Depth                    :   37
%              Number of atoms          :  751 (38748 expanded)
%              Number of equality atoms :  168 (2816 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f375,plain,(
    $false ),
    inference(subsumption_resolution,[],[f374,f152])).

fof(f152,plain,(
    ~ v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f129,f151])).

fof(f151,plain,(
    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f150,f109])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f108,f80])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f40,f78])).

fof(f78,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f76,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

% (4224)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f76,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f44,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f44,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f108,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f107,f78])).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f106,f79])).

fof(f79,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f39,f78])).

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f106,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f105,f78])).

fof(f105,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f104,f45])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f104,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f103,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f84,f44])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(f41,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f149,f127])).

fof(f127,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f102,f125])).

fof(f125,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f77,f59])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f45,f64])).

fof(f102,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f101,f78])).

fof(f101,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f100,f80])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f99,f78])).

% (4226)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f99,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f98,f79])).

fof(f98,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f97,f78])).

fof(f97,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f96,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f95,f38])).

fof(f95,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f149,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f148,f130])).

fof(f130,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f80,f125])).

fof(f148,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f38])).

fof(f135,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f131,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f131,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f79,f125])).

fof(f129,plain,(
    ~ v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f81,f125])).

fof(f81,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f42,f78])).

fof(f42,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f374,plain,(
    v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f373,f153])).

fof(f153,plain,(
    v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f126,f151])).

fof(f126,plain,(
    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f124,f125])).

fof(f124,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f123,f78])).

fof(f123,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f80])).

fof(f122,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f121,f78])).

fof(f121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f79])).

fof(f120,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(forward_demodulation,[],[f119,f78])).

fof(f119,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f118,f45])).

fof(f118,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f86,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f373,plain,
    ( ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f372,f240])).

fof(f240,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f159,f163])).

fof(f163,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f130,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f159,plain,
    ( ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f156,f38])).

fof(f156,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f109,f63])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f372,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f371,f323])).

fof(f323,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f322,f172])).

fof(f172,plain,(
    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f151,f165])).

fof(f165,plain,(
    k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f128,f162])).

fof(f162,plain,(
    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f130,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f128,plain,(
    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f94,f125])).

fof(f94,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f93,f78])).

fof(f93,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f92,f80])).

fof(f92,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f91,f78])).

fof(f91,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f90,f79])).

fof(f90,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(forward_demodulation,[],[f89,f78])).

fof(f89,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f88,f45])).

fof(f88,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f82,f44])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f322,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f321,f109])).

fof(f321,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f320,f167])).

fof(f167,plain,(
    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f127,f165])).

fof(f320,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f319,f168])).

fof(f168,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f130,f165])).

fof(f319,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f318,f38])).

fof(f318,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f256,f169])).

fof(f169,plain,(
    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f131,f165])).

fof(f256,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f254,f77])).

fof(f254,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f194,f166])).

fof(f166,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f125,f165])).

fof(f194,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1))
      | ~ v1_funct_1(X4)
      | ~ l1_struct_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4)
      | ~ v2_funct_1(X4)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4)) ) ),
    inference(subsumption_resolution,[],[f193,f76])).

fof(f193,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X4)
      | ~ l1_struct_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4)
      | ~ v2_funct_1(X4)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4)) ) ),
    inference(subsumption_resolution,[],[f187,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f187,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X4)
      | ~ l1_struct_0(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4)
      | ~ v2_funct_1(X4)
      | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4)) ) ),
    inference(superposition,[],[f47,f78])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f371,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f370,f171])).

fof(f171,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) ),
    inference(backward_demodulation,[],[f147,f165])).

fof(f147,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f146,f127])).

fof(f146,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f145,f109])).

fof(f145,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f144,f130])).

fof(f144,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(resolution,[],[f131,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f370,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f369,f170])).

fof(f170,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f143,f165])).

fof(f143,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f142,f127])).

fof(f142,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f141,f109])).

fof(f141,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f140,f130])).

fof(f140,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f133,f38])).

fof(f133,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(resolution,[],[f131,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f369,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f368,f139])).

fof(f139,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f138,f127])).

fof(f138,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f137,f109])).

fof(f137,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f136,f130])).

fof(f136,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f132,f38])).

fof(f132,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f131,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f368,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f367,f335])).

fof(f335,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f334,f172])).

fof(f334,plain,(
    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f333,f109])).

fof(f333,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f332,f167])).

% (4235)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
fof(f332,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f331,f168])).

fof(f331,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f330,f38])).

fof(f330,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f261,f169])).

fof(f261,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1))
      | k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1) ) ),
    inference(forward_demodulation,[],[f260,f165])).

fof(f260,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1)) ) ),
    inference(subsumption_resolution,[],[f258,f77])).

fof(f258,plain,(
    ! [X1] :
      ( ~ v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1))
      | ~ v1_funct_1(X1)
      | ~ l1_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1)
      | ~ v2_funct_1(X1)
      | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1)) ) ),
    inference(superposition,[],[f197,f166])).

fof(f197,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1))
      | ~ v1_funct_1(X8)
      | ~ l1_struct_0(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8)
      | ~ v2_funct_1(X8)
      | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8)) ) ),
    inference(subsumption_resolution,[],[f196,f76])).

fof(f196,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1))
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X8)
      | ~ l1_struct_0(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8)
      | ~ v2_funct_1(X8)
      | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8)) ) ),
    inference(subsumption_resolution,[],[f189,f43])).

fof(f189,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1))
      | v2_struct_0(sK1)
      | ~ l1_struct_0(sK1)
      | ~ v1_funct_1(X8)
      | ~ l1_struct_0(X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1))))
      | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8)
      | ~ v2_funct_1(X8)
      | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8)) ) ),
    inference(superposition,[],[f48,f78])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f367,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f366,f116])).

fof(f116,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f80])).

fof(f115,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f114,f78])).

fof(f114,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f79])).

fof(f113,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f112,f78])).

fof(f112,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f110,f38])).

fof(f110,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f85,f44])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f41,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f366,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(superposition,[],[f360,f337])).

fof(f337,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f336])).

% (4231)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f336,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f303,f335])).

fof(f303,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f232,f299])).

fof(f299,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f160,f163])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f157,f38])).

fof(f157,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f109,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).

fof(f232,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(global_subsumption,[],[f159,f163,f231])).

fof(f231,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f230,f171])).

fof(f230,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f220,f139])).

fof(f220,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    inference(resolution,[],[f170,f46])).

fof(f360,plain,(
    ! [X1] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1)
      | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | ~ v2_funct_1(X1)
      | ~ v5_pre_topc(X1,sK1,sK0)
      | v3_tops_2(X1,sK1,sK0) ) ),
    inference(forward_demodulation,[],[f359,f165])).

fof(f359,plain,(
    ! [X1] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | ~ v2_funct_1(X1)
      | ~ v5_pre_topc(X1,sK1,sK0)
      | v3_tops_2(X1,sK1,sK0) ) ),
    inference(subsumption_resolution,[],[f358,f45])).

fof(f358,plain,(
    ! [X1] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1)
      | ~ v2_funct_1(X1)
      | ~ v5_pre_topc(X1,sK1,sK0)
      | v3_tops_2(X1,sK1,sK0) ) ),
    inference(superposition,[],[f192,f166])).

fof(f192,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X2),X3),X2,sK1)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X2))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3)
      | k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3)
      | ~ v2_funct_1(X3)
      | ~ v5_pre_topc(X3,sK1,X2)
      | v3_tops_2(X3,sK1,X2) ) ),
    inference(subsumption_resolution,[],[f186,f44])).

fof(f186,plain,(
    ! [X2,X3] :
      ( ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X2),X3),X2,sK1)
      | ~ l1_pre_topc(X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,k2_struct_0(sK1),u1_struct_0(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X2))))
      | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3)
      | k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3)
      | ~ v2_funct_1(X3)
      | ~ v5_pre_topc(X3,sK1,X2)
      | ~ l1_pre_topc(sK1)
      | v3_tops_2(X3,sK1,X2) ) ),
    inference(superposition,[],[f54,f78])).

fof(f54,plain,(
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
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:35:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (4225)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (4230)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (4214)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (4213)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (4217)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (4234)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (4216)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (4232)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (4211)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (4215)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (4222)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (4228)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (4210)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.52  % (4223)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (4218)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (4219)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.52  % (4215)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % (4233)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (4221)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (4216)Refutation not found, incomplete strategy% (4216)------------------------------
% 0.21/0.52  % (4216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4216)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4216)Memory used [KB]: 10618
% 0.21/0.52  % (4216)Time elapsed: 0.104 s
% 0.21/0.52  % (4216)------------------------------
% 0.21/0.52  % (4216)------------------------------
% 0.21/0.53  % (4223)Refutation not found, incomplete strategy% (4223)------------------------------
% 0.21/0.53  % (4223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (4223)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (4223)Memory used [KB]: 6396
% 0.21/0.53  % (4223)Time elapsed: 0.106 s
% 0.21/0.53  % (4223)------------------------------
% 0.21/0.53  % (4223)------------------------------
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f374,f152])).
% 0.21/0.53  fof(f152,plain,(
% 0.21/0.53    ~v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f129,f151])).
% 0.21/0.53  fof(f151,plain,(
% 0.21/0.53    k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f150,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    v2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f108,f80])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f40,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f76,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.53  % (4224)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    l1_struct_0(sK1)),
% 0.21/0.53    inference(resolution,[],[f44,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f11])).
% 0.21/0.53  fof(f11,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    l1_pre_topc(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,negated_conjecture,(
% 0.21/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f15])).
% 0.21/0.53  fof(f15,conjecture,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f107,f78])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f106,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f39,f78])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f105,f78])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f104,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f103,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    v1_funct_1(sK2)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f44])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f41,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_funct_1(X2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f150,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f149,f127])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f102,f125])).
% 0.21/0.53  fof(f125,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f77,f59])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(resolution,[],[f45,f64])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f101,f78])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f80])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f99,f78])).
% 0.21/0.53  % (4226)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f98,f79])).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f97,f78])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f45])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f95,f38])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f83,f44])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f41,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f148,f130])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f80,f125])).
% 0.21/0.53  fof(f148,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f135,f38])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f131,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f79,f125])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    ~v3_tops_2(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f81,f125])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f42,f78])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f374,plain,(
% 0.21/0.53    v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f373,f153])).
% 0.21/0.53  fof(f153,plain,(
% 0.21/0.53    v5_pre_topc(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f126,f151])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    v5_pre_topc(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(backward_demodulation,[],[f124,f125])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f123,f78])).
% 0.21/0.53  fof(f123,plain,(
% 0.21/0.53    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f122,f80])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f121,f78])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f120,f79])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(forward_demodulation,[],[f119,f78])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f118,f45])).
% 0.21/0.53  fof(f118,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f117,f38])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f86,f44])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f41,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f372,f240])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f159,f163])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    v1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f130,f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f156,f38])).
% 0.21/0.53  fof(f156,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f109,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(flattening,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.53  fof(f372,plain,(
% 0.21/0.53    ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f371,f323])).
% 0.21/0.53  fof(f323,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f322,f172])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f151,f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f128,f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.21/0.53    inference(resolution,[],[f130,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f94,f125])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f93,f78])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f92,f80])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f91,f78])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f90,f79])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(forward_demodulation,[],[f89,f78])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f88,f45])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f87,f38])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f82,f44])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~l1_pre_topc(sK0)),
% 0.21/0.53    inference(resolution,[],[f41,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f321,f109])).
% 0.21/0.53  fof(f321,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f320,f167])).
% 0.21/0.53  fof(f167,plain,(
% 0.21/0.53    k2_struct_0(sK1) = k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f127,f165])).
% 0.21/0.53  fof(f320,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f319,f168])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.21/0.53    inference(backward_demodulation,[],[f130,f165])).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f318,f38])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(resolution,[],[f256,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))),
% 0.21/0.53    inference(backward_demodulation,[],[f131,f165])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f254,f77])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1))) )),
% 0.21/0.53    inference(superposition,[],[f194,f166])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.53    inference(backward_demodulation,[],[f125,f165])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1)) | ~v1_funct_1(X4) | ~l1_struct_0(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4) | ~v2_funct_1(X4) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f193,f76])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(X4) | ~l1_struct_0(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4) | ~v2_funct_1(X4) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4))) )),
% 0.21/0.53    inference(subsumption_resolution,[],[f187,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~v1_funct_2(X4,u1_struct_0(X5),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X4) | ~l1_struct_0(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X5),k2_struct_0(sK1),X4) | ~v2_funct_1(X4) | k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(X5),k2_tops_2(u1_struct_0(X5),k2_struct_0(sK1),X4))) )),
% 0.21/0.53    inference(superposition,[],[f47,f78])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f370,f171])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))),
% 0.21/0.53    inference(backward_demodulation,[],[f147,f165])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f146,f127])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f109])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f144,f130])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.53    inference(subsumption_resolution,[],[f134,f38])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.53    inference(resolution,[],[f131,f57])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f369,f170])).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2))),
% 0.21/0.53    inference(backward_demodulation,[],[f143,f165])).
% 0.21/0.53  fof(f143,plain,(
% 0.21/0.53    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f142,f127])).
% 0.21/0.53  fof(f142,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f141,f109])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f140,f130])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.53    inference(subsumption_resolution,[],[f133,f38])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.53    inference(resolution,[],[f131,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f369,plain,(
% 0.21/0.53    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f368,f139])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f138,f127])).
% 0.21/0.53  fof(f138,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f137,f109])).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f136,f130])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f132,f38])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.53    inference(resolution,[],[f131,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.53    inference(subsumption_resolution,[],[f367,f335])).
% 0.21/0.53  fof(f335,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.53    inference(forward_demodulation,[],[f334,f172])).
% 0.21/0.53  fof(f334,plain,(
% 0.21/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))),
% 0.21/0.53    inference(subsumption_resolution,[],[f333,f109])).
% 1.29/0.53  fof(f333,plain,(
% 1.29/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~v2_funct_1(sK2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f332,f167])).
% 1.29/0.53  % (4235)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.29/0.53  fof(f332,plain,(
% 1.29/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f331,f168])).
% 1.29/0.53  fof(f331,plain,(
% 1.29/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2)),
% 1.29/0.53    inference(subsumption_resolution,[],[f330,f38])).
% 1.29/0.53  fof(f330,plain,(
% 1.29/0.53    k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | ~v2_funct_1(sK2)),
% 1.29/0.53    inference(resolution,[],[f261,f169])).
% 1.29/0.53  fof(f261,plain,(
% 1.29/0.53    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1)) | k1_relat_1(sK2) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1) | ~v2_funct_1(X1)) )),
% 1.29/0.53    inference(forward_demodulation,[],[f260,f165])).
% 1.29/0.53  fof(f260,plain,(
% 1.29/0.53    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1))) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f258,f77])).
% 1.29/0.53  fof(f258,plain,(
% 1.29/0.53    ( ! [X1] : (~v1_funct_2(X1,k1_relat_1(sK2),k2_struct_0(sK1)) | ~v1_funct_1(X1) | ~l1_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),X1) | ~v2_funct_1(X1) | k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),X1))) )),
% 1.29/0.53    inference(superposition,[],[f197,f166])).
% 1.29/0.53  fof(f197,plain,(
% 1.29/0.53    ( ! [X8,X9] : (~v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1)) | ~v1_funct_1(X8) | ~l1_struct_0(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8) | ~v2_funct_1(X8) | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8))) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f196,f76])).
% 1.29/0.53  fof(f196,plain,(
% 1.29/0.53    ( ! [X8,X9] : (~v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1)) | ~l1_struct_0(sK1) | ~v1_funct_1(X8) | ~l1_struct_0(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8) | ~v2_funct_1(X8) | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8))) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f189,f43])).
% 1.29/0.53  fof(f189,plain,(
% 1.29/0.53    ( ! [X8,X9] : (~v1_funct_2(X8,u1_struct_0(X9),k2_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(X8) | ~l1_struct_0(X9) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X9),k2_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(X9),k2_struct_0(sK1),X8) | ~v2_funct_1(X8) | k2_struct_0(X9) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(X9),k2_tops_2(u1_struct_0(X9),k2_struct_0(sK1),X8))) )),
% 1.29/0.53    inference(superposition,[],[f48,f78])).
% 1.29/0.53  fof(f48,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~l1_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f367,plain,(
% 1.29/0.53    k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f366,f116])).
% 1.29/0.53  fof(f116,plain,(
% 1.29/0.53    v5_pre_topc(sK2,sK0,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f115,f80])).
% 1.29/0.53  fof(f115,plain,(
% 1.29/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.29/0.53    inference(forward_demodulation,[],[f114,f78])).
% 1.29/0.53  fof(f114,plain,(
% 1.29/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f113,f79])).
% 1.29/0.53  fof(f113,plain,(
% 1.29/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.29/0.53    inference(forward_demodulation,[],[f112,f78])).
% 1.29/0.53  fof(f112,plain,(
% 1.29/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 1.29/0.53    inference(subsumption_resolution,[],[f111,f45])).
% 1.29/0.53  fof(f111,plain,(
% 1.29/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f110,f38])).
% 1.29/0.53  fof(f110,plain,(
% 1.29/0.53    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.29/0.53    inference(subsumption_resolution,[],[f85,f44])).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.29/0.53    inference(resolution,[],[f41,f52])).
% 1.29/0.53  fof(f52,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f25])).
% 1.29/0.53  fof(f366,plain,(
% 1.29/0.53    ~v5_pre_topc(sK2,sK0,sK1) | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 1.29/0.53    inference(superposition,[],[f360,f337])).
% 1.29/0.53  fof(f337,plain,(
% 1.29/0.53    sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(trivial_inequality_removal,[],[f336])).
% 1.29/0.53  % (4231)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.29/0.53  fof(f336,plain,(
% 1.29/0.53    k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(backward_demodulation,[],[f303,f335])).
% 1.29/0.53  fof(f303,plain,(
% 1.29/0.53    k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(backward_demodulation,[],[f232,f299])).
% 1.29/0.53  fof(f299,plain,(
% 1.29/0.53    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.29/0.53    inference(resolution,[],[f160,f163])).
% 1.29/0.53  fof(f160,plain,(
% 1.29/0.53    ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.29/0.53    inference(subsumption_resolution,[],[f157,f38])).
% 1.29/0.53  fof(f157,plain,(
% 1.29/0.53    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.29/0.53    inference(resolution,[],[f109,f60])).
% 1.29/0.53  fof(f60,plain,(
% 1.29/0.53    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 1.29/0.53    inference(cnf_transformation,[],[f31])).
% 1.29/0.53  fof(f31,plain,(
% 1.29/0.53    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.29/0.53    inference(flattening,[],[f30])).
% 1.29/0.53  fof(f30,plain,(
% 1.29/0.53    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.29/0.53    inference(ennf_transformation,[],[f5])).
% 1.29/0.53  fof(f5,axiom,(
% 1.29/0.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 1.29/0.53  fof(f232,plain,(
% 1.29/0.53    k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(global_subsumption,[],[f159,f163,f231])).
% 1.29/0.53  fof(f231,plain,(
% 1.29/0.53    k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(subsumption_resolution,[],[f230,f171])).
% 1.29/0.53  fof(f230,plain,(
% 1.29/0.53    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(subsumption_resolution,[],[f220,f139])).
% 1.29/0.53  fof(f220,plain,(
% 1.29/0.53    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.29/0.53    inference(resolution,[],[f170,f46])).
% 1.29/0.53  fof(f360,plain,(
% 1.29/0.53    ( ! [X1] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1) | k1_relat_1(sK2) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | ~v2_funct_1(X1) | ~v5_pre_topc(X1,sK1,sK0) | v3_tops_2(X1,sK1,sK0)) )),
% 1.29/0.53    inference(forward_demodulation,[],[f359,f165])).
% 1.29/0.53  fof(f359,plain,(
% 1.29/0.53    ( ! [X1] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | ~v2_funct_1(X1) | ~v5_pre_topc(X1,sK1,sK0) | v3_tops_2(X1,sK1,sK0)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f358,f45])).
% 1.29/0.53  fof(f358,plain,(
% 1.29/0.53    ( ! [X1] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),X1),sK0,sK1) | ~l1_pre_topc(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK1),k1_relat_1(sK2)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),X1) | ~v2_funct_1(X1) | ~v5_pre_topc(X1,sK1,sK0) | v3_tops_2(X1,sK1,sK0)) )),
% 1.29/0.53    inference(superposition,[],[f192,f166])).
% 1.29/0.53  fof(f192,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X2),X3),X2,sK1) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3) | k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3) | ~v2_funct_1(X3) | ~v5_pre_topc(X3,sK1,X2) | v3_tops_2(X3,sK1,X2)) )),
% 1.29/0.53    inference(subsumption_resolution,[],[f186,f44])).
% 1.29/0.53  fof(f186,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),u1_struct_0(X2),X3),X2,sK1) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,k2_struct_0(sK1),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(X2)))) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3) | k2_struct_0(X2) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(X2),X3) | ~v2_funct_1(X3) | ~v5_pre_topc(X3,sK1,X2) | ~l1_pre_topc(sK1) | v3_tops_2(X3,sK1,X2)) )),
% 1.29/0.53    inference(superposition,[],[f54,f78])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    ( ! [X2,X0,X1] : (~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | ~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | v3_tops_2(X2,X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f25])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (4215)------------------------------
% 1.29/0.53  % (4215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (4215)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (4215)Memory used [KB]: 6396
% 1.29/0.53  % (4215)Time elapsed: 0.101 s
% 1.29/0.53  % (4215)------------------------------
% 1.29/0.53  % (4215)------------------------------
% 1.29/0.53  % (4208)Success in time 0.17 s
%------------------------------------------------------------------------------
