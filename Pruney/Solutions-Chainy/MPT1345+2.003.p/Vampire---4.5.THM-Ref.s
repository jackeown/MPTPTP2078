%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  166 (2681 expanded)
%              Number of leaves         :   10 ( 493 expanded)
%              Depth                    :   37
%              Number of atoms          :  603 (14679 expanded)
%              Number of equality atoms :  135 ( 873 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f525,plain,(
    $false ),
    inference(subsumption_resolution,[],[f523,f124])).

fof(f124,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f123,f31])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f122,f30])).

fof(f30,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f121,f29])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f120,f35])).

fof(f35,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f103,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f103,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(resolution,[],[f32,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

% (28134)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f32,plain,(
    v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f523,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(backward_demodulation,[],[f450,f519])).

fof(f519,plain,(
    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f518,f389])).

fof(f389,plain,(
    sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f388,f29])).

fof(f388,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f380,f178])).

fof(f178,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f31,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f380,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f119,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f119,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f31])).

fof(f118,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f117,f30])).

fof(f117,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f116,f29])).

fof(f116,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v2_funct_1(X2)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f518,plain,(
    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f517,f393])).

fof(f393,plain,(
    v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f392,f29])).

fof(f392,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f383,f178])).

fof(f383,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f119,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f517,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f516,f331])).

fof(f331,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f283,f308])).

fof(f308,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f99,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f36,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f283,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f236,f279])).

fof(f279,plain,(
    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f240,f210])).

fof(f210,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f35,f55])).

fof(f240,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(backward_demodulation,[],[f167,f210])).

fof(f167,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(forward_demodulation,[],[f166,f114])).

fof(f114,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f113,f31])).

fof(f113,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f112,f30])).

fof(f112,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f111,f29])).

fof(f111,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subsumption_resolution,[],[f101,f36])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(resolution,[],[f32,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f166,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f165,f119])).

fof(f165,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f164,f31])).

fof(f164,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f141,f29])).

fof(f141,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(resolution,[],[f30,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f236,plain,(
    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f157,f210])).

fof(f157,plain,(
    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f156,f119])).

fof(f156,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f155,f114])).

% (28131)Refutation not found, incomplete strategy% (28131)------------------------------
% (28131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f155,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f154,f31])).

fof(f154,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f153,f29])).

fof(f153,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f152,f86])).

fof(f152,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f151,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f151,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f131,f99])).

fof(f131,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f30,f42])).

% (28131)Termination reason: Refutation not found, incomplete strategy
fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

% (28131)Memory used [KB]: 10490
fof(f19,plain,(
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
    inference(flattening,[],[f18])).

% (28131)Time elapsed: 0.142 s
fof(f18,plain,(
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

% (28131)------------------------------
% (28131)------------------------------
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

fof(f516,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f515,f333])).

fof(f333,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f286,f308])).

fof(f286,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f239,f279])).

fof(f239,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f163,f210])).

fof(f163,plain,(
    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f162,f31])).

fof(f162,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f140,f29])).

fof(f140,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f30,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f17])).

% (28133)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f515,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f508,f284])).

fof(f284,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f237,f279])).

fof(f237,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f159,f210])).

fof(f159,plain,(
    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f158,f31])).

fof(f158,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_tops_2(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f508,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(resolution,[],[f332,f37])).

fof(f332,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f285,f308])).

fof(f285,plain,(
    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f238,f279])).

fof(f238,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f161,f210])).

fof(f161,plain,(
    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f160,f31])).

fof(f160,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f139,f29])).

fof(f139,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f450,plain,(
    ~ v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f449,f210])).

fof(f449,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f448,f308])).

fof(f448,plain,(
    ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f447,f331])).

fof(f447,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f446,f210])).

fof(f446,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f445,f308])).

fof(f445,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f444,f330])).

fof(f330,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f282,f308])).

fof(f282,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) ),
    inference(backward_demodulation,[],[f235,f279])).

fof(f235,plain,(
    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    inference(backward_demodulation,[],[f150,f210])).

fof(f150,plain,(
    k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f149,f119])).

fof(f149,plain,
    ( ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f148,f114])).

fof(f148,plain,
    ( k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f147,f31])).

fof(f147,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f146,f29])).

fof(f146,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f145,f86])).

fof(f145,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f144,f34])).

fof(f144,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subsumption_resolution,[],[f130,f99])).

fof(f130,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(resolution,[],[f30,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f444,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f443,f210])).

fof(f443,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f442,f308])).

fof(f442,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f441,f333])).

fof(f441,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f440,f210])).

fof(f440,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f439,f308])).

fof(f439,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f438,f332])).

fof(f438,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f437,f210])).

fof(f437,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(forward_demodulation,[],[f436,f308])).

fof(f436,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f435,f281])).

fof(f281,plain,(
    v5_pre_topc(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f234,f279])).

fof(f234,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f129,f210])).

fof(f129,plain,(
    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f31])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f30])).

fof(f127,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f126,f29])).

fof(f126,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f125,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f435,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f434,f393])).

fof(f434,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f433,f284])).

fof(f433,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f432,f36])).

fof(f432,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(subsumption_resolution,[],[f431,f35])).

fof(f431,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v5_pre_topc(k2_funct_1(sK2),sK1,sK0)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1) ),
    inference(resolution,[],[f280,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f280,plain,(
    ~ v3_tops_2(k2_funct_1(sK2),sK1,sK0) ),
    inference(backward_demodulation,[],[f204,f279])).

fof(f204,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) ),
    inference(subsumption_resolution,[],[f193,f86])).

fof(f193,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)
    | ~ l1_struct_0(sK1) ),
    inference(superposition,[],[f33,f50])).

fof(f33,plain,(
    ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (28122)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.53  % (28126)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.54  % (28123)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.54  % (28129)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.54  % (28127)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.55  % (28121)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.55  % (28124)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.55  % (28142)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.55  % (28124)Refutation not found, incomplete strategy% (28124)------------------------------
% 0.21/0.55  % (28124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (28124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (28124)Memory used [KB]: 10618
% 0.21/0.55  % (28124)Time elapsed: 0.123 s
% 0.21/0.55  % (28124)------------------------------
% 0.21/0.55  % (28124)------------------------------
% 0.21/0.56  % (28125)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.56  % (28140)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.56  % (28137)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.56  % (28143)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.56  % (28142)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.57  % (28132)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.57  % (28131)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f525,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(subsumption_resolution,[],[f523,f124])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f123,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v3_tops_2(X2,X0,X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & ~v2_struct_0(X1))) & l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.57    inference(negated_conjecture,[],[f10])).
% 0.21/0.57  fof(f10,conjecture,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_tops_2)).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f121,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f120,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    l1_pre_topc(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f103,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    l1_pre_topc(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f32,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(X2,X0,X1) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  % (28134)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tops_2)).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f523,plain,(
% 0.21/0.57    ~v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f450,f519])).
% 0.21/0.57  fof(f519,plain,(
% 0.21/0.57    sK2 = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(forward_demodulation,[],[f518,f389])).
% 0.21/0.57  fof(f389,plain,(
% 0.21/0.57    sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f388,f29])).
% 0.21/0.57  fof(f388,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f380,f178])).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    v1_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f31,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f380,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(resolution,[],[f119,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f118,f31])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f117,f30])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f116,f29])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f115,f35])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f102,f36])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v2_funct_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f32,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v2_funct_1(X2) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f518,plain,(
% 0.21/0.57    k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f517,f393])).
% 0.21/0.57  fof(f393,plain,(
% 0.21/0.57    v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f392,f29])).
% 0.21/0.57  fof(f392,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f383,f178])).
% 0.21/0.57  fof(f383,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(resolution,[],[f119,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.57  fof(f517,plain,(
% 0.21/0.57    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f516,f331])).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f283,f308])).
% 0.21/0.57  fof(f308,plain,(
% 0.21/0.57    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.57    inference(resolution,[],[f99,f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    l1_struct_0(sK0)),
% 0.21/0.57    inference(resolution,[],[f36,f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.57  fof(f283,plain,(
% 0.21/0.57    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f236,f279])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f240,f210])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f86,f50])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    l1_struct_0(sK1)),
% 0.21/0.57    inference(resolution,[],[f35,f55])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK1) != k2_struct_0(sK1)),
% 0.21/0.57    inference(backward_demodulation,[],[f167,f210])).
% 0.21/0.57  fof(f167,plain,(
% 0.21/0.57    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.57    inference(forward_demodulation,[],[f166,f114])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f113,f31])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f112,f30])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f111,f29])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f110,f35])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f101,f36])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.57    inference(resolution,[],[f32,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f166,plain,(
% 0.21/0.57    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f165,f119])).
% 0.21/0.57  fof(f165,plain,(
% 0.21/0.57    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f164,f31])).
% 0.21/0.57  fof(f164,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f141,f29])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f30,f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f157,f210])).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f156,f119])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f155,f114])).
% 0.21/0.57  % (28131)Refutation not found, incomplete strategy% (28131)------------------------------
% 0.21/0.57  % (28131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f154,f31])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f153,f29])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f152,f86])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f151,f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ~v2_struct_0(sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f131,f99])).
% 0.21/0.57  fof(f131,plain,(
% 0.21/0.57    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(resolution,[],[f30,f42])).
% 0.21/0.57  % (28131)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  
% 0.21/0.57  % (28131)Memory used [KB]: 10490
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  % (28131)Time elapsed: 0.142 s
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f9])).
% 0.21/0.57  % (28131)------------------------------
% 0.21/0.57  % (28131)------------------------------
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.57  fof(f516,plain,(
% 0.21/0.57    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f515,f333])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))),
% 0.21/0.57    inference(backward_demodulation,[],[f286,f308])).
% 0.21/0.57  fof(f286,plain,(
% 0.21/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    inference(backward_demodulation,[],[f239,f279])).
% 0.21/0.57  fof(f239,plain,(
% 0.21/0.57    m1_subset_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    inference(backward_demodulation,[],[f163,f210])).
% 0.21/0.57  fof(f163,plain,(
% 0.21/0.57    m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    inference(subsumption_resolution,[],[f162,f31])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    inference(subsumption_resolution,[],[f140,f29])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.57    inference(resolution,[],[f30,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  % (28133)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.57  fof(f515,plain,(
% 0.21/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f508,f284])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f237,f279])).
% 0.21/0.57  fof(f237,plain,(
% 0.21/0.57    v1_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f159,f210])).
% 0.21/0.57  fof(f159,plain,(
% 0.21/0.57    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f158,f31])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f138,f29])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(resolution,[],[f30,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_tops_2(X0,X1,X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(resolution,[],[f332,f37])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0))),
% 0.21/0.57    inference(backward_demodulation,[],[f285,f308])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    inference(backward_demodulation,[],[f238,f279])).
% 0.21/0.57  fof(f238,plain,(
% 0.21/0.57    v1_funct_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),k2_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    inference(backward_demodulation,[],[f161,f210])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f160,f31])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    inference(subsumption_resolution,[],[f139,f29])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.57    inference(resolution,[],[f30,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f450,plain,(
% 0.21/0.57    ~v5_pre_topc(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f449,f210])).
% 0.21/0.57  fof(f449,plain,(
% 0.21/0.57    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f448,f308])).
% 0.21/0.57  fof(f448,plain,(
% 0.21/0.57    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f447,f331])).
% 0.21/0.57  fof(f447,plain,(
% 0.21/0.57    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f446,f210])).
% 0.21/0.57  fof(f446,plain,(
% 0.21/0.57    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f445,f308])).
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f444,f330])).
% 0.21/0.57  fof(f330,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f282,f308])).
% 0.21/0.57  fof(f282,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f235,f279])).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.21/0.57    inference(backward_demodulation,[],[f150,f210])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f149,f119])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f148,f114])).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f147,f31])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f146,f29])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f145,f86])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f144,f34])).
% 0.21/0.57  fof(f144,plain,(
% 0.21/0.57    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(subsumption_resolution,[],[f130,f99])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.57    inference(resolution,[],[f30,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f444,plain,(
% 0.21/0.57    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f443,f210])).
% 0.21/0.57  fof(f443,plain,(
% 0.21/0.57    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f442,f308])).
% 0.21/0.57  fof(f442,plain,(
% 0.21/0.57    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f441,f333])).
% 0.21/0.57  fof(f441,plain,(
% 0.21/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f440,f210])).
% 0.21/0.57  fof(f440,plain,(
% 0.21/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f439,f308])).
% 0.21/0.57  fof(f439,plain,(
% 0.21/0.57    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f438,f332])).
% 0.21/0.57  fof(f438,plain,(
% 0.21/0.57    ~v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f437,f210])).
% 0.21/0.57  fof(f437,plain,(
% 0.21/0.57    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),k2_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(forward_demodulation,[],[f436,f308])).
% 0.21/0.57  fof(f436,plain,(
% 0.21/0.57    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f435,f281])).
% 0.21/0.57  fof(f281,plain,(
% 0.21/0.57    v5_pre_topc(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f234,f279])).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f129,f210])).
% 0.21/0.57  fof(f129,plain,(
% 0.21/0.57    v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f128,f31])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f127,f30])).
% 0.21/0.57  fof(f127,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f126,f29])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f125,f35])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f104,f36])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(resolution,[],[f32,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f435,plain,(
% 0.21/0.57    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f434,f393])).
% 0.21/0.57  fof(f434,plain,(
% 0.21/0.57    ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f433,f284])).
% 0.21/0.57  fof(f433,plain,(
% 0.21/0.57    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f432,f36])).
% 0.21/0.57  fof(f432,plain,(
% 0.21/0.57    ~l1_pre_topc(sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(subsumption_resolution,[],[f431,f35])).
% 0.21/0.57  fof(f431,plain,(
% 0.21/0.57    ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v5_pre_topc(k2_funct_1(sK2),sK1,sK0) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_funct_1(sK2)),sK0,sK1)),
% 0.21/0.57    inference(resolution,[],[f280,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | ~v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f280,plain,(
% 0.21/0.57    ~v3_tops_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f204,f279])).
% 0.21/0.57  fof(f204,plain,(
% 0.21/0.57    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(subsumption_resolution,[],[f193,f86])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2),sK1,sK0) | ~l1_struct_0(sK1)),
% 0.21/0.57    inference(superposition,[],[f33,f50])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (28142)------------------------------
% 0.21/0.57  % (28142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (28142)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (28142)Memory used [KB]: 1918
% 0.21/0.57  % (28142)Time elapsed: 0.138 s
% 0.21/0.57  % (28142)------------------------------
% 0.21/0.57  % (28142)------------------------------
% 0.21/0.57  % (28120)Success in time 0.216 s
%------------------------------------------------------------------------------
