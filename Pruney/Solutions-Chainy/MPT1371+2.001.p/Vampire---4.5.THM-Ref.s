%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:51 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  152 (1645 expanded)
%              Number of leaves         :   13 ( 317 expanded)
%              Depth                    :   27
%              Number of atoms          :  713 (13253 expanded)
%              Number of equality atoms :  126 (2051 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f239,plain,(
    $false ),
    inference(global_subsumption,[],[f176,f236,f238])).

% (13150)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
fof(f238,plain,(
    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f237,f165])).

fof(f165,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f145,f156])).

fof(f156,plain,(
    u1_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f106,f148])).

fof(f148,plain,(
    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f40,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f40,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f106,plain,(
    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f43,f105])).

fof(f105,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f84,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f52,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f43,plain,(
    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f145,plain,(
    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f144,f104])).

fof(f104,plain,(
    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f44,f103])).

fof(f103,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f83,f70])).

fof(f83,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f50,f80])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f44,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f144,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f143,f103])).

fof(f143,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f142,f105])).

fof(f142,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f141,f106])).

fof(f141,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f140,f47])).

fof(f47,plain,(
    ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f140,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f139,f45])).

fof(f45,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f139,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f138,f40])).

fof(f138,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f137,f52])).

fof(f137,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f38,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f136,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f50])).

fof(f135,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f112,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f112,plain,
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
    inference(resolution,[],[f39,f57])).

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
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f39,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f237,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2)))
    | v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) ),
    inference(resolution,[],[f236,f175])).

fof(f175,plain,(
    ! [X1] :
      ( ~ v4_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2)))
      | v4_pre_topc(k9_relat_1(sK2,X1),sK1) ) ),
    inference(backward_demodulation,[],[f169,f173])).

fof(f173,plain,(
    ! [X2] : k9_relat_1(sK2,X2) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X2) ),
    inference(forward_demodulation,[],[f151,f156])).

fof(f151,plain,(
    ! [X2] : k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k9_relat_1(sK2,X2) ),
    inference(resolution,[],[f40,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f169,plain,(
    ! [X1] :
      ( v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v4_pre_topc(X1,sK0) ) ),
    inference(forward_demodulation,[],[f160,f156])).

fof(f160,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(backward_demodulation,[],[f102,f156])).

fof(f102,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f101,f51])).

fof(f51,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f101,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f100,f44])).

fof(f100,plain,(
    ! [X1] :
      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f99,f42])).

fof(f42,plain,(
    v8_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    ! [X1] :
      ( ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f41,plain,(
    v1_compts_1(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f98,plain,(
    ! [X1] :
      ( ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f97,f40])).

fof(f97,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ v1_compts_1(sK0)
      | ~ v8_pre_topc(sK1)
      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X1,sK0)
      | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1) ) ),
    inference(subsumption_resolution,[],[f96,f39])).

fof(f96,plain,(
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
    inference(subsumption_resolution,[],[f95,f38])).

fof(f95,plain,(
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
    inference(subsumption_resolution,[],[f94,f50])).

fof(f94,plain,(
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
    inference(subsumption_resolution,[],[f93,f49])).

fof(f49,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
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
    inference(subsumption_resolution,[],[f92,f48])).

fof(f92,plain,(
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
    inference(subsumption_resolution,[],[f86,f52])).

fof(f86,plain,(
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
    inference(resolution,[],[f46,f61])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f46,plain,(
    v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f236,plain,(
    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f234,f231])).

fof(f231,plain,(
    sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f230,f45])).

fof(f230,plain,
    ( ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f229,f152])).

fof(f152,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f40,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f229,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f226,f38])).

fof(f226,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))) ),
    inference(resolution,[],[f225,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f225,plain,(
    r1_tarski(sK3(sK0,sK1,sK2),k1_relat_1(sK2)) ),
    inference(resolution,[],[f165,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f234,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0) ),
    inference(subsumption_resolution,[],[f233,f174])).

fof(f174,plain,(
    ! [X0] : m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(backward_demodulation,[],[f170,f173])).

fof(f170,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f149,f156])).

fof(f149,plain,(
    ! [X0] : m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f40,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).

fof(f233,plain,
    ( v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | ~ m1_subset_1(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1)))
    | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0) ),
    inference(resolution,[],[f177,f172])).

fof(f172,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | v4_pre_topc(k10_relat_1(sK2,X0),sK0) ) ),
    inference(backward_demodulation,[],[f159,f171])).

fof(f171,plain,(
    ! [X1] : k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X1) ),
    inference(forward_demodulation,[],[f150,f156])).

fof(f150,plain,(
    ! [X1] : k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1) ),
    inference(resolution,[],[f40,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f159,plain,(
    ! [X0] :
      ( v4_pre_topc(k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1) ) ),
    inference(backward_demodulation,[],[f91,f156])).

fof(f91,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f90,f52])).

fof(f90,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f89,f40])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f88,f39])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f38])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f85,f50])).

fof(f85,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ v1_funct_1(sK2)
      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v4_pre_topc(X0,sK1)
      | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f177,plain,
    ( v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f163,f173])).

fof(f163,plain,
    ( v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f123,f156])).

fof(f123,plain,
    ( v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f122,f104])).

fof(f122,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f121,f103])).

fof(f121,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f120,f105])).

fof(f120,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f119,f106])).

fof(f119,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f118,f47])).

fof(f118,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f117,f45])).

fof(f117,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f116,f40])).

fof(f116,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f115,f52])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f114,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,
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
    inference(subsumption_resolution,[],[f110,f48])).

fof(f110,plain,
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
    inference(resolution,[],[f39,f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f176,plain,
    ( ~ v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f164,f173])).

fof(f164,plain,
    ( ~ v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(backward_demodulation,[],[f134,f156])).

fof(f134,plain,
    ( ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f133,f104])).

fof(f133,plain,
    ( u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f132,f103])).

fof(f132,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f131,f105])).

fof(f131,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f130,f106])).

fof(f130,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f129,f47])).

fof(f129,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f128,f45])).

fof(f128,plain,
    ( k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f126,f52])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,
    ( ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1)
    | ~ v4_pre_topc(sK3(sK0,sK1,sK2),sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f124,f50])).

fof(f124,plain,
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
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
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
    inference(resolution,[],[f39,f56])).

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
      | ~ v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1)
      | ~ v4_pre_topc(sK3(X0,X1,X2),X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:52:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (13156)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.51  % (13172)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (13156)Refutation not found, incomplete strategy% (13156)------------------------------
% 0.22/0.52  % (13156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (13167)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.53  % (13157)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (13170)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.53  % (13156)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (13156)Memory used [KB]: 10746
% 0.22/0.53  % (13156)Time elapsed: 0.086 s
% 0.22/0.53  % (13156)------------------------------
% 0.22/0.53  % (13156)------------------------------
% 0.22/0.54  % (13160)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.56  % (13164)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.56  % (13151)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (13152)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.56  % (13154)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.56  % (13155)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.56  % (13159)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.57  % (13153)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.57  % (13163)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (13171)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  % (13174)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.58  % (13166)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.58  % (13168)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.58  % (13161)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.71/0.58  % (13169)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.71/0.58  % (13175)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.71/0.59  % (13158)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.71/0.59  % (13155)Refutation found. Thanks to Tanya!
% 1.71/0.59  % SZS status Theorem for theBenchmark
% 1.71/0.59  % SZS output start Proof for theBenchmark
% 1.71/0.59  fof(f239,plain,(
% 1.71/0.59    $false),
% 1.71/0.59    inference(global_subsumption,[],[f176,f236,f238])).
% 1.71/0.59  % (13150)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.71/0.59  fof(f238,plain,(
% 1.71/0.59    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f237,f165])).
% 1.71/0.59  fof(f165,plain,(
% 1.71/0.59    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2)))),
% 1.71/0.59    inference(backward_demodulation,[],[f145,f156])).
% 1.71/0.59  fof(f156,plain,(
% 1.71/0.59    u1_struct_0(sK0) = k1_relat_1(sK2)),
% 1.71/0.59    inference(backward_demodulation,[],[f106,f148])).
% 1.71/0.59  fof(f148,plain,(
% 1.71/0.59    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 1.71/0.59    inference(resolution,[],[f40,f69])).
% 1.71/0.59  fof(f69,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f31])).
% 1.71/0.59  fof(f31,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f7])).
% 1.71/0.59  fof(f7,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.71/0.59  fof(f40,plain,(
% 1.71/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f21,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : (~v3_tops_2(X2,X0,X1) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.71/0.59    inference(flattening,[],[f20])).
% 1.71/0.59  fof(f20,plain,(
% 1.71/0.59    ? [X0] : (? [X1] : (? [X2] : ((~v3_tops_2(X2,X0,X1) & (v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f19])).
% 1.71/0.59  fof(f19,negated_conjecture,(
% 1.71/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 1.71/0.59    inference(negated_conjecture,[],[f18])).
% 1.71/0.59  fof(f18,conjecture,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & v8_pre_topc(X1) & v1_compts_1(X0)) => v3_tops_2(X2,X0,X1)))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_compts_1)).
% 1.71/0.59  fof(f106,plain,(
% 1.71/0.59    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.71/0.59    inference(backward_demodulation,[],[f43,f105])).
% 1.71/0.59  fof(f105,plain,(
% 1.71/0.59    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.71/0.59    inference(resolution,[],[f84,f70])).
% 1.71/0.59  fof(f70,plain,(
% 1.71/0.59    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f32])).
% 1.71/0.59  fof(f32,plain,(
% 1.71/0.59    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f14])).
% 1.71/0.59  fof(f14,axiom,(
% 1.71/0.59    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.71/0.59  fof(f84,plain,(
% 1.71/0.59    l1_struct_0(sK0)),
% 1.71/0.59    inference(resolution,[],[f52,f80])).
% 1.71/0.59  fof(f80,plain,(
% 1.71/0.59    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f37])).
% 1.71/0.59  fof(f37,plain,(
% 1.71/0.59    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f15])).
% 1.71/0.59  fof(f15,axiom,(
% 1.71/0.59    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.71/0.59  fof(f52,plain,(
% 1.71/0.59    l1_pre_topc(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f43,plain,(
% 1.71/0.59    k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f145,plain,(
% 1.71/0.59    m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f144,f104])).
% 1.71/0.59  fof(f104,plain,(
% 1.71/0.59    u1_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.71/0.59    inference(backward_demodulation,[],[f44,f103])).
% 1.71/0.59  fof(f103,plain,(
% 1.71/0.59    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.71/0.59    inference(resolution,[],[f83,f70])).
% 1.71/0.59  fof(f83,plain,(
% 1.71/0.59    l1_struct_0(sK1)),
% 1.71/0.59    inference(resolution,[],[f50,f80])).
% 1.71/0.59  fof(f50,plain,(
% 1.71/0.59    l1_pre_topc(sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f44,plain,(
% 1.71/0.59    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f144,plain,(
% 1.71/0.59    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    inference(forward_demodulation,[],[f143,f103])).
% 1.71/0.59  fof(f143,plain,(
% 1.71/0.59    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f142,f105])).
% 1.71/0.59  fof(f142,plain,(
% 1.71/0.59    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    inference(forward_demodulation,[],[f141,f106])).
% 1.71/0.59  fof(f141,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f140,f47])).
% 1.71/0.59  fof(f47,plain,(
% 1.71/0.59    ~v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f140,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f139,f45])).
% 1.71/0.59  fof(f45,plain,(
% 1.71/0.59    v2_funct_1(sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f139,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f138,f40])).
% 1.71/0.59  fof(f138,plain,(
% 1.71/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f137,f52])).
% 1.71/0.59  fof(f137,plain,(
% 1.71/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f136,f38])).
% 1.71/0.59  fof(f38,plain,(
% 1.71/0.59    v1_funct_1(sK2)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f136,plain,(
% 1.71/0.59    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f135,f50])).
% 1.71/0.59  fof(f135,plain,(
% 1.71/0.59    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f112,f48])).
% 1.71/0.59  fof(f48,plain,(
% 1.71/0.59    ~v2_struct_0(sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f112,plain,(
% 1.71/0.59    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(resolution,[],[f39,f57])).
% 1.71/0.59  fof(f57,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | v3_tops_2(X2,X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f23])).
% 1.71/0.59  fof(f23,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(flattening,[],[f22])).
% 1.71/0.59  fof(f22,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : ((v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f16])).
% 1.71/0.59  fof(f16,axiom,(
% 1.71/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) <=> v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k2_struct_0(X0) = k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_tops_2)).
% 1.71/0.59  fof(f39,plain,(
% 1.71/0.59    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f237,plain,(
% 1.71/0.59    ~m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k1_relat_1(sK2))) | v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1)),
% 1.71/0.59    inference(resolution,[],[f236,f175])).
% 1.71/0.59  fof(f175,plain,(
% 1.71/0.59    ( ! [X1] : (~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2))) | v4_pre_topc(k9_relat_1(sK2,X1),sK1)) )),
% 1.71/0.59    inference(backward_demodulation,[],[f169,f173])).
% 1.71/0.59  fof(f173,plain,(
% 1.71/0.59    ( ! [X2] : (k9_relat_1(sK2,X2) = k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X2)) )),
% 1.71/0.59    inference(forward_demodulation,[],[f151,f156])).
% 1.71/0.59  fof(f151,plain,(
% 1.71/0.59    ( ! [X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2) = k9_relat_1(sK2,X2)) )),
% 1.71/0.59    inference(resolution,[],[f40,f73])).
% 1.71/0.59  fof(f73,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f35])).
% 1.71/0.59  fof(f35,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f9])).
% 1.71/0.59  fof(f9,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.71/0.59  fof(f169,plain,(
% 1.71/0.59    ( ! [X1] : (v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2))) | ~v4_pre_topc(X1,sK0)) )),
% 1.71/0.59    inference(forward_demodulation,[],[f160,f156])).
% 1.71/0.59  fof(f160,plain,(
% 1.71/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_relat_1(sK2))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(backward_demodulation,[],[f102,f156])).
% 1.71/0.59  fof(f102,plain,(
% 1.71/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f101,f51])).
% 1.71/0.59  fof(f51,plain,(
% 1.71/0.59    v2_pre_topc(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f101,plain,(
% 1.71/0.59    ( ! [X1] : (~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f100,f44])).
% 1.71/0.59  fof(f100,plain,(
% 1.71/0.59    ( ! [X1] : (k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f99,f42])).
% 1.71/0.59  fof(f42,plain,(
% 1.71/0.59    v8_pre_topc(sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f99,plain,(
% 1.71/0.59    ( ! [X1] : (~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f98,f41])).
% 1.71/0.59  fof(f41,plain,(
% 1.71/0.59    v1_compts_1(sK0)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f98,plain,(
% 1.71/0.59    ( ! [X1] : (~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f97,f40])).
% 1.71/0.59  fof(f97,plain,(
% 1.71/0.59    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f96,f39])).
% 1.71/0.59  fof(f96,plain,(
% 1.71/0.59    ( ! [X1] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f95,f38])).
% 1.71/0.59  fof(f95,plain,(
% 1.71/0.59    ( ! [X1] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f94,f50])).
% 1.71/0.59  fof(f94,plain,(
% 1.71/0.59    ( ! [X1] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f93,f49])).
% 1.71/0.59  fof(f49,plain,(
% 1.71/0.59    v2_pre_topc(sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f93,plain,(
% 1.71/0.59    ( ! [X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f92,f48])).
% 1.71/0.59  fof(f92,plain,(
% 1.71/0.59    ( ! [X1] : (v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f86,f52])).
% 1.71/0.59  fof(f86,plain,(
% 1.71/0.59    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_compts_1(sK0) | ~v8_pre_topc(sK1) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X1,sK0) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1),sK1)) )),
% 1.71/0.59    inference(resolution,[],[f46,f61])).
% 1.71/0.59  fof(f61,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_compts_1(X0) | ~v8_pre_topc(X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f25])).
% 1.71/0.59  fof(f25,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.71/0.59    inference(flattening,[],[f24])).
% 1.71/0.59  fof(f24,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1) | ~v4_pre_topc(X3,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~v5_pre_topc(X2,X0,X1) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v8_pre_topc(X1) | ~v1_compts_1(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.71/0.59    inference(ennf_transformation,[],[f17])).
% 1.71/0.59  fof(f17,axiom,(
% 1.71/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v5_pre_topc(X2,X0,X1) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & v8_pre_topc(X1) & v1_compts_1(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X3,X0) => v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X1)))))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_compts_1)).
% 1.71/0.59  fof(f46,plain,(
% 1.71/0.59    v5_pre_topc(sK2,sK0,sK1)),
% 1.71/0.59    inference(cnf_transformation,[],[f21])).
% 1.71/0.59  fof(f236,plain,(
% 1.71/0.59    v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(duplicate_literal_removal,[],[f235])).
% 1.71/0.59  fof(f235,plain,(
% 1.71/0.59    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(forward_demodulation,[],[f234,f231])).
% 1.71/0.59  fof(f231,plain,(
% 1.71/0.59    sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f230,f45])).
% 1.71/0.59  fof(f230,plain,(
% 1.71/0.59    ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f229,f152])).
% 1.71/0.59  fof(f152,plain,(
% 1.71/0.59    v1_relat_1(sK2)),
% 1.71/0.59    inference(resolution,[],[f40,f79])).
% 1.71/0.59  fof(f79,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f36])).
% 1.71/0.59  fof(f36,plain,(
% 1.71/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f4])).
% 1.71/0.59  fof(f4,axiom,(
% 1.71/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.71/0.59  fof(f229,plain,(
% 1.71/0.59    ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 1.71/0.59    inference(subsumption_resolution,[],[f226,f38])).
% 1.71/0.59  fof(f226,plain,(
% 1.71/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v2_funct_1(sK2) | sK3(sK0,sK1,sK2) = k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2)))),
% 1.71/0.59    inference(resolution,[],[f225,f66])).
% 1.71/0.59  fof(f66,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 1.71/0.59    inference(cnf_transformation,[],[f29])).
% 1.71/0.59  fof(f29,plain,(
% 1.71/0.59    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.71/0.59    inference(flattening,[],[f28])).
% 1.71/0.59  fof(f28,plain,(
% 1.71/0.59    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.71/0.59    inference(ennf_transformation,[],[f3])).
% 1.71/0.59  fof(f3,axiom,(
% 1.71/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 1.71/0.59  fof(f225,plain,(
% 1.71/0.59    r1_tarski(sK3(sK0,sK1,sK2),k1_relat_1(sK2))),
% 1.71/0.59    inference(resolution,[],[f165,f75])).
% 1.71/0.59  fof(f75,plain,(
% 1.71/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f2])).
% 1.71/0.59  fof(f2,axiom,(
% 1.71/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.59  fof(f234,plain,(
% 1.71/0.59    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f233,f174])).
% 1.71/0.59  fof(f174,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k9_relat_1(sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.71/0.59    inference(backward_demodulation,[],[f170,f173])).
% 1.71/0.59  fof(f170,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.71/0.59    inference(forward_demodulation,[],[f149,f156])).
% 1.71/0.59  fof(f149,plain,(
% 1.71/0.59    ( ! [X0] : (m1_subset_1(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.71/0.59    inference(resolution,[],[f40,f71])).
% 1.71/0.59  fof(f71,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))) )),
% 1.71/0.59    inference(cnf_transformation,[],[f33])).
% 1.71/0.59  fof(f33,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f6])).
% 1.71/0.59  fof(f6,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relset_1)).
% 1.71/0.59  fof(f233,plain,(
% 1.71/0.59    v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | ~m1_subset_1(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k10_relat_1(sK2,k9_relat_1(sK2,sK3(sK0,sK1,sK2))),sK0)),
% 1.71/0.59    inference(resolution,[],[f177,f172])).
% 1.71/0.59  fof(f172,plain,(
% 1.71/0.59    ( ! [X0] : (~v4_pre_topc(X0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | v4_pre_topc(k10_relat_1(sK2,X0),sK0)) )),
% 1.71/0.59    inference(backward_demodulation,[],[f159,f171])).
% 1.71/0.59  fof(f171,plain,(
% 1.71/0.59    ( ! [X1] : (k10_relat_1(sK2,X1) = k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X1)) )),
% 1.71/0.59    inference(forward_demodulation,[],[f150,f156])).
% 1.71/0.59  fof(f150,plain,(
% 1.71/0.59    ( ! [X1] : (k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X1) = k10_relat_1(sK2,X1)) )),
% 1.71/0.59    inference(resolution,[],[f40,f72])).
% 1.71/0.59  fof(f72,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f34])).
% 1.71/0.59  fof(f34,plain,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.71/0.59    inference(ennf_transformation,[],[f10])).
% 1.71/0.59  fof(f10,axiom,(
% 1.71/0.59    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.71/0.59  fof(f159,plain,(
% 1.71/0.59    ( ! [X0] : (v4_pre_topc(k8_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1)) )),
% 1.71/0.59    inference(backward_demodulation,[],[f91,f156])).
% 1.71/0.59  fof(f91,plain,(
% 1.71/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f90,f52])).
% 1.71/0.59  fof(f90,plain,(
% 1.71/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f89,f40])).
% 1.71/0.59  fof(f89,plain,(
% 1.71/0.59    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f88,f39])).
% 1.71/0.59  fof(f88,plain,(
% 1.71/0.59    ( ! [X0] : (~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f87,f38])).
% 1.71/0.59  fof(f87,plain,(
% 1.71/0.59    ( ! [X0] : (~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.71/0.59    inference(subsumption_resolution,[],[f85,f50])).
% 1.71/0.59  fof(f85,plain,(
% 1.71/0.59    ( ! [X0] : (~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | ~v4_pre_topc(X0,sK1) | v4_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0),sK0) | ~l1_pre_topc(sK0)) )),
% 1.71/0.59    inference(resolution,[],[f46,f62])).
% 1.71/0.59  fof(f62,plain,(
% 1.71/0.59    ( ! [X2,X0,X3,X1] : (~v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v4_pre_topc(X3,X1) | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~l1_pre_topc(X0)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f27])).
% 1.71/0.59  fof(f27,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(flattening,[],[f26])).
% 1.71/0.59  fof(f26,plain,(
% 1.71/0.59    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v4_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.71/0.59    inference(ennf_transformation,[],[f13])).
% 1.71/0.59  fof(f13,axiom,(
% 1.71/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X3,X1) => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)))))))),
% 1.71/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).
% 1.71/0.59  fof(f177,plain,(
% 1.71/0.59    v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(backward_demodulation,[],[f163,f173])).
% 1.71/0.59  fof(f163,plain,(
% 1.71/0.59    v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(backward_demodulation,[],[f123,f156])).
% 1.71/0.59  fof(f123,plain,(
% 1.71/0.59    v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f122,f104])).
% 1.71/0.59  fof(f122,plain,(
% 1.71/0.59    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(forward_demodulation,[],[f121,f103])).
% 1.71/0.59  fof(f121,plain,(
% 1.71/0.59    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f120,f105])).
% 1.71/0.59  fof(f120,plain,(
% 1.71/0.59    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(forward_demodulation,[],[f119,f106])).
% 1.71/0.59  fof(f119,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f118,f47])).
% 1.71/0.59  fof(f118,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f117,f45])).
% 1.71/0.59  fof(f117,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f116,f40])).
% 1.71/0.59  fof(f116,plain,(
% 1.71/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f115,f52])).
% 1.71/0.59  fof(f115,plain,(
% 1.71/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f114,f38])).
% 1.71/0.59  fof(f114,plain,(
% 1.71/0.59    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f113,f50])).
% 1.71/0.59  fof(f113,plain,(
% 1.71/0.59    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f110,f48])).
% 1.71/0.59  fof(f110,plain,(
% 1.71/0.59    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(resolution,[],[f39,f55])).
% 1.71/0.59  fof(f55,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1) | v4_pre_topc(sK3(X0,X1,X2),X0) | v3_tops_2(X2,X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f23])).
% 1.71/0.59  fof(f176,plain,(
% 1.71/0.59    ~v4_pre_topc(k9_relat_1(sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(backward_demodulation,[],[f164,f173])).
% 1.71/0.59  fof(f164,plain,(
% 1.71/0.59    ~v4_pre_topc(k7_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(backward_demodulation,[],[f134,f156])).
% 1.71/0.59  fof(f134,plain,(
% 1.71/0.59    ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f133,f104])).
% 1.71/0.59  fof(f133,plain,(
% 1.71/0.59    u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(forward_demodulation,[],[f132,f103])).
% 1.71/0.59  fof(f132,plain,(
% 1.71/0.59    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f131,f105])).
% 1.71/0.59  fof(f131,plain,(
% 1.71/0.59    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(forward_demodulation,[],[f130,f106])).
% 1.71/0.59  fof(f130,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 1.71/0.59    inference(subsumption_resolution,[],[f129,f47])).
% 1.71/0.59  fof(f129,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f128,f45])).
% 1.71/0.59  fof(f128,plain,(
% 1.71/0.59    k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f127,f40])).
% 1.71/0.59  fof(f127,plain,(
% 1.71/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f126,f52])).
% 1.71/0.59  fof(f126,plain,(
% 1.71/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f125,f38])).
% 1.71/0.59  fof(f125,plain,(
% 1.71/0.59    ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f124,f50])).
% 1.71/0.59  fof(f124,plain,(
% 1.71/0.59    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(subsumption_resolution,[],[f111,f48])).
% 1.71/0.59  fof(f111,plain,(
% 1.71/0.59    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK1) | ~v4_pre_topc(sK3(sK0,sK1,sK2),sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.71/0.59    inference(resolution,[],[f39,f56])).
% 1.71/0.59  fof(f56,plain,(
% 1.71/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | ~v4_pre_topc(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X1) | ~v4_pre_topc(sK3(X0,X1,X2),X0) | v3_tops_2(X2,X0,X1)) )),
% 1.71/0.59    inference(cnf_transformation,[],[f23])).
% 1.71/0.59  % SZS output end Proof for theBenchmark
% 1.71/0.59  % (13155)------------------------------
% 1.71/0.59  % (13155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (13155)Termination reason: Refutation
% 1.71/0.59  
% 1.71/0.59  % (13155)Memory used [KB]: 6396
% 1.71/0.59  % (13155)Time elapsed: 0.108 s
% 1.71/0.59  % (13155)------------------------------
% 1.71/0.59  % (13155)------------------------------
% 1.71/0.59  % (13149)Success in time 0.232 s
%------------------------------------------------------------------------------
