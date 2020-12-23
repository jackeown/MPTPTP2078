%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:25 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  199 (2626 expanded)
%              Number of leaves         :   29 ( 873 expanded)
%              Depth                    :   39
%              Number of atoms          :  742 (16473 expanded)
%              Number of equality atoms :   93 ( 874 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1995,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1994,f1235])).

fof(f1235,plain,(
    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1234,f145])).

fof(f145,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f89,f138])).

fof(f138,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f90,f78])).

fof(f78,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f52,f51,f50])).

fof(f50,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v5_pre_topc(X2,X0,X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,sK0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK0)
      & v1_tdlat_3(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v5_pre_topc(X2,sK0,X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ~ v5_pre_topc(X2,sK0,sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X2] :
        ( ~ v5_pre_topc(X2,sK0,sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ v5_pre_topc(sK2,sK0,sK1)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v5_pre_topc(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => v5_pre_topc(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => v5_pre_topc(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f1234,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1233,f1035])).

fof(f1035,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f675,f766])).

fof(f766,plain,(
    ! [X2] : v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),sK0) ),
    inference(resolution,[],[f463,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f209,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f209,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f208,f145])).

fof(f208,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f207,f78])).

fof(f207,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f136,f77])).

fof(f77,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f136,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f103,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f103,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v3_pre_topc(sK4(X0),X0)
            & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f463,plain,(
    ! [X16] : r1_tarski(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X16),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f462,f146])).

fof(f146,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f89,f139])).

fof(f139,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f90,f80])).

fof(f80,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f462,plain,(
    ! [X16] : r1_tarski(k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X16),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f458,f145])).

fof(f458,plain,(
    ! [X16] : r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X16),u1_struct_0(sK0)) ),
    inference(resolution,[],[f222,f83])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f222,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1) ) ),
    inference(resolution,[],[f130,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f675,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f674,f145])).

fof(f674,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f673,f146])).

fof(f673,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f672,f78])).

fof(f672,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f671,f80])).

fof(f671,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f670,f84])).

fof(f84,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f670,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f664,f82])).

fof(f82,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f664,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f298,f83])).

fof(f298,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f98,f81])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
                    & v3_pre_topc(sK3(X0,X1,X2),X1)
                    & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v3_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k1_xboole_0 != k2_struct_0(X0)
                & k1_xboole_0 = k2_struct_0(X1) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f1233,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1208,f146])).

fof(f1208,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(superposition,[],[f82,f1078])).

fof(f1078,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f1077,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1077,plain,(
    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1076,f86])).

fof(f86,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1076,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1042,f133])).

fof(f1042,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[],[f206,f1035])).

fof(f206,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f159,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f159,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f158,f145])).

fof(f158,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f155,f146])).

fof(f155,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f83,f121])).

fof(f1994,plain,(
    ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1993,f145])).

fof(f1993,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1992,f1035])).

fof(f1992,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1991,f146])).

fof(f1991,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1990,f86])).

fof(f1990,plain,
    ( ~ r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1989,f445])).

fof(f445,plain,(
    ! [X4,X3] : k1_xboole_0 = k8_relset_1(X3,X4,k1_xboole_0,X4) ),
    inference(forward_demodulation,[],[f436,f412])).

fof(f412,plain,(
    ! [X0,X1] : k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(forward_demodulation,[],[f406,f165])).

fof(f165,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f164,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f164,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k1_xboole_0),X3) ),
    inference(subsumption_resolution,[],[f163,f113])).

fof(f113,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f163,plain,(
    ! [X3] :
      ( ~ v4_relat_1(k1_xboole_0,X3)
      | r1_tarski(k1_relat_1(k1_xboole_0),X3) ) ),
    inference(resolution,[],[f115,f140])).

fof(f140,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f112,f133])).

fof(f112,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | r1_tarski(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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

fof(f406,plain,(
    ! [X0,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f216,f86])).

fof(f216,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,k2_zfmisc_1(X2,X3))
      | k1_relset_1(X2,X3,X4) = k1_relat_1(X4) ) ),
    inference(resolution,[],[f127,f122])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f436,plain,(
    ! [X4,X3] : k1_relset_1(X3,X4,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,X4) ),
    inference(resolution,[],[f426,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f426,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f425,f135])).

fof(f135,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f88,f87])).

fof(f87,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f425,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f424,f133])).

fof(f424,plain,(
    ! [X0] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(superposition,[],[f130,f419])).

fof(f419,plain,(
    ! [X0] : k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f415,f165])).

fof(f415,plain,(
    ! [X0] : k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f253,f133])).

fof(f253,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(forward_demodulation,[],[f247,f215])).

fof(f215,plain,(
    ! [X0,X1] : k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) ),
    inference(resolution,[],[f127,f135])).

fof(f247,plain,(
    ! [X0,X1] : k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1) ),
    inference(resolution,[],[f129,f135])).

fof(f1989,plain,
    ( ~ r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1988,f698])).

fof(f698,plain,(
    ! [X2,X1] : k8_relset_1(k2_struct_0(sK0),X1,k1_xboole_0,X2) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X1,k1_xboole_0,X2)) ),
    inference(resolution,[],[f343,f456])).

fof(f456,plain,(
    ! [X8,X7,X9] : r1_tarski(k8_relset_1(X7,X8,k1_xboole_0,X9),X7) ),
    inference(resolution,[],[f222,f426])).

fof(f343,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_struct_0(sK0))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f234,f122])).

fof(f234,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f233,f214])).

fof(f214,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f213,f145])).

fof(f213,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f212,f78])).

fof(f212,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f137,f77])).

fof(f137,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f106,f91])).

fof(f106,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ( ~ v4_pre_topc(sK5(X0),X0)
            & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( v4_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v1_tdlat_3(X0)
          | ? [X1] :
              ( ~ v4_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( v4_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f233,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(forward_demodulation,[],[f231,f145])).

fof(f231,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f100,f78])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f1988,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1987,f145])).

fof(f1987,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1986,f1035])).

fof(f1986,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1985,f146])).

fof(f1985,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1984,f76])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f1984,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1983,f78])).

fof(f1983,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1982,f79])).

fof(f79,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f1982,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1981,f80])).

fof(f1981,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1980,f1207])).

fof(f1207,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f81,f1078])).

fof(f1980,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1979,f426])).

fof(f1979,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1977,f1210])).

fof(f1210,plain,(
    ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(superposition,[],[f84,f1078])).

fof(f1977,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f111,f1895])).

fof(f1895,plain,(
    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) ),
    inference(resolution,[],[f1858,f102])).

fof(f1858,plain,(
    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1857,f1078])).

fof(f1857,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1856,f1035])).

fof(f1856,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f1855,f146])).

fof(f1855,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1854,f76])).

fof(f1854,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1853,f78])).

fof(f1853,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1852,f79])).

fof(f1852,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1851,f80])).

fof(f1851,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1850,f84])).

fof(f1850,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f1843,f82])).

fof(f1843,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f661,f83])).

fof(f661,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(sK6(X0,X1,sK2),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f291,f81])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | v5_pre_topc(X0,X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | r1_tarski(sK6(X1,X2,X0),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f110,f121])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4)))
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
      | v5_pre_topc(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:34:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (25698)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (25715)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (25710)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.53  % (25709)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  % (25696)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  % (25706)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (25695)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (25699)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (25706)Refutation not found, incomplete strategy% (25706)------------------------------
% 0.21/0.53  % (25706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (25706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (25706)Memory used [KB]: 6140
% 0.21/0.53  % (25706)Time elapsed: 0.108 s
% 0.21/0.53  % (25706)------------------------------
% 0.21/0.53  % (25706)------------------------------
% 0.21/0.53  % (25701)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.54  % (25699)Refutation not found, incomplete strategy% (25699)------------------------------
% 0.21/0.54  % (25699)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25699)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25699)Memory used [KB]: 10618
% 0.21/0.54  % (25699)Time elapsed: 0.099 s
% 0.21/0.54  % (25699)------------------------------
% 0.21/0.54  % (25699)------------------------------
% 0.21/0.54  % (25697)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (25714)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.54  % (25717)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (25693)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (25703)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.54  % (25713)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.54  % (25693)Refutation not found, incomplete strategy% (25693)------------------------------
% 0.21/0.54  % (25693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (25693)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (25693)Memory used [KB]: 10490
% 0.21/0.54  % (25693)Time elapsed: 0.002 s
% 0.21/0.54  % (25693)------------------------------
% 0.21/0.54  % (25693)------------------------------
% 0.21/0.55  % (25707)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.55  % (25711)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.55  % (25705)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (25708)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (25704)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (25704)Refutation not found, incomplete strategy% (25704)------------------------------
% 0.21/0.55  % (25704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (25704)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (25704)Memory used [KB]: 10490
% 0.21/0.55  % (25704)Time elapsed: 0.002 s
% 0.21/0.55  % (25704)------------------------------
% 0.21/0.55  % (25704)------------------------------
% 0.21/0.55  % (25712)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (25716)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (25700)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (25702)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (25718)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.57  % (25694)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.57  % (25698)Refutation not found, incomplete strategy% (25698)------------------------------
% 0.21/0.57  % (25698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (25698)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (25698)Memory used [KB]: 6524
% 0.21/0.57  % (25698)Time elapsed: 0.126 s
% 0.21/0.57  % (25698)------------------------------
% 0.21/0.57  % (25698)------------------------------
% 2.03/0.64  % (25709)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.64  % SZS output start Proof for theBenchmark
% 2.03/0.64  fof(f1995,plain,(
% 2.03/0.64    $false),
% 2.03/0.64    inference(subsumption_resolution,[],[f1994,f1235])).
% 2.03/0.64  fof(f1235,plain,(
% 2.03/0.64    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1234,f145])).
% 2.03/0.64  fof(f145,plain,(
% 2.03/0.64    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.03/0.64    inference(resolution,[],[f89,f138])).
% 2.03/0.64  fof(f138,plain,(
% 2.03/0.64    l1_struct_0(sK0)),
% 2.03/0.64    inference(resolution,[],[f90,f78])).
% 2.03/0.64  fof(f78,plain,(
% 2.03/0.64    l1_pre_topc(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f53,plain,(
% 2.03/0.64    ((~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0)),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f52,f51,f50])).
% 2.03/0.64  fof(f50,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f51,plain,(
% 2.03/0.64    ? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f52,plain,(
% 2.03/0.64    ? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f28,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f27])).
% 2.03/0.64  fof(f27,plain,(
% 2.03/0.64    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f26])).
% 2.03/0.64  fof(f26,negated_conjecture,(
% 2.03/0.64    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.03/0.64    inference(negated_conjecture,[],[f25])).
% 2.03/0.64  fof(f25,conjecture,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_tex_2)).
% 2.03/0.64  fof(f90,plain,(
% 2.03/0.64    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f30])).
% 2.03/0.64  fof(f30,plain,(
% 2.03/0.64    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f18])).
% 2.03/0.64  fof(f18,axiom,(
% 2.03/0.64    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.03/0.64  fof(f89,plain,(
% 2.03/0.64    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f29])).
% 2.03/0.64  fof(f29,plain,(
% 2.03/0.64    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f17])).
% 2.03/0.64  fof(f17,axiom,(
% 2.03/0.64    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 2.03/0.64  fof(f1234,plain,(
% 2.03/0.64    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1233,f1035])).
% 2.03/0.64  fof(f1035,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1)),
% 2.03/0.64    inference(resolution,[],[f675,f766])).
% 2.03/0.64  fof(f766,plain,(
% 2.03/0.64    ( ! [X2] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),sK0)) )),
% 2.03/0.64    inference(resolution,[],[f463,f211])).
% 2.03/0.64  fof(f211,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | v3_pre_topc(X0,sK0)) )),
% 2.03/0.64    inference(resolution,[],[f209,f122])).
% 2.03/0.64  fof(f122,plain,(
% 2.03/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f73])).
% 2.03/0.64  fof(f73,plain,(
% 2.03/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.03/0.64    inference(nnf_transformation,[],[f9])).
% 2.03/0.64  fof(f9,axiom,(
% 2.03/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.03/0.64  fof(f209,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f208,f145])).
% 2.03/0.64  fof(f208,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f207,f78])).
% 2.03/0.64  fof(f207,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(resolution,[],[f136,f77])).
% 2.03/0.64  fof(f77,plain,(
% 2.03/0.64    v1_tdlat_3(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f136,plain,(
% 2.03/0.64    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f103,f91])).
% 2.03/0.64  fof(f91,plain,(
% 2.03/0.64    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f32])).
% 2.03/0.64  fof(f32,plain,(
% 2.03/0.64    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f31])).
% 2.03/0.64  fof(f31,plain,(
% 2.03/0.64    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f22])).
% 2.03/0.64  fof(f22,axiom,(
% 2.03/0.64    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 2.03/0.64  fof(f103,plain,(
% 2.03/0.64    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f61])).
% 2.03/0.64  fof(f61,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f59,f60])).
% 2.03/0.64  fof(f60,plain,(
% 2.03/0.64    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f59,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(rectify,[],[f58])).
% 2.03/0.64  fof(f58,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f39])).
% 2.03/0.64  fof(f39,plain,(
% 2.03/0.64    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f38])).
% 2.03/0.64  fof(f38,plain,(
% 2.03/0.64    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f23])).
% 2.03/0.64  fof(f23,axiom,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tdlat_3)).
% 2.03/0.64  fof(f463,plain,(
% 2.03/0.64    ( ! [X16] : (r1_tarski(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X16),k2_struct_0(sK0))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f462,f146])).
% 2.03/0.64  fof(f146,plain,(
% 2.03/0.64    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.03/0.64    inference(resolution,[],[f89,f139])).
% 2.03/0.64  fof(f139,plain,(
% 2.03/0.64    l1_struct_0(sK1)),
% 2.03/0.64    inference(resolution,[],[f90,f80])).
% 2.03/0.64  fof(f80,plain,(
% 2.03/0.64    l1_pre_topc(sK1)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f462,plain,(
% 2.03/0.64    ( ! [X16] : (r1_tarski(k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X16),k2_struct_0(sK0))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f458,f145])).
% 2.03/0.64  fof(f458,plain,(
% 2.03/0.64    ( ! [X16] : (r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X16),u1_struct_0(sK0))) )),
% 2.03/0.64    inference(resolution,[],[f222,f83])).
% 2.03/0.64  fof(f83,plain,(
% 2.03/0.64    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f222,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k8_relset_1(X1,X2,X0,X3),X1)) )),
% 2.03/0.64    inference(resolution,[],[f130,f121])).
% 2.03/0.64  fof(f121,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f73])).
% 2.03/0.64  fof(f130,plain,(
% 2.03/0.64    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f49])).
% 2.03/0.64  fof(f49,plain,(
% 2.03/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.64    inference(ennf_transformation,[],[f14])).
% 2.03/0.64  fof(f14,axiom,(
% 2.03/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.03/0.64  fof(f675,plain,(
% 2.03/0.64    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | k1_xboole_0 = k2_struct_0(sK1)),
% 2.03/0.64    inference(forward_demodulation,[],[f674,f145])).
% 2.03/0.64  fof(f674,plain,(
% 2.03/0.64    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | k1_xboole_0 = k2_struct_0(sK1)),
% 2.03/0.64    inference(forward_demodulation,[],[f673,f146])).
% 2.03/0.64  fof(f673,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f672,f78])).
% 2.03/0.64  fof(f672,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f671,f80])).
% 2.03/0.64  fof(f671,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f670,f84])).
% 2.03/0.64  fof(f84,plain,(
% 2.03/0.64    ~v5_pre_topc(sK2,sK0,sK1)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f670,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f664,f82])).
% 2.03/0.64  fof(f82,plain,(
% 2.03/0.64    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f664,plain,(
% 2.03/0.64    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.03/0.64    inference(resolution,[],[f298,f83])).
% 2.03/0.64  fof(f298,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_xboole_0 = k2_struct_0(X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(resolution,[],[f98,f81])).
% 2.03/0.64  fof(f81,plain,(
% 2.03/0.64    v1_funct_1(sK2)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f98,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f57])).
% 2.03/0.64  fof(f57,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f55,f56])).
% 2.03/0.64  fof(f56,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f55,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(rectify,[],[f54])).
% 2.03/0.64  fof(f54,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f34])).
% 2.03/0.64  fof(f34,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f33])).
% 2.03/0.64  fof(f33,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f20])).
% 2.03/0.64  fof(f20,axiom,(
% 2.03/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 2.03/0.64  fof(f1233,plain,(
% 2.03/0.64    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1208,f146])).
% 2.03/0.64  fof(f1208,plain,(
% 2.03/0.64    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(superposition,[],[f82,f1078])).
% 2.03/0.64  fof(f1078,plain,(
% 2.03/0.64    k1_xboole_0 = sK2),
% 2.03/0.64    inference(forward_demodulation,[],[f1077,f133])).
% 2.03/0.64  fof(f133,plain,(
% 2.03/0.64    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.03/0.64    inference(equality_resolution,[],[f125])).
% 2.03/0.64  fof(f125,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f75])).
% 2.03/0.64  fof(f75,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    inference(flattening,[],[f74])).
% 2.03/0.64  fof(f74,plain,(
% 2.03/0.64    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.03/0.64    inference(nnf_transformation,[],[f6])).
% 2.03/0.64  fof(f6,axiom,(
% 2.03/0.64    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.03/0.64  fof(f1077,plain,(
% 2.03/0.64    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1076,f86])).
% 2.03/0.64  fof(f86,plain,(
% 2.03/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f3])).
% 2.03/0.64  fof(f3,axiom,(
% 2.03/0.64    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.03/0.64  fof(f1076,plain,(
% 2.03/0.64    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1042,f133])).
% 2.03/0.64  fof(f1042,plain,(
% 2.03/0.64    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(superposition,[],[f206,f1035])).
% 2.03/0.64  fof(f206,plain,(
% 2.03/0.64    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.03/0.64    inference(resolution,[],[f159,f120])).
% 2.03/0.64  fof(f120,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f72])).
% 2.03/0.64  fof(f72,plain,(
% 2.03/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.64    inference(flattening,[],[f71])).
% 2.03/0.64  fof(f71,plain,(
% 2.03/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.03/0.64    inference(nnf_transformation,[],[f2])).
% 2.03/0.64  fof(f2,axiom,(
% 2.03/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.03/0.64  fof(f159,plain,(
% 2.03/0.64    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 2.03/0.64    inference(forward_demodulation,[],[f158,f145])).
% 2.03/0.64  fof(f158,plain,(
% 2.03/0.64    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))),
% 2.03/0.64    inference(forward_demodulation,[],[f155,f146])).
% 2.03/0.64  fof(f155,plain,(
% 2.03/0.64    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 2.03/0.64    inference(resolution,[],[f83,f121])).
% 2.03/0.64  fof(f1994,plain,(
% 2.03/0.64    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1993,f145])).
% 2.03/0.64  fof(f1993,plain,(
% 2.03/0.64    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1992,f1035])).
% 2.03/0.64  fof(f1992,plain,(
% 2.03/0.64    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1991,f146])).
% 2.03/0.64  fof(f1991,plain,(
% 2.03/0.64    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1990,f86])).
% 2.03/0.64  fof(f1990,plain,(
% 2.03/0.64    ~r1_tarski(k1_xboole_0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1989,f445])).
% 2.03/0.64  fof(f445,plain,(
% 2.03/0.64    ( ! [X4,X3] : (k1_xboole_0 = k8_relset_1(X3,X4,k1_xboole_0,X4)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f436,f412])).
% 2.03/0.64  fof(f412,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_xboole_0 = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f406,f165])).
% 2.03/0.64  fof(f165,plain,(
% 2.03/0.64    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.03/0.64    inference(resolution,[],[f164,f102])).
% 2.03/0.64  fof(f102,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f37])).
% 2.03/0.64  fof(f37,plain,(
% 2.03/0.64    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.03/0.64    inference(ennf_transformation,[],[f4])).
% 2.03/0.64  fof(f4,axiom,(
% 2.03/0.64    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 2.03/0.64  fof(f164,plain,(
% 2.03/0.64    ( ! [X3] : (r1_tarski(k1_relat_1(k1_xboole_0),X3)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f163,f113])).
% 2.03/0.64  fof(f113,plain,(
% 2.03/0.64    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f12])).
% 2.03/0.64  fof(f12,axiom,(
% 2.03/0.64    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).
% 2.03/0.64  fof(f163,plain,(
% 2.03/0.64    ( ! [X3] : (~v4_relat_1(k1_xboole_0,X3) | r1_tarski(k1_relat_1(k1_xboole_0),X3)) )),
% 2.03/0.64    inference(resolution,[],[f115,f140])).
% 2.03/0.64  fof(f140,plain,(
% 2.03/0.64    v1_relat_1(k1_xboole_0)),
% 2.03/0.64    inference(superposition,[],[f112,f133])).
% 2.03/0.64  fof(f112,plain,(
% 2.03/0.64    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f11])).
% 2.03/0.64  fof(f11,axiom,(
% 2.03/0.64    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.03/0.64  fof(f115,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | r1_tarski(k1_relat_1(X1),X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f70])).
% 2.03/0.64  fof(f70,plain,(
% 2.03/0.64    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.03/0.64    inference(nnf_transformation,[],[f44])).
% 2.03/0.64  fof(f44,plain,(
% 2.03/0.64    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.03/0.64    inference(ennf_transformation,[],[f10])).
% 2.03/0.64  fof(f10,axiom,(
% 2.03/0.64    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 2.03/0.64  fof(f406,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X0,X1,k1_xboole_0)) )),
% 2.03/0.64    inference(resolution,[],[f216,f86])).
% 2.03/0.64  fof(f216,plain,(
% 2.03/0.64    ( ! [X4,X2,X3] : (~r1_tarski(X4,k2_zfmisc_1(X2,X3)) | k1_relset_1(X2,X3,X4) = k1_relat_1(X4)) )),
% 2.03/0.64    inference(resolution,[],[f127,f122])).
% 2.03/0.64  fof(f127,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f47])).
% 2.03/0.64  fof(f47,plain,(
% 2.03/0.64    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.64    inference(ennf_transformation,[],[f15])).
% 2.03/0.64  fof(f15,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.03/0.64  fof(f436,plain,(
% 2.03/0.64    ( ! [X4,X3] : (k1_relset_1(X3,X4,k1_xboole_0) = k8_relset_1(X3,X4,k1_xboole_0,X4)) )),
% 2.03/0.64    inference(resolution,[],[f426,f129])).
% 2.03/0.64  fof(f129,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f48])).
% 2.03/0.64  fof(f48,plain,(
% 2.03/0.64    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.03/0.64    inference(ennf_transformation,[],[f16])).
% 2.03/0.64  fof(f16,axiom,(
% 2.03/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 2.03/0.64  fof(f426,plain,(
% 2.03/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f425,f135])).
% 2.03/0.64  fof(f135,plain,(
% 2.03/0.64    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f88,f87])).
% 2.03/0.64  fof(f87,plain,(
% 2.03/0.64    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.03/0.64    inference(cnf_transformation,[],[f7])).
% 2.03/0.64  fof(f7,axiom,(
% 2.03/0.64    ! [X0] : k2_subset_1(X0) = X0),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.03/0.64  fof(f88,plain,(
% 2.03/0.64    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(cnf_transformation,[],[f8])).
% 2.03/0.64  fof(f8,axiom,(
% 2.03/0.64    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 2.03/0.64  fof(f425,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.03/0.64    inference(forward_demodulation,[],[f424,f133])).
% 2.03/0.64  fof(f424,plain,(
% 2.03/0.64    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.03/0.64    inference(superposition,[],[f130,f419])).
% 2.03/0.64  fof(f419,plain,(
% 2.03/0.64    ( ! [X0] : (k1_xboole_0 = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f415,f165])).
% 2.03/0.64  fof(f415,plain,(
% 2.03/0.64    ( ! [X0] : (k1_relat_1(k1_xboole_0) = k8_relset_1(X0,k1_xboole_0,k1_xboole_0,k1_xboole_0)) )),
% 2.03/0.64    inference(superposition,[],[f253,f133])).
% 2.03/0.64  fof(f253,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f247,f215])).
% 2.03/0.64  fof(f215,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1))) )),
% 2.03/0.64    inference(resolution,[],[f127,f135])).
% 2.03/0.64  fof(f247,plain,(
% 2.03/0.64    ( ! [X0,X1] : (k1_relset_1(X0,X1,k2_zfmisc_1(X0,X1)) = k8_relset_1(X0,X1,k2_zfmisc_1(X0,X1),X1)) )),
% 2.03/0.64    inference(resolution,[],[f129,f135])).
% 2.03/0.64  fof(f1989,plain,(
% 2.03/0.64    ~r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1988,f698])).
% 2.03/0.64  fof(f698,plain,(
% 2.03/0.64    ( ! [X2,X1] : (k8_relset_1(k2_struct_0(sK0),X1,k1_xboole_0,X2) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X1,k1_xboole_0,X2))) )),
% 2.03/0.64    inference(resolution,[],[f343,f456])).
% 2.03/0.64  fof(f456,plain,(
% 2.03/0.64    ( ! [X8,X7,X9] : (r1_tarski(k8_relset_1(X7,X8,k1_xboole_0,X9),X7)) )),
% 2.03/0.64    inference(resolution,[],[f222,f426])).
% 2.03/0.64  fof(f343,plain,(
% 2.03/0.64    ( ! [X0] : (~r1_tarski(X0,k2_struct_0(sK0)) | k2_pre_topc(sK0,X0) = X0) )),
% 2.03/0.64    inference(resolution,[],[f234,f122])).
% 2.03/0.64  fof(f234,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f233,f214])).
% 2.03/0.64  fof(f214,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.03/0.64    inference(forward_demodulation,[],[f213,f145])).
% 2.03/0.64  fof(f213,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f212,f78])).
% 2.03/0.64  fof(f212,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.03/0.64    inference(resolution,[],[f137,f77])).
% 2.03/0.64  fof(f137,plain,(
% 2.03/0.64    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.03/0.64    inference(subsumption_resolution,[],[f106,f91])).
% 2.03/0.64  fof(f106,plain,(
% 2.03/0.64    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f65])).
% 2.03/0.64  fof(f65,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f63,f64])).
% 2.03/0.64  fof(f64,plain,(
% 2.03/0.64    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f63,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(rectify,[],[f62])).
% 2.03/0.64  fof(f62,plain,(
% 2.03/0.64    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f41])).
% 2.03/0.64  fof(f41,plain,(
% 2.03/0.64    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f40])).
% 2.03/0.64  fof(f40,plain,(
% 2.03/0.64    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.03/0.64    inference(ennf_transformation,[],[f24])).
% 2.03/0.64  fof(f24,axiom,(
% 2.03/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_tdlat_3)).
% 2.03/0.64  fof(f233,plain,(
% 2.03/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 2.03/0.64    inference(forward_demodulation,[],[f231,f145])).
% 2.03/0.64  fof(f231,plain,(
% 2.03/0.64    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 2.03/0.64    inference(resolution,[],[f100,f78])).
% 2.03/0.64  fof(f100,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 2.03/0.64    inference(cnf_transformation,[],[f36])).
% 2.03/0.64  fof(f36,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f35])).
% 2.03/0.64  fof(f35,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.03/0.64    inference(ennf_transformation,[],[f19])).
% 2.03/0.64  fof(f19,axiom,(
% 2.03/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.03/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.03/0.64  fof(f1988,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1987,f145])).
% 2.03/0.64  fof(f1987,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1986,f1035])).
% 2.03/0.64  fof(f1986,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1985,f146])).
% 2.03/0.64  fof(f1985,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1984,f76])).
% 2.03/0.64  fof(f76,plain,(
% 2.03/0.64    v2_pre_topc(sK0)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f1984,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1983,f78])).
% 2.03/0.64  fof(f1983,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1982,f79])).
% 2.03/0.64  fof(f79,plain,(
% 2.03/0.64    v2_pre_topc(sK1)),
% 2.03/0.64    inference(cnf_transformation,[],[f53])).
% 2.03/0.64  fof(f1982,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1981,f80])).
% 2.03/0.64  fof(f1981,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1980,f1207])).
% 2.03/0.64  fof(f1207,plain,(
% 2.03/0.64    v1_funct_1(k1_xboole_0)),
% 2.03/0.64    inference(superposition,[],[f81,f1078])).
% 2.03/0.64  fof(f1980,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1979,f426])).
% 2.03/0.64  fof(f1979,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(subsumption_resolution,[],[f1977,f1210])).
% 2.03/0.64  fof(f1210,plain,(
% 2.03/0.64    ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.03/0.64    inference(superposition,[],[f84,f1078])).
% 2.03/0.64  fof(f1977,plain,(
% 2.03/0.64    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.03/0.64    inference(superposition,[],[f111,f1895])).
% 2.03/0.64  fof(f1895,plain,(
% 2.03/0.64    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)),
% 2.03/0.64    inference(resolution,[],[f1858,f102])).
% 2.03/0.64  fof(f1858,plain,(
% 2.03/0.64    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1857,f1078])).
% 2.03/0.64  fof(f1857,plain,(
% 2.03/0.64    r1_tarski(sK6(sK0,sK1,sK2),k1_xboole_0)),
% 2.03/0.64    inference(forward_demodulation,[],[f1856,f1035])).
% 2.03/0.64  fof(f1856,plain,(
% 2.03/0.64    r1_tarski(sK6(sK0,sK1,sK2),k2_struct_0(sK1))),
% 2.03/0.64    inference(forward_demodulation,[],[f1855,f146])).
% 2.03/0.64  fof(f1855,plain,(
% 2.03/0.64    r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1854,f76])).
% 2.03/0.64  fof(f1854,plain,(
% 2.03/0.64    ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1853,f78])).
% 2.03/0.64  fof(f1853,plain,(
% 2.03/0.64    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1852,f79])).
% 2.03/0.64  fof(f1852,plain,(
% 2.03/0.64    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1851,f80])).
% 2.03/0.64  fof(f1851,plain,(
% 2.03/0.64    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1850,f84])).
% 2.03/0.64  fof(f1850,plain,(
% 2.03/0.64    v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(subsumption_resolution,[],[f1843,f82])).
% 2.03/0.64  fof(f1843,plain,(
% 2.03/0.64    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.03/0.64    inference(resolution,[],[f661,f83])).
% 2.03/0.64  fof(f661,plain,(
% 2.03/0.64    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r1_tarski(sK6(X0,X1,sK2),u1_struct_0(X1))) )),
% 2.03/0.64    inference(resolution,[],[f291,f81])).
% 2.03/0.64  fof(f291,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | v5_pre_topc(X0,X1,X2) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | r1_tarski(sK6(X1,X2,X0),u1_struct_0(X2))) )),
% 2.03/0.64    inference(resolution,[],[f110,f121])).
% 2.03/0.64  fof(f110,plain,(
% 2.03/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.64    inference(cnf_transformation,[],[f69])).
% 2.03/0.64  fof(f69,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f67,f68])).
% 2.03/0.64  fof(f68,plain,(
% 2.03/0.64    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.03/0.64    introduced(choice_axiom,[])).
% 2.03/0.64  fof(f67,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(rectify,[],[f66])).
% 2.03/0.64  fof(f66,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(nnf_transformation,[],[f43])).
% 2.03/0.64  fof(f43,plain,(
% 2.03/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.03/0.64    inference(flattening,[],[f42])).
% 2.03/0.65  fof(f42,plain,(
% 2.03/0.65    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.03/0.65    inference(ennf_transformation,[],[f21])).
% 2.03/0.65  fof(f21,axiom,(
% 2.03/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 2.03/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_2)).
% 2.03/0.65  fof(f111,plain,(
% 2.03/0.65    ( ! [X2,X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.03/0.65    inference(cnf_transformation,[],[f69])).
% 2.03/0.65  % SZS output end Proof for theBenchmark
% 2.03/0.65  % (25709)------------------------------
% 2.03/0.65  % (25709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.03/0.65  % (25709)Termination reason: Refutation
% 2.03/0.65  
% 2.03/0.65  % (25709)Memory used [KB]: 2558
% 2.03/0.65  % (25709)Time elapsed: 0.207 s
% 2.03/0.65  % (25709)------------------------------
% 2.03/0.65  % (25709)------------------------------
% 2.03/0.65  % (25692)Success in time 0.275 s
%------------------------------------------------------------------------------
