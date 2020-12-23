%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:24 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  175 (2447 expanded)
%              Number of leaves         :   24 ( 829 expanded)
%              Depth                    :   39
%              Number of atoms          :  702 (16088 expanded)
%              Number of equality atoms :   81 ( 634 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3469,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3468,f2354])).

fof(f2354,plain,(
    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2353,f169])).

fof(f169,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f108,f161])).

fof(f161,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f110,f91])).

fof(f91,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & l1_pre_topc(sK0)
    & v1_tdlat_3(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f61,f60,f59])).

fof(f59,plain,
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

fof(f60,plain,
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

fof(f61,plain,
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f108,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f2353,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2352,f2125])).

fof(f2125,plain,(
    k1_xboole_0 = k2_struct_0(sK1) ),
    inference(resolution,[],[f1065,f1282])).

fof(f1282,plain,(
    ! [X2] : v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),sK0) ),
    inference(resolution,[],[f707,f480])).

fof(f480,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_struct_0(sK0))
      | v3_pre_topc(X3,sK0) ) ),
    inference(resolution,[],[f265,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f265,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f264,f169])).

fof(f264,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f263,f91])).

fof(f263,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f159,f90])).

fof(f90,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f159,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f122,f111])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | v2_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f122,plain,(
    ! [X2,X0] :
      ( v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f68,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK4(X0),X0)
        & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
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
    inference(rectify,[],[f67])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f707,plain,(
    ! [X2] : r1_tarski(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f706,f170])).

fof(f170,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f108,f162])).

fof(f162,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f110,f93])).

fof(f93,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f706,plain,(
    ! [X2] : r1_tarski(k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X2),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f696,f169])).

fof(f696,plain,(
    ! [X2] : r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f289,f96])).

fof(f96,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f62])).

fof(f289,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | r1_tarski(k8_relset_1(X6,X7,X5,X8),X6) ) ),
    inference(resolution,[],[f152,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).

fof(f1065,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f1064,f169])).

fof(f1064,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | k1_xboole_0 = k2_struct_0(sK1) ),
    inference(forward_demodulation,[],[f1063,f170])).

fof(f1063,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f1062,f91])).

fof(f1062,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1061,f93])).

fof(f1061,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1060,f97])).

fof(f97,plain,(
    ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f1060,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1053,f95])).

fof(f95,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f62])).

fof(f1053,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f364,f96])).

fof(f364,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0)
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f118,f94])).

fof(f94,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f62])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
      | k1_xboole_0 = k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f64,f65])).

fof(f65,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0)
        & v3_pre_topc(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f2352,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f2320,f170])).

fof(f2320,plain,(
    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(superposition,[],[f95,f2176])).

fof(f2176,plain,(
    k1_xboole_0 = sK2 ),
    inference(forward_demodulation,[],[f2175,f156])).

fof(f156,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2175,plain,(
    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f2174,f99])).

fof(f99,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2174,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2139,f156])).

fof(f2139,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0) ),
    inference(superposition,[],[f427,f2125])).

fof(f427,plain,
    ( ~ r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2)
    | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(resolution,[],[f182,f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f182,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f181,f169])).

fof(f181,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f179,f170])).

fof(f179,plain,(
    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[],[f96,f138])).

fof(f3468,plain,(
    ~ v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3467,f169])).

fof(f3467,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3466,f2125])).

fof(f3466,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3465,f170])).

fof(f3465,plain,(
    ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3464,f505])).

fof(f505,plain,(
    ! [X2] : r1_tarski(k1_relat_1(k1_xboole_0),X2) ),
    inference(resolution,[],[f501,f138])).

fof(f501,plain,(
    ! [X0] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(subsumption_resolution,[],[f499,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f499,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f152,f321])).

fof(f321,plain,(
    ! [X2,X1] : k1_relat_1(k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f311,f281])).

fof(f281,plain,(
    ! [X2,X1] : k1_relat_1(k1_xboole_0) = k1_relset_1(X1,X2,k1_xboole_0) ),
    inference(resolution,[],[f145,f101])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f311,plain,(
    ! [X2,X1] : k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2) ),
    inference(resolution,[],[f149,f101])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f3464,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3463,f321])).

fof(f3463,plain,
    ( ~ r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3462,f1212])).

fof(f1212,plain,(
    ! [X0,X1] : k8_relset_1(k2_struct_0(sK0),X0,k1_xboole_0,X1) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X0,k1_xboole_0,X1)) ),
    inference(resolution,[],[f537,f698])).

fof(f698,plain,(
    ! [X6,X8,X7] : r1_tarski(k8_relset_1(X6,X7,k1_xboole_0,X8),X6) ),
    inference(resolution,[],[f289,f101])).

fof(f537,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k2_struct_0(sK0))
      | k2_pre_topc(sK0,X3) = X3 ) ),
    inference(resolution,[],[f297,f139])).

fof(f297,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(subsumption_resolution,[],[f296,f268])).

fof(f268,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(forward_demodulation,[],[f267,f169])).

fof(f267,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f266,f91])).

fof(f266,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v4_pre_topc(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f160,f90])).

fof(f160,plain,(
    ! [X2,X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f125,f111])).

fof(f125,plain,(
    ! [X2,X0] :
      ( v4_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f72,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v4_pre_topc(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).

fof(f296,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(forward_demodulation,[],[f294,f169])).

fof(f294,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f120,f91])).

fof(f120,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f3462,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3461,f169])).

fof(f3461,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3460,f2125])).

fof(f3460,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3459,f170])).

fof(f3459,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3458,f89])).

fof(f89,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f62])).

fof(f3458,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3457,f91])).

fof(f3457,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3456,f92])).

fof(f92,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f62])).

fof(f3456,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3455,f93])).

fof(f3455,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3454,f2319])).

fof(f2319,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f94,f2176])).

fof(f3454,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3453,f101])).

fof(f3453,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f3451,f2322])).

fof(f2322,plain,(
    ~ v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    inference(superposition,[],[f97,f2176])).

fof(f3451,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0)))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(superposition,[],[f130,f3412])).

fof(f3412,plain,(
    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0) ),
    inference(resolution,[],[f3372,f195])).

fof(f195,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f137,f99])).

fof(f3372,plain,(
    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3371,f2176])).

fof(f3371,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),k1_xboole_0) ),
    inference(forward_demodulation,[],[f3370,f2125])).

fof(f3370,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),k2_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f3369,f170])).

fof(f3369,plain,(
    r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3368,f89])).

fof(f3368,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3367,f91])).

fof(f3367,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3366,f92])).

fof(f3366,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3365,f93])).

fof(f3365,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3364,f97])).

fof(f3364,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f3356,f95])).

fof(f3356,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    inference(resolution,[],[f1044,f96])).

fof(f1044,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
      | v5_pre_topc(sK2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(sK6(X0,X1,sK2),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f353,f94])).

fof(f353,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6))))
      | ~ v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6))
      | v5_pre_topc(X4,X5,X6)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | r1_tarski(sK6(X5,X6,X4),u1_struct_0(X6)) ) ),
    inference(resolution,[],[f129,f138])).

fof(f129,plain,(
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
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2))))
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
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
    inference(rectify,[],[f75])).

fof(f75,plain,(
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
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).

fof(f130,plain,(
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
    inference(cnf_transformation,[],[f78])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:18:41 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.23/0.46  % (3958)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.47  % (3957)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.23/0.48  % (3974)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.23/0.49  % (3966)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.23/0.49  % (3966)Refutation not found, incomplete strategy% (3966)------------------------------
% 0.23/0.49  % (3966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (3966)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (3966)Memory used [KB]: 6140
% 0.23/0.49  % (3966)Time elapsed: 0.094 s
% 0.23/0.49  % (3966)------------------------------
% 0.23/0.49  % (3966)------------------------------
% 0.23/0.50  % (3958)Refutation not found, incomplete strategy% (3958)------------------------------
% 0.23/0.50  % (3958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (3958)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (3958)Memory used [KB]: 6524
% 0.23/0.50  % (3958)Time elapsed: 0.085 s
% 0.23/0.50  % (3958)------------------------------
% 0.23/0.50  % (3958)------------------------------
% 0.23/0.51  % (3959)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.23/0.51  % (3976)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.23/0.51  % (3968)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.23/0.51  % (3965)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.23/0.52  % (3953)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.23/0.52  % (3962)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.23/0.52  % (3975)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.52  % (3961)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.27/0.52  % (3956)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.27/0.53  % (3954)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.53  % (3959)Refutation not found, incomplete strategy% (3959)------------------------------
% 1.27/0.53  % (3959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (3959)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (3959)Memory used [KB]: 10618
% 1.27/0.53  % (3959)Time elapsed: 0.105 s
% 1.27/0.53  % (3959)------------------------------
% 1.27/0.53  % (3959)------------------------------
% 1.27/0.53  % (3977)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.27/0.53  % (3967)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.27/0.53  % (3955)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.27/0.53  % (3972)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.27/0.53  % (3960)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.27/0.54  % (3969)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.27/0.54  % (3953)Refutation not found, incomplete strategy% (3953)------------------------------
% 1.27/0.54  % (3953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (3953)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (3953)Memory used [KB]: 10490
% 1.27/0.54  % (3953)Time elapsed: 0.003 s
% 1.27/0.54  % (3953)------------------------------
% 1.27/0.54  % (3953)------------------------------
% 1.27/0.54  % (3964)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.54  % (3964)Refutation not found, incomplete strategy% (3964)------------------------------
% 1.27/0.54  % (3964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.54  % (3964)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.54  
% 1.27/0.54  % (3964)Memory used [KB]: 10490
% 1.27/0.54  % (3964)Time elapsed: 0.001 s
% 1.27/0.54  % (3964)------------------------------
% 1.27/0.54  % (3964)------------------------------
% 1.45/0.54  % (3973)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.45/0.54  % (3963)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.45/0.55  % (3971)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.45/0.56  % (3979)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.45/0.56  % (3970)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.45/0.63  % (3962)Refutation not found, incomplete strategy% (3962)------------------------------
% 1.45/0.63  % (3962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.63  % (3962)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.63  
% 1.45/0.63  % (3962)Memory used [KB]: 6140
% 1.45/0.63  % (3962)Time elapsed: 0.204 s
% 1.45/0.63  % (3962)------------------------------
% 1.45/0.63  % (3962)------------------------------
% 2.12/0.67  % (3969)Refutation found. Thanks to Tanya!
% 2.12/0.67  % SZS status Theorem for theBenchmark
% 2.56/0.69  % SZS output start Proof for theBenchmark
% 2.56/0.69  fof(f3469,plain,(
% 2.56/0.69    $false),
% 2.56/0.69    inference(subsumption_resolution,[],[f3468,f2354])).
% 2.56/0.69  fof(f2354,plain,(
% 2.56/0.69    v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(forward_demodulation,[],[f2353,f169])).
% 2.56/0.69  fof(f169,plain,(
% 2.56/0.69    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.56/0.69    inference(resolution,[],[f108,f161])).
% 2.56/0.69  fof(f161,plain,(
% 2.56/0.69    l1_struct_0(sK0)),
% 2.56/0.69    inference(resolution,[],[f110,f91])).
% 2.56/0.69  fof(f91,plain,(
% 2.56/0.69    l1_pre_topc(sK0)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f62,plain,(
% 2.56/0.69    ((~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0)),
% 2.56/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f32,f61,f60,f59])).
% 2.56/0.69  fof(f59,plain,(
% 2.56/0.69    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK0) & v1_tdlat_3(sK0) & v2_pre_topc(sK0))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f60,plain,(
% 2.56/0.69    ? [X1] : (? [X2] : (~v5_pre_topc(X2,sK0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f61,plain,(
% 2.56/0.69    ? [X2] : (~v5_pre_topc(X2,sK0,sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~v5_pre_topc(sK2,sK0,sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f32,plain,(
% 2.56/0.69    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f31])).
% 2.56/0.69  fof(f31,plain,(
% 2.56/0.69    ? [X0] : (? [X1] : (? [X2] : (~v5_pre_topc(X2,X0,X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)))),
% 2.56/0.69    inference(ennf_transformation,[],[f30])).
% 2.56/0.69  fof(f30,negated_conjecture,(
% 2.56/0.69    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.56/0.69    inference(negated_conjecture,[],[f29])).
% 2.56/0.69  fof(f29,conjecture,(
% 2.56/0.69    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => v5_pre_topc(X2,X0,X1))))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_tex_2)).
% 2.56/0.69  fof(f110,plain,(
% 2.56/0.69    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f35])).
% 2.56/0.69  fof(f35,plain,(
% 2.56/0.69    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(ennf_transformation,[],[f21])).
% 2.56/0.69  fof(f21,axiom,(
% 2.56/0.69    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.56/0.69  fof(f108,plain,(
% 2.56/0.69    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f33])).
% 2.56/0.69  fof(f33,plain,(
% 2.56/0.69    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.56/0.69    inference(ennf_transformation,[],[f20])).
% 2.56/0.69  fof(f20,axiom,(
% 2.56/0.69    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.56/0.69  fof(f2353,plain,(
% 2.56/0.69    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(forward_demodulation,[],[f2352,f2125])).
% 2.56/0.69  fof(f2125,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1)),
% 2.56/0.69    inference(resolution,[],[f1065,f1282])).
% 2.56/0.69  fof(f1282,plain,(
% 2.56/0.69    ( ! [X2] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),sK0)) )),
% 2.56/0.69    inference(resolution,[],[f707,f480])).
% 2.56/0.69  fof(f480,plain,(
% 2.56/0.69    ( ! [X3] : (~r1_tarski(X3,k2_struct_0(sK0)) | v3_pre_topc(X3,sK0)) )),
% 2.56/0.69    inference(resolution,[],[f265,f139])).
% 2.56/0.69  fof(f139,plain,(
% 2.56/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f86])).
% 2.56/0.69  fof(f86,plain,(
% 2.56/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.56/0.69    inference(nnf_transformation,[],[f11])).
% 2.56/0.69  fof(f11,axiom,(
% 2.56/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.56/0.69  fof(f265,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 2.56/0.69    inference(forward_demodulation,[],[f264,f169])).
% 2.56/0.69  fof(f264,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f263,f91])).
% 2.56/0.69  fof(f263,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.56/0.69    inference(resolution,[],[f159,f90])).
% 2.56/0.69  fof(f90,plain,(
% 2.56/0.69    v1_tdlat_3(sK0)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f159,plain,(
% 2.56/0.69    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f122,f111])).
% 2.56/0.69  fof(f111,plain,(
% 2.56/0.69    ( ! [X0] : (~v1_tdlat_3(X0) | v2_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f37])).
% 2.56/0.69  fof(f37,plain,(
% 2.56/0.69    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f36])).
% 2.56/0.69  fof(f36,plain,(
% 2.56/0.69    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(ennf_transformation,[],[f26])).
% 2.56/0.69  fof(f26,axiom,(
% 2.56/0.69    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 2.56/0.69  fof(f122,plain,(
% 2.56/0.69    ( ! [X2,X0] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f70])).
% 2.56/0.69  fof(f70,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f68,f69])).
% 2.56/0.69  fof(f69,plain,(
% 2.56/0.69    ! [X0] : (? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_pre_topc(sK4(X0),X0) & m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f68,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(rectify,[],[f67])).
% 2.56/0.69  fof(f67,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(nnf_transformation,[],[f43])).
% 2.56/0.69  fof(f43,plain,(
% 2.56/0.69    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f42])).
% 2.56/0.69  fof(f42,plain,(
% 2.56/0.69    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.56/0.69    inference(ennf_transformation,[],[f27])).
% 2.56/0.69  fof(f27,axiom,(
% 2.56/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 2.56/0.69  fof(f707,plain,(
% 2.56/0.69    ( ! [X2] : (r1_tarski(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X2),k2_struct_0(sK0))) )),
% 2.56/0.69    inference(forward_demodulation,[],[f706,f170])).
% 2.56/0.69  fof(f170,plain,(
% 2.56/0.69    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 2.56/0.69    inference(resolution,[],[f108,f162])).
% 2.56/0.69  fof(f162,plain,(
% 2.56/0.69    l1_struct_0(sK1)),
% 2.56/0.69    inference(resolution,[],[f110,f93])).
% 2.56/0.69  fof(f93,plain,(
% 2.56/0.69    l1_pre_topc(sK1)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f706,plain,(
% 2.56/0.69    ( ! [X2] : (r1_tarski(k8_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2,X2),k2_struct_0(sK0))) )),
% 2.56/0.69    inference(forward_demodulation,[],[f696,f169])).
% 2.56/0.69  fof(f696,plain,(
% 2.56/0.69    ( ! [X2] : (r1_tarski(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X2),u1_struct_0(sK0))) )),
% 2.56/0.69    inference(resolution,[],[f289,f96])).
% 2.56/0.69  fof(f96,plain,(
% 2.56/0.69    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f289,plain,(
% 2.56/0.69    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | r1_tarski(k8_relset_1(X6,X7,X5,X8),X6)) )),
% 2.56/0.69    inference(resolution,[],[f152,f138])).
% 2.56/0.69  fof(f138,plain,(
% 2.56/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f86])).
% 2.56/0.69  fof(f152,plain,(
% 2.56/0.69    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.69    inference(cnf_transformation,[],[f58])).
% 2.56/0.69  fof(f58,plain,(
% 2.56/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.69    inference(ennf_transformation,[],[f16])).
% 2.56/0.69  fof(f16,axiom,(
% 2.56/0.69    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relset_1)).
% 2.56/0.69  fof(f1065,plain,(
% 2.56/0.69    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | k1_xboole_0 = k2_struct_0(sK1)),
% 2.56/0.69    inference(forward_demodulation,[],[f1064,f169])).
% 2.56/0.69  fof(f1064,plain,(
% 2.56/0.69    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | k1_xboole_0 = k2_struct_0(sK1)),
% 2.56/0.69    inference(forward_demodulation,[],[f1063,f170])).
% 2.56/0.69  fof(f1063,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f1062,f91])).
% 2.56/0.69  fof(f1062,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f1061,f93])).
% 2.56/0.69  fof(f1061,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f1060,f97])).
% 2.56/0.69  fof(f97,plain,(
% 2.56/0.69    ~v5_pre_topc(sK2,sK0,sK1)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f1060,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f1053,f95])).
% 2.56/0.69  fof(f95,plain,(
% 2.56/0.69    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f1053,plain,(
% 2.56/0.69    k1_xboole_0 = k2_struct_0(sK1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3(sK0,sK1,sK2)),sK0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 2.56/0.69    inference(resolution,[],[f364,f96])).
% 2.56/0.69  fof(f364,plain,(
% 2.56/0.69    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_xboole_0 = k2_struct_0(X1) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2,sK3(X0,X1,sK2)),X0) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.56/0.69    inference(resolution,[],[f118,f94])).
% 2.56/0.69  fof(f94,plain,(
% 2.56/0.69    v1_funct_1(sK2)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f118,plain,(
% 2.56/0.69    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) | k1_xboole_0 = k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f66])).
% 2.56/0.69  fof(f66,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f64,f65])).
% 2.56/0.69  fof(f65,plain,(
% 2.56/0.69    ! [X2,X1,X0] : (? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK3(X0,X1,X2)),X0) & v3_pre_topc(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f64,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0) | ~v3_pre_topc(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(rectify,[],[f63])).
% 2.56/0.69  fof(f63,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) & v3_pre_topc(X3,X1) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(nnf_transformation,[],[f39])).
% 2.56/0.69  fof(f39,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f38])).
% 2.56/0.69  fof(f38,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k1_xboole_0 != k2_struct_0(X0) & k1_xboole_0 = k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(ennf_transformation,[],[f23])).
% 2.56/0.69  fof(f23,axiom,(
% 2.56/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.56/0.69  fof(f2352,plain,(
% 2.56/0.69    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f2320,f170])).
% 2.56/0.69  fof(f2320,plain,(
% 2.56/0.69    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(superposition,[],[f95,f2176])).
% 2.56/0.69  fof(f2176,plain,(
% 2.56/0.69    k1_xboole_0 = sK2),
% 2.56/0.69    inference(forward_demodulation,[],[f2175,f156])).
% 2.56/0.69  fof(f156,plain,(
% 2.56/0.69    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.56/0.69    inference(equality_resolution,[],[f142])).
% 2.56/0.69  fof(f142,plain,(
% 2.56/0.69    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.56/0.69    inference(cnf_transformation,[],[f88])).
% 2.56/0.69  fof(f88,plain,(
% 2.56/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.56/0.69    inference(flattening,[],[f87])).
% 2.56/0.69  fof(f87,plain,(
% 2.56/0.69    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.56/0.69    inference(nnf_transformation,[],[f7])).
% 2.56/0.69  fof(f7,axiom,(
% 2.56/0.69    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 2.56/0.69  fof(f2175,plain,(
% 2.56/0.69    sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f2174,f99])).
% 2.56/0.69  fof(f99,plain,(
% 2.56/0.69    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f5])).
% 2.56/0.69  fof(f5,axiom,(
% 2.56/0.69    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.56/0.69  fof(f2174,plain,(
% 2.56/0.69    ~r1_tarski(k1_xboole_0,sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(forward_demodulation,[],[f2139,f156])).
% 2.56/0.69  fof(f2139,plain,(
% 2.56/0.69    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0),sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(superposition,[],[f427,f2125])).
% 2.56/0.69  fof(f427,plain,(
% 2.56/0.69    ~r1_tarski(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)),sK2) | sK2 = k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),
% 2.56/0.69    inference(resolution,[],[f182,f137])).
% 2.56/0.69  fof(f137,plain,(
% 2.56/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f85])).
% 2.56/0.69  fof(f85,plain,(
% 2.56/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/0.69    inference(flattening,[],[f84])).
% 2.56/0.69  fof(f84,plain,(
% 2.56/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.56/0.69    inference(nnf_transformation,[],[f4])).
% 2.56/0.69  fof(f4,axiom,(
% 2.56/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.56/0.69  fof(f182,plain,(
% 2.56/0.69    r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 2.56/0.69    inference(forward_demodulation,[],[f181,f169])).
% 2.56/0.69  fof(f181,plain,(
% 2.56/0.69    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))),
% 2.56/0.69    inference(forward_demodulation,[],[f179,f170])).
% 2.56/0.69  fof(f179,plain,(
% 2.56/0.69    r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))),
% 2.56/0.69    inference(resolution,[],[f96,f138])).
% 2.56/0.69  fof(f3468,plain,(
% 2.56/0.69    ~v1_funct_2(k1_xboole_0,k2_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(forward_demodulation,[],[f3467,f169])).
% 2.56/0.69  fof(f3467,plain,(
% 2.56/0.69    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 2.56/0.69    inference(forward_demodulation,[],[f3466,f2125])).
% 2.56/0.69  fof(f3466,plain,(
% 2.56/0.69    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k2_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3465,f170])).
% 2.56/0.69  fof(f3465,plain,(
% 2.56/0.69    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(subsumption_resolution,[],[f3464,f505])).
% 2.56/0.69  fof(f505,plain,(
% 2.56/0.69    ( ! [X2] : (r1_tarski(k1_relat_1(k1_xboole_0),X2)) )),
% 2.56/0.69    inference(resolution,[],[f501,f138])).
% 2.56/0.69  fof(f501,plain,(
% 2.56/0.69    ( ! [X0] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0))) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f499,f101])).
% 2.56/0.69  fof(f101,plain,(
% 2.56/0.69    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.56/0.69    inference(cnf_transformation,[],[f10])).
% 2.56/0.69  fof(f10,axiom,(
% 2.56/0.69    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 2.56/0.69  fof(f499,plain,(
% 2.56/0.69    ( ! [X0,X1] : (m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.69    inference(superposition,[],[f152,f321])).
% 2.56/0.69  fof(f321,plain,(
% 2.56/0.69    ( ! [X2,X1] : (k1_relat_1(k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2)) )),
% 2.56/0.69    inference(forward_demodulation,[],[f311,f281])).
% 2.56/0.69  fof(f281,plain,(
% 2.56/0.69    ( ! [X2,X1] : (k1_relat_1(k1_xboole_0) = k1_relset_1(X1,X2,k1_xboole_0)) )),
% 2.56/0.69    inference(resolution,[],[f145,f101])).
% 2.56/0.69  fof(f145,plain,(
% 2.56/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f52])).
% 2.56/0.69  fof(f52,plain,(
% 2.56/0.69    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.69    inference(ennf_transformation,[],[f17])).
% 2.56/0.69  fof(f17,axiom,(
% 2.56/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.56/0.69  fof(f311,plain,(
% 2.56/0.69    ( ! [X2,X1] : (k1_relset_1(X1,X2,k1_xboole_0) = k8_relset_1(X1,X2,k1_xboole_0,X2)) )),
% 2.56/0.69    inference(resolution,[],[f149,f101])).
% 2.56/0.69  fof(f149,plain,(
% 2.56/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f54])).
% 2.56/0.69  fof(f54,plain,(
% 2.56/0.69    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.69    inference(ennf_transformation,[],[f18])).
% 2.56/0.69  fof(f18,axiom,(
% 2.56/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 2.56/0.69  fof(f3464,plain,(
% 2.56/0.69    ~r1_tarski(k1_relat_1(k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3463,f321])).
% 2.56/0.69  fof(f3463,plain,(
% 2.56/0.69    ~r1_tarski(k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3462,f1212])).
% 2.56/0.69  fof(f1212,plain,(
% 2.56/0.69    ( ! [X0,X1] : (k8_relset_1(k2_struct_0(sK0),X0,k1_xboole_0,X1) = k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),X0,k1_xboole_0,X1))) )),
% 2.56/0.69    inference(resolution,[],[f537,f698])).
% 2.56/0.69  fof(f698,plain,(
% 2.56/0.69    ( ! [X6,X8,X7] : (r1_tarski(k8_relset_1(X6,X7,k1_xboole_0,X8),X6)) )),
% 2.56/0.69    inference(resolution,[],[f289,f101])).
% 2.56/0.69  fof(f537,plain,(
% 2.56/0.69    ( ! [X3] : (~r1_tarski(X3,k2_struct_0(sK0)) | k2_pre_topc(sK0,X3) = X3) )),
% 2.56/0.69    inference(resolution,[],[f297,f139])).
% 2.56/0.69  fof(f297,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f296,f268])).
% 2.56/0.69  fof(f268,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.56/0.69    inference(forward_demodulation,[],[f267,f169])).
% 2.56/0.69  fof(f267,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f266,f91])).
% 2.56/0.69  fof(f266,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 2.56/0.69    inference(resolution,[],[f160,f90])).
% 2.56/0.69  fof(f160,plain,(
% 2.56/0.69    ( ! [X2,X0] : (~v1_tdlat_3(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X2,X0) | ~l1_pre_topc(X0)) )),
% 2.56/0.69    inference(subsumption_resolution,[],[f125,f111])).
% 2.56/0.69  fof(f125,plain,(
% 2.56/0.69    ( ! [X2,X0] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/0.69    inference(cnf_transformation,[],[f74])).
% 2.56/0.69  fof(f74,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f72,f73])).
% 2.56/0.69  fof(f73,plain,(
% 2.56/0.69    ! [X0] : (? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v4_pre_topc(sK5(X0),X0) & m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.56/0.69    introduced(choice_axiom,[])).
% 2.56/0.69  fof(f72,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v4_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(rectify,[],[f71])).
% 2.56/0.69  fof(f71,plain,(
% 2.56/0.69    ! [X0] : (((v1_tdlat_3(X0) | ? [X1] : (~v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(nnf_transformation,[],[f45])).
% 2.56/0.69  fof(f45,plain,(
% 2.56/0.69    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f44])).
% 2.56/0.69  fof(f44,plain,(
% 2.56/0.69    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.56/0.69    inference(ennf_transformation,[],[f28])).
% 2.56/0.69  fof(f28,axiom,(
% 2.56/0.69    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v4_pre_topc(X1,X0))))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_tdlat_3)).
% 2.56/0.69  fof(f296,plain,(
% 2.56/0.69    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 2.56/0.69    inference(forward_demodulation,[],[f294,f169])).
% 2.56/0.69  fof(f294,plain,(
% 2.56/0.69    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) )),
% 2.56/0.69    inference(resolution,[],[f120,f91])).
% 2.56/0.69  fof(f120,plain,(
% 2.56/0.69    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 2.56/0.69    inference(cnf_transformation,[],[f41])).
% 2.56/0.69  fof(f41,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(flattening,[],[f40])).
% 2.56/0.69  fof(f40,plain,(
% 2.56/0.69    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.56/0.69    inference(ennf_transformation,[],[f22])).
% 2.56/0.69  fof(f22,axiom,(
% 2.56/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 2.56/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 2.56/0.69  fof(f3462,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3461,f169])).
% 2.56/0.69  fof(f3461,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3460,f2125])).
% 2.56/0.69  fof(f3460,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(forward_demodulation,[],[f3459,f170])).
% 2.56/0.69  fof(f3459,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.69    inference(subsumption_resolution,[],[f3458,f89])).
% 2.56/0.69  fof(f89,plain,(
% 2.56/0.69    v2_pre_topc(sK0)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f3458,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3457,f91])).
% 2.56/0.69  fof(f3457,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3456,f92])).
% 2.56/0.69  fof(f92,plain,(
% 2.56/0.69    v2_pre_topc(sK1)),
% 2.56/0.69    inference(cnf_transformation,[],[f62])).
% 2.56/0.69  fof(f3456,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3455,f93])).
% 2.56/0.69  fof(f3455,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3454,f2319])).
% 2.56/0.69  fof(f2319,plain,(
% 2.56/0.69    v1_funct_1(k1_xboole_0)),
% 2.56/0.69    inference(superposition,[],[f94,f2176])).
% 2.56/0.69  fof(f3454,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3453,f101])).
% 2.56/0.69  fof(f3453,plain,(
% 2.56/0.69    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.69    inference(subsumption_resolution,[],[f3451,f2322])).
% 2.56/0.70  fof(f2322,plain,(
% 2.56/0.70    ~v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 2.56/0.70    inference(superposition,[],[f97,f2176])).
% 2.56/0.70  fof(f3451,plain,(
% 2.56/0.70    ~r1_tarski(k2_pre_topc(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k1_xboole_0)),k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),k1_xboole_0,k2_pre_topc(sK1,k1_xboole_0))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 2.56/0.70    inference(superposition,[],[f130,f3412])).
% 2.56/0.70  fof(f3412,plain,(
% 2.56/0.70    k1_xboole_0 = sK6(sK0,sK1,k1_xboole_0)),
% 2.56/0.70    inference(resolution,[],[f3372,f195])).
% 2.56/0.70  fof(f195,plain,(
% 2.56/0.70    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.56/0.70    inference(resolution,[],[f137,f99])).
% 2.56/0.70  fof(f3372,plain,(
% 2.56/0.70    r1_tarski(sK6(sK0,sK1,k1_xboole_0),k1_xboole_0)),
% 2.56/0.70    inference(forward_demodulation,[],[f3371,f2176])).
% 2.56/0.70  fof(f3371,plain,(
% 2.56/0.70    r1_tarski(sK6(sK0,sK1,sK2),k1_xboole_0)),
% 2.56/0.70    inference(forward_demodulation,[],[f3370,f2125])).
% 2.56/0.70  fof(f3370,plain,(
% 2.56/0.70    r1_tarski(sK6(sK0,sK1,sK2),k2_struct_0(sK1))),
% 2.56/0.70    inference(forward_demodulation,[],[f3369,f170])).
% 2.56/0.70  fof(f3369,plain,(
% 2.56/0.70    r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3368,f89])).
% 2.56/0.70  fof(f3368,plain,(
% 2.56/0.70    ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3367,f91])).
% 2.56/0.70  fof(f3367,plain,(
% 2.56/0.70    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3366,f92])).
% 2.56/0.70  fof(f3366,plain,(
% 2.56/0.70    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3365,f93])).
% 2.56/0.70  fof(f3365,plain,(
% 2.56/0.70    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3364,f97])).
% 2.56/0.70  fof(f3364,plain,(
% 2.56/0.70    v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(subsumption_resolution,[],[f3356,f95])).
% 2.56/0.70  fof(f3356,plain,(
% 2.56/0.70    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | v5_pre_topc(sK2,sK0,sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK6(sK0,sK1,sK2),u1_struct_0(sK1))),
% 2.56/0.70    inference(resolution,[],[f1044,f96])).
% 2.56/0.70  fof(f1044,plain,(
% 2.56/0.70    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | v5_pre_topc(sK2,X0,X1) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r1_tarski(sK6(X0,X1,sK2),u1_struct_0(X1))) )),
% 2.56/0.70    inference(resolution,[],[f353,f94])).
% 2.56/0.70  fof(f353,plain,(
% 2.56/0.70    ( ! [X6,X4,X5] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X5),u1_struct_0(X6)))) | ~v1_funct_2(X4,u1_struct_0(X5),u1_struct_0(X6)) | v5_pre_topc(X4,X5,X6) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | r1_tarski(sK6(X5,X6,X4),u1_struct_0(X6))) )),
% 2.56/0.70    inference(resolution,[],[f129,f138])).
% 2.56/0.70  fof(f129,plain,(
% 2.56/0.70    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/0.70    inference(cnf_transformation,[],[f78])).
% 2.56/0.70  fof(f78,plain,(
% 2.56/0.70    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f76,f77])).
% 2.56/0.70  fof(f77,plain,(
% 2.56/0.70    ! [X2,X1,X0] : (? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 2.56/0.70    introduced(choice_axiom,[])).
% 2.56/0.70  fof(f76,plain,(
% 2.56/0.70    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.70    inference(rectify,[],[f75])).
% 2.56/0.70  fof(f75,plain,(
% 2.56/0.70    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) | ? [X3] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v5_pre_topc(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.70    inference(nnf_transformation,[],[f47])).
% 2.56/0.70  fof(f47,plain,(
% 2.56/0.70    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.56/0.70    inference(flattening,[],[f46])).
% 2.56/0.70  fof(f46,plain,(
% 2.56/0.70    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.56/0.70    inference(ennf_transformation,[],[f24])).
% 2.56/0.70  fof(f24,axiom,(
% 2.56/0.70    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3))))))))),
% 2.56/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_2)).
% 2.56/0.70  fof(f130,plain,(
% 2.56/0.70    ( ! [X2,X0,X1] : (~r1_tarski(k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2))),k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK6(X0,X1,X2)))) | v5_pre_topc(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.56/0.70    inference(cnf_transformation,[],[f78])).
% 2.56/0.70  % SZS output end Proof for theBenchmark
% 2.56/0.70  % (3969)------------------------------
% 2.56/0.70  % (3969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.56/0.70  % (3969)Termination reason: Refutation
% 2.56/0.70  
% 2.56/0.70  % (3969)Memory used [KB]: 3070
% 2.56/0.70  % (3969)Time elapsed: 0.263 s
% 2.56/0.70  % (3969)------------------------------
% 2.56/0.70  % (3969)------------------------------
% 2.56/0.70  % (3952)Success in time 0.331 s
%------------------------------------------------------------------------------
