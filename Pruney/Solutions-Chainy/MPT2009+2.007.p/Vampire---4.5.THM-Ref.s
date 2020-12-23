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
% DateTime   : Thu Dec  3 13:23:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 319 expanded)
%              Number of leaves         :   10 (  58 expanded)
%              Depth                    :   52
%              Number of atoms          :  518 (1443 expanded)
%              Number of equality atoms :   19 (  19 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(subsumption_resolution,[],[f313,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).

fof(f313,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f312,f33])).

fof(f33,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f312,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f311,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f311,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f310,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f310,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f309,f59])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f58,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f58,plain,(
    l1_orders_2(sK1) ),
    inference(subsumption_resolution,[],[f55,f33])).

fof(f55,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f309,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f308,f44])).

fof(f308,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f307,f33])).

fof(f307,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f306,f30])).

fof(f306,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f305,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).

fof(f305,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f304,f59])).

fof(f304,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[],[f303,f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_waybel_0(sK2(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] :
          ( v7_waybel_0(X1)
          & v6_waybel_0(X1,X0)
          & v5_orders_2(X1)
          & v4_orders_2(X1)
          & v3_orders_2(X1)
          & ~ v2_struct_0(X1)
          & l1_waybel_0(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_waybel_0)).

fof(f303,plain,
    ( ~ l1_waybel_0(sK2(sK1),sK1)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f302,f29])).

fof(f302,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ l1_waybel_0(sK2(sK1),sK1)
    | v2_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f301,f59])).

fof(f301,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ l1_struct_0(sK1)
    | ~ l1_waybel_0(sK2(sK1),sK1)
    | v2_struct_0(sK1) ),
    inference(resolution,[],[f300,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).

fof(f300,plain,
    ( ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f299,f33])).

fof(f299,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f298,f30])).

fof(f298,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f297,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f297,plain,
    ( ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f296,f33])).

fof(f296,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f295,f30])).

fof(f295,plain,
    ( ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f294,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f294,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f293,f31])).

fof(f31,plain,(
    ~ r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f293,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f292,f32])).

fof(f292,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f291,f30])).

fof(f291,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f290,f29])).

fof(f290,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f289,f33])).

fof(f289,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(resolution,[],[f287,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).

fof(f287,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f286,f31])).

fof(f286,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f285,f32])).

fof(f285,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f284,f30])).

fof(f284,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f283,f29])).

fof(f283,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f282,f33])).

fof(f282,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) ),
    inference(resolution,[],[f135,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f135,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(superposition,[],[f34,f129])).

fof(f129,plain,(
    k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) ),
    inference(resolution,[],[f128,f31])).

fof(f128,plain,(
    ! [X0] :
      ( r1_waybel_0(sK0,sK1,X0)
      | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) ) ),
    inference(subsumption_resolution,[],[f127,f33])).

fof(f127,plain,(
    ! [X0] :
      ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1))))
      | ~ l1_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f126,f32])).

fof(f126,plain,(
    ! [X0] :
      ( k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1))))
      | v2_struct_0(sK0)
      | ~ l1_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f123,f30])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X0)
      | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1))))
      | v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f122,f29])).

fof(f122,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1))))
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | r1_waybel_0(sK0,sK1,X1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f121,f59])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1))))
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | r1_waybel_0(sK0,sK1,X1)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f120,f32])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1))))
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X1)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(subsumption_resolution,[],[f117,f33])).

fof(f117,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1))))
      | ~ l1_struct_0(sK0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X1)
      | ~ l1_struct_0(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f114,f30])).

fof(f114,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ l1_waybel_0(X3,X5)
      | v2_struct_0(X4)
      | k2_waybel_0(X4,X3,sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),u1_waybel_0(X4,X3),sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3))))
      | ~ l1_struct_0(X5)
      | ~ l1_waybel_0(X3,X4)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X5)
      | r1_waybel_0(X5,X3,X6)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X6,X4,X5,X3] :
      ( ~ l1_waybel_0(X3,X4)
      | v2_struct_0(X4)
      | k2_waybel_0(X4,X3,sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),u1_waybel_0(X4,X3),sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3))))
      | ~ l1_struct_0(X5)
      | ~ l1_waybel_0(X3,X5)
      | ~ l1_struct_0(X4)
      | v2_struct_0(X5)
      | r1_waybel_0(X5,X3,X6)
      | ~ l1_struct_0(X3)
      | v2_struct_0(X3)
      | ~ l1_struct_0(X3) ) ),
    inference(resolution,[],[f106,f37])).

fof(f106,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X4,X0)
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X1)
      | k2_waybel_0(X1,X0,sK4(X2,X0,X3,k4_yellow_6(X0,X4))) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),sK4(X2,X0,X3,k4_yellow_6(X0,X4)))
      | ~ l1_struct_0(X2)
      | ~ l1_waybel_0(X0,X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | r1_waybel_0(X2,X0,X3)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_waybel_0(X0,X1)
      | v2_struct_0(X1)
      | k2_waybel_0(X1,X0,sK4(X2,X0,X3,k4_yellow_6(X0,X4))) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),sK4(X2,X0,X3,k4_yellow_6(X0,X4)))
      | ~ l1_struct_0(X2)
      | ~ l1_waybel_0(X0,X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X2)
      | r1_waybel_0(X2,X0,X3)
      | ~ l1_struct_0(X0)
      | ~ l1_waybel_0(X4,X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f64,f51])).

fof(f64,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ m1_subset_1(X11,u1_struct_0(X8))
      | v2_struct_0(X8)
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X7)
      | k2_waybel_0(X7,X8,sK4(X9,X8,X10,X11)) = k3_funct_2(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),sK4(X9,X8,X10,X11))
      | ~ l1_struct_0(X9)
      | ~ l1_waybel_0(X8,X9)
      | ~ l1_struct_0(X7)
      | v2_struct_0(X9)
      | r1_waybel_0(X9,X8,X10) ) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X10,X8,X7,X11,X9] :
      ( ~ l1_struct_0(X7)
      | v2_struct_0(X8)
      | ~ l1_waybel_0(X8,X7)
      | v2_struct_0(X7)
      | k2_waybel_0(X7,X8,sK4(X9,X8,X10,X11)) = k3_funct_2(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),sK4(X9,X8,X10,X11))
      | ~ l1_struct_0(X9)
      | v2_struct_0(X8)
      | ~ l1_waybel_0(X8,X9)
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | v2_struct_0(X9)
      | r1_waybel_0(X9,X8,X10) ) ),
    inference(resolution,[],[f45,f46])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X0)
      | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X0)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_2(X3,X0,X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,X0) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( m1_subset_1(X2,X0)
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X3,X0,X1)
                    & v1_funct_1(X3) )
                 => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:22:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (20266)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.46  % (20266)Refutation not found, incomplete strategy% (20266)------------------------------
% 0.21/0.46  % (20266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (20266)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.46  
% 0.21/0.46  % (20266)Memory used [KB]: 10490
% 0.21/0.46  % (20266)Time elapsed: 0.002 s
% 0.21/0.46  % (20266)------------------------------
% 0.21/0.46  % (20266)------------------------------
% 0.21/0.46  % (20273)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.47  % (20273)Refutation not found, incomplete strategy% (20273)------------------------------
% 0.21/0.47  % (20273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20273)Memory used [KB]: 1663
% 0.21/0.47  % (20273)Time elapsed: 0.056 s
% 0.21/0.47  % (20273)------------------------------
% 0.21/0.47  % (20273)------------------------------
% 0.21/0.48  % (20269)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.49  % (20262)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.49  % (20279)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.49  % (20262)Refutation not found, incomplete strategy% (20262)------------------------------
% 0.21/0.49  % (20262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (20262)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (20262)Memory used [KB]: 10746
% 0.21/0.49  % (20262)Time elapsed: 0.075 s
% 0.21/0.49  % (20262)------------------------------
% 0.21/0.49  % (20262)------------------------------
% 0.21/0.49  % (20260)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.49  % (20274)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.49  % (20259)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (20259)Refutation not found, incomplete strategy% (20259)------------------------------
% 0.21/0.50  % (20259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20259)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20259)Memory used [KB]: 10618
% 0.21/0.50  % (20259)Time elapsed: 0.088 s
% 0.21/0.50  % (20259)------------------------------
% 0.21/0.50  % (20259)------------------------------
% 0.21/0.50  % (20278)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (20256)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (20267)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (20268)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (20264)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (20264)Refutation not found, incomplete strategy% (20264)------------------------------
% 0.21/0.50  % (20264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (20264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (20264)Memory used [KB]: 10490
% 0.21/0.50  % (20264)Time elapsed: 0.100 s
% 0.21/0.50  % (20264)------------------------------
% 0.21/0.50  % (20264)------------------------------
% 0.21/0.51  % (20261)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (20270)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (20277)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (20269)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f314,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f313,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f10])).
% 0.21/0.51  fof(f10,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_9)).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    v2_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f312,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f312,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f311,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f311,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f310,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f310,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | v2_struct_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f309,f59])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f58,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    l1_orders_2(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f55,f33])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | l1_orders_2(sK1)),
% 0.21/0.51    inference(resolution,[],[f36,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    l1_waybel_0(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.51  fof(f309,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK1) | v2_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f308,f44])).
% 0.21/0.51  fof(f308,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f307,f33])).
% 0.21/0.51  fof(f307,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f306,f30])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f305,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_1(u1_waybel_0(X0,X1)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0)) => (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(u1_waybel_0(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_waybel_0)).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f304,f59])).
% 0.21/0.51  fof(f304,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~l1_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f303,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0] : (l1_waybel_0(sK2(X0),X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ? [X1] : (v7_waybel_0(X1) & v6_waybel_0(X1,X0) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1) & l1_waybel_0(X1,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc5_waybel_0)).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    ~l1_waybel_0(sK2(sK1),sK1) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f302,f29])).
% 0.21/0.51  fof(f302,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~l1_waybel_0(sK2(sK1),sK1) | v2_struct_0(sK1)),
% 0.21/0.51    inference(subsumption_resolution,[],[f301,f59])).
% 0.21/0.51  fof(f301,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~l1_struct_0(sK1) | ~l1_waybel_0(sK2(sK1),sK1) | v2_struct_0(sK1)),
% 0.21/0.51    inference(resolution,[],[f300,f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_struct_0(X0) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)) | (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : ((l1_waybel_0(X1,X0) & l1_struct_0(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_yellow_6(X0,X1),u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_yellow_6)).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f299,f33])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f298,f30])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f297,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0)) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f296,f33])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f295,f30])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f294,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~l1_waybel_0(X1,X0) | ~l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f293,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ~r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f292,f32])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f291,f30])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f29])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f33])).
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f288])).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(resolution,[],[f287,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : ((r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r1_waybel_0(X0,X1,X2) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r1_orders_2(X1,X3,X4) => r2_hidden(k2_waybel_0(X0,X1,X4),X2))) & m1_subset_1(X3,u1_struct_0(X1))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_waybel_0)).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK0)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f286,f31])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f285,f32])).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f284,f30])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f283,f29])).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f282,f33])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1)) | ~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(k4_yellow_6(sK1,sK2(sK1)),u1_struct_0(sK1)) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)))),
% 0.21/0.51    inference(resolution,[],[f135,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~r2_hidden(k2_waybel_0(X0,X1,sK4(X0,X1,X2,X3)),X2) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X0) | r1_waybel_0(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    r2_hidden(k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))),k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1))) | v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))),u1_struct_0(sK1)) | ~v1_funct_1(u1_waybel_0(sK0,sK1)) | ~v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.51    inference(superposition,[],[f34,f129])).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    k2_waybel_0(sK0,sK1,sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1)),k4_yellow_6(sK1,sK2(sK1))))),
% 0.21/0.51    inference(resolution,[],[f128,f31])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (r1_waybel_0(sK0,sK1,X0) | k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1))))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f33])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) | ~l1_struct_0(sK0) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f32])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0] : (k2_waybel_0(sK0,sK1,sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(sK0),u1_waybel_0(sK0,sK1),sK4(sK0,sK1,X0,k4_yellow_6(sK1,sK2(sK1)))) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | r1_waybel_0(sK0,sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f123,f30])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_waybel_0(sK1,X0) | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) | v2_struct_0(X0) | ~l1_struct_0(X0) | r1_waybel_0(sK0,sK1,X1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f29])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | r1_waybel_0(sK0,sK1,X1) | v2_struct_0(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f59])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | r1_waybel_0(sK0,sK1,X1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f120,f32])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,X1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f33])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | k2_waybel_0(X0,sK1,sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) = k3_funct_2(u1_struct_0(sK1),u1_struct_0(X0),u1_waybel_0(X0,sK1),sK4(sK0,sK1,X1,k4_yellow_6(sK1,sK2(sK1)))) | ~l1_struct_0(sK0) | ~l1_waybel_0(sK1,X0) | ~l1_struct_0(X0) | v2_struct_0(sK0) | r1_waybel_0(sK0,sK1,X1) | ~l1_struct_0(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.51    inference(resolution,[],[f114,f30])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X6,X4,X5,X3] : (~l1_waybel_0(X3,X5) | v2_struct_0(X4) | k2_waybel_0(X4,X3,sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),u1_waybel_0(X4,X3),sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) | ~l1_struct_0(X5) | ~l1_waybel_0(X3,X4) | ~l1_struct_0(X4) | v2_struct_0(X5) | r1_waybel_0(X5,X3,X6) | ~l1_struct_0(X3) | v2_struct_0(X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f113])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ( ! [X6,X4,X5,X3] : (~l1_waybel_0(X3,X4) | v2_struct_0(X4) | k2_waybel_0(X4,X3,sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) = k3_funct_2(u1_struct_0(X3),u1_struct_0(X4),u1_waybel_0(X4,X3),sK4(X5,X3,X6,k4_yellow_6(X3,sK2(X3)))) | ~l1_struct_0(X5) | ~l1_waybel_0(X3,X5) | ~l1_struct_0(X4) | v2_struct_0(X5) | r1_waybel_0(X5,X3,X6) | ~l1_struct_0(X3) | v2_struct_0(X3) | ~l1_struct_0(X3)) )),
% 0.21/0.51    inference(resolution,[],[f106,f37])).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (~l1_waybel_0(X4,X0) | ~l1_waybel_0(X0,X1) | v2_struct_0(X1) | k2_waybel_0(X1,X0,sK4(X2,X0,X3,k4_yellow_6(X0,X4))) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),sK4(X2,X0,X3,k4_yellow_6(X0,X4))) | ~l1_struct_0(X2) | ~l1_waybel_0(X0,X2) | ~l1_struct_0(X1) | v2_struct_0(X2) | r1_waybel_0(X2,X0,X3) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_waybel_0(X0,X1) | v2_struct_0(X1) | k2_waybel_0(X1,X0,sK4(X2,X0,X3,k4_yellow_6(X0,X4))) = k3_funct_2(u1_struct_0(X0),u1_struct_0(X1),u1_waybel_0(X1,X0),sK4(X2,X0,X3,k4_yellow_6(X0,X4))) | ~l1_struct_0(X2) | ~l1_waybel_0(X0,X2) | ~l1_struct_0(X1) | v2_struct_0(X2) | r1_waybel_0(X2,X0,X3) | ~l1_struct_0(X0) | ~l1_waybel_0(X4,X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(resolution,[],[f64,f51])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X10,X8,X7,X11,X9] : (~m1_subset_1(X11,u1_struct_0(X8)) | v2_struct_0(X8) | ~l1_waybel_0(X8,X7) | v2_struct_0(X7) | k2_waybel_0(X7,X8,sK4(X9,X8,X10,X11)) = k3_funct_2(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),sK4(X9,X8,X10,X11)) | ~l1_struct_0(X9) | ~l1_waybel_0(X8,X9) | ~l1_struct_0(X7) | v2_struct_0(X9) | r1_waybel_0(X9,X8,X10)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X10,X8,X7,X11,X9] : (~l1_struct_0(X7) | v2_struct_0(X8) | ~l1_waybel_0(X8,X7) | v2_struct_0(X7) | k2_waybel_0(X7,X8,sK4(X9,X8,X10,X11)) = k3_funct_2(u1_struct_0(X8),u1_struct_0(X7),u1_waybel_0(X7,X8),sK4(X9,X8,X10,X11)) | ~l1_struct_0(X9) | v2_struct_0(X8) | ~l1_waybel_0(X8,X9) | ~m1_subset_1(X11,u1_struct_0(X8)) | v2_struct_0(X9) | r1_waybel_0(X9,X8,X10)) )),
% 0.21/0.51    inference(resolution,[],[f45,f46])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | v2_struct_0(X0) | k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => k2_waybel_0(X0,X1,X2) = k3_funct_2(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_waybel_0)).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | v1_xboole_0(X1) | ~m1_subset_1(X2,X0) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))) | ~m1_subset_1(X2,X0)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,X0) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r2_hidden(k3_funct_2(X0,X1,X3,X2),k2_relset_1(X0,X1,X3))))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_funct_2)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (20269)------------------------------
% 0.21/0.51  % (20269)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (20269)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (20269)Memory used [KB]: 6908
% 0.21/0.51  % (20269)Time elapsed: 0.097 s
% 0.21/0.51  % (20269)------------------------------
% 0.21/0.51  % (20269)------------------------------
% 0.21/0.51  % (20255)Success in time 0.155 s
%------------------------------------------------------------------------------
