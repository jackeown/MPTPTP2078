%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t13_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:49 EDT 2019

% Result     : Theorem 10.29s
% Output     : Refutation 10.29s
% Verified   : 
% Statistics : Number of formulae       :  203 (2300 expanded)
%              Number of leaves         :   14 ( 398 expanded)
%              Depth                    :   56
%              Number of atoms          :  978 (16574 expanded)
%              Number of equality atoms :    6 (  44 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21979,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21978,f11786])).

fof(f11786,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f11783])).

fof(f11783,plain,
    ( ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f11778,f105])).

fof(f105,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <~> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & v4_orders_2(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,X1))
                <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t13_yellow19)).

fof(f11778,plain,(
    ! [X1] :
      ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X1)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f11772])).

fof(f11772,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X1)
      | r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X1) ) ),
    inference(resolution,[],[f11769,f2784])).

fof(f2784,plain,(
    ! [X14] :
      ( ~ r1_waybel_0(sK0,sK1,sK7(sK0,k2_yellow19(sK0,sK1),X14))
      | r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X14) ) ),
    inference(subsumption_resolution,[],[f2780,f900])).

fof(f900,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK7(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f899,f113])).

fof(f113,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f899,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | m1_subset_1(sK7(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f143,f112])).

fof(f112,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',d5_waybel_7)).

fof(f2780,plain,(
    ! [X14] :
      ( ~ m1_subset_1(sK7(sK0,k2_yellow19(sK0,sK1),X14),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_waybel_0(sK0,sK1,sK7(sK0,k2_yellow19(sK0,sK1),X14))
      | r2_waybel_7(sK0,k2_yellow19(sK0,sK1),X14) ) ),
    inference(resolution,[],[f2766,f633])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(sK0,X0,X1),X0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f632,f113])).

fof(f632,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ r2_hidden(sK7(sK0,X0,X1),X0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f146,f112])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(sK7(X0,X1,X2),X1)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f2766,plain,(
    ! [X1] :
      ( r2_hidden(X1,k2_yellow19(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f2765,f113])).

fof(f2765,plain,(
    ! [X1] :
      ( ~ r1_waybel_0(sK0,sK1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,k2_yellow19(sK0,sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f2763,f118])).

fof(f118,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',dt_l1_pre_topc)).

fof(f2763,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f2762,f111])).

fof(f111,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f2762,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f2759,f107])).

fof(f107,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f2759,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(resolution,[],[f139,f110])).

fof(f110,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X2,k2_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_hidden(X2,k2_yellow19(X0,X1))
            <=> ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & r1_waybel_0(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t11_yellow19)).

fof(f11769,plain,(
    ! [X0,X1] :
      ( r1_waybel_0(sK0,sK1,sK7(sK0,X1,X0))
      | ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f11736])).

fof(f11736,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k10_yellow_6(sK0,sK1))
      | r1_waybel_0(sK0,sK1,sK7(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0)
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(resolution,[],[f4485,f551])).

fof(f551,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK7(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f550,f113])).

fof(f550,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | r2_hidden(X0,sK7(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(resolution,[],[f145,f112])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(X2,sK7(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f4485,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X7,sK7(sK0,X5,X6))
      | ~ r2_hidden(X7,k10_yellow_6(sK0,sK1))
      | r1_waybel_0(sK0,sK1,sK7(sK0,X5,X6))
      | r2_waybel_7(sK0,X5,X6) ) ),
    inference(resolution,[],[f4480,f3165])).

fof(f3165,plain,(
    ! [X6,X4,X5] :
      ( m1_connsp_2(sK7(sK0,X4,X5),sK0,X6)
      | ~ r2_hidden(X6,sK7(sK0,X4,X5))
      | r2_waybel_7(sK0,X4,X5) ) ),
    inference(subsumption_resolution,[],[f3164,f900])).

fof(f3164,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK7(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK7(sK0,X4,X5))
      | m1_connsp_2(sK7(sK0,X4,X5),sK0,X6)
      | r2_waybel_7(sK0,X4,X5) ) ),
    inference(subsumption_resolution,[],[f3163,f112])).

fof(f3163,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK7(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK7(sK0,X4,X5))
      | m1_connsp_2(sK7(sK0,X4,X5),sK0,X6)
      | ~ v2_pre_topc(sK0)
      | r2_waybel_7(sK0,X4,X5) ) ),
    inference(subsumption_resolution,[],[f3161,f113])).

fof(f3161,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(sK7(sK0,X4,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X6,sK7(sK0,X4,X5))
      | m1_connsp_2(sK7(sK0,X4,X5),sK0,X6)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r2_waybel_7(sK0,X4,X5) ) ),
    inference(resolution,[],[f3156,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK7(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f3156,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f3155,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f101])).

fof(f101,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t4_subset)).

fof(f3155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f3154,f113])).

fof(f3154,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f3153,f111])).

fof(f3153,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | m1_connsp_2(X0,sK0,X1) ) ),
    inference(resolution,[],[f128,f112])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t5_connsp_2)).

fof(f4480,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X0,sK0,X1)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4479,f112])).

fof(f4479,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_connsp_2(X0,sK0,X1)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4478,f111])).

fof(f4478,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_connsp_2(X0,sK0,X1)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4477,f113])).

fof(f4477,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_connsp_2(X0,sK0,X1)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X1,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f3745,f110])).

fof(f3745,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_waybel_0(X0,sK1,X2)
      | ~ r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3744,f2444])).

fof(f2444,plain,(
    ! [X0] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f2443,f108])).

fof(f108,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f2443,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f2442,f107])).

fof(f2442,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f155,f109])).

fof(f109,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_waybel_0(X1,X0)
      | ~ v7_waybel_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & v7_waybel_0(X1)
        & v4_orders_2(X1)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',dt_k10_yellow_6)).

fof(f3744,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_waybel_0(X0,sK1,X2)
      | ~ r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3743,f172])).

fof(f3743,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_waybel_0(X0,sK1,X2)
      | ~ r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3742,f108])).

fof(f3742,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_waybel_0(X0,sK1,X2)
      | ~ r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3741,f107])).

fof(f3741,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | r1_waybel_0(X0,sK1,X2)
      | ~ r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(resolution,[],[f179,f109])).

fof(f179,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X4,X0,X3)
      | r1_waybel_0(X0,X1,X4)
      | ~ r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f129])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_connsp_2(X4,X0,X3)
      | r1_waybel_0(X0,X1,X4)
      | ~ r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( r1_waybel_0(X0,X1,X4)
                          | ~ m1_connsp_2(X4,X0,X3) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k10_yellow_6(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ! [X4] :
                          ( m1_connsp_2(X4,X0,X3)
                         => r1_waybel_0(X0,X1,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',d18_yellow_6)).

fof(f21978,plain,(
    r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21977,f111])).

fof(f21977,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21976,f106])).

fof(f106,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f21976,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21975,f2449])).

fof(f2449,plain,(
    m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2448,f112])).

fof(f2448,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2447,f111])).

fof(f2447,plain,
    ( v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2446,f113])).

fof(f2446,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f2444,f110])).

fof(f21975,plain,
    ( ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21974,f110])).

fof(f21974,plain,
    ( ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21973,f109])).

fof(f21973,plain,
    ( ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21972,f108])).

fof(f21972,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21971,f107])).

fof(f21971,plain,
    ( v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21970,f113])).

fof(f21970,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21969,f112])).

fof(f21969,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v7_waybel_0(sK1)
    | ~ l1_waybel_0(sK1,sK0)
    | ~ m1_subset_1(k10_yellow_6(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(resolution,[],[f21963,f177])).

fof(f177,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_waybel_0(X0,X1,sK6(X0,X1,X3))
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f21963,plain,(
    r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f21962,f106])).

fof(f21962,plain,
    ( r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f21960,f11786])).

fof(f21960,plain,
    ( r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21958,f5579])).

fof(f5579,plain,(
    ! [X2] :
      ( m1_subset_1(sK6(sK0,sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,k10_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f5578])).

fof(f5578,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k10_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | m1_subset_1(sK6(sK0,sK1,X2),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f5575,f1664])).

fof(f1664,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1663,f113])).

fof(f1663,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f1662,f111])).

fof(f1662,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_connsp_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f156,f112])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',dt_m1_connsp_2)).

fof(f5575,plain,(
    ! [X0] :
      ( m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5574,f112])).

fof(f5574,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
      | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5573,f111])).

fof(f5573,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
      | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f5572,f113])).

fof(f5572,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK6(sK0,sK1,X0),sK0,X0)
      | r2_hidden(X0,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f3656,f110])).

fof(f3656,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(sK1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
      | r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3655,f2444])).

fof(f3655,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
      | r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3654,f108])).

fof(f3654,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
      | r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(subsumption_resolution,[],[f3653,f107])).

fof(f3653,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(sK1)
      | ~ v4_orders_2(sK1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(sK1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,sK1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,sK1,X1),X0,X1)
      | r2_hidden(X1,k10_yellow_6(X0,sK1)) ) ),
    inference(resolution,[],[f178,f109])).

fof(f178,plain,(
    ! [X0,X3,X1] :
      ( ~ v7_waybel_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(k10_yellow_6(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
      | r2_hidden(X3,k10_yellow_6(X0,X1)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | m1_connsp_2(sK6(X0,X1,X3),X0,X3)
      | r2_hidden(X3,X2)
      | k10_yellow_6(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f21958,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_waybel_0(sK0,sK1,sK6(sK0,sK1,sK2)) ),
    inference(resolution,[],[f21957,f246])).

fof(f246,plain,(
    ! [X0] :
      ( r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f119,f113])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t44_tops_1)).

fof(f21957,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK6(sK0,sK1,sK2)),X0)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f21952,f1915])).

fof(f1915,plain,(
    ! [X2,X3] :
      ( ~ r1_waybel_0(sK0,sK1,X2)
      | ~ r1_tarski(X2,X3)
      | r1_waybel_0(sK0,sK1,X3) ) ),
    inference(subsumption_resolution,[],[f1914,f113])).

fof(f1914,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | ~ r1_waybel_0(sK0,sK1,X2)
      | r1_waybel_0(sK0,sK1,X3)
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f1912,f118])).

fof(f1912,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f1911,f111])).

fof(f1911,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f1908,f107])).

fof(f1908,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | ~ r1_tarski(X0,X1)
      | ~ r1_waybel_0(sK0,sK1,X0)
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(resolution,[],[f141,f110])).

fof(f141,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ r1_tarski(X2,X3)
      | ~ r1_waybel_0(X0,X1,X2)
      | r1_waybel_0(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2,X3] :
              ( ( ( r2_waybel_0(X0,X1,X3)
                  | ~ r2_waybel_0(X0,X1,X2) )
                & ( r1_waybel_0(X0,X1,X3)
                  | ~ r1_waybel_0(X0,X1,X2) ) )
              | ~ r1_tarski(X2,X3) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ( r1_tarski(X2,X3)
             => ( ( r2_waybel_0(X0,X1,X2)
                 => r2_waybel_0(X0,X1,X3) )
                & ( r1_waybel_0(X0,X1,X2)
                 => r1_waybel_0(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',t8_waybel_0)).

fof(f21952,plain,(
    r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK6(sK0,sK1,sK2))) ),
    inference(subsumption_resolution,[],[f21951,f106])).

fof(f21951,plain,
    ( r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK6(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f21949,f11786])).

fof(f21949,plain,
    ( r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK6(sK0,sK1,sK2)))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21947,f5579])).

fof(f21947,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f21941,f796])).

fof(f796,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f160,f113])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',dt_k1_tops_1)).

fof(f21941,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK6(sK0,sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_waybel_0(sK0,sK1,k1_tops_1(sK0,sK6(sK0,sK1,sK2))) ),
    inference(resolution,[],[f21857,f246])).

fof(f21857,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),X0)
      | r1_waybel_0(sK0,sK1,X0) ) ),
    inference(resolution,[],[f21834,f1915])).

fof(f21834,plain,(
    r1_waybel_0(sK0,sK1,k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2)))) ),
    inference(resolution,[],[f21832,f1365])).

fof(f1365,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | r1_waybel_0(sK0,sK1,X1) ) ),
    inference(subsumption_resolution,[],[f1364,f113])).

fof(f1364,plain,(
    ! [X1] :
      ( r1_waybel_0(sK0,sK1,X1)
      | ~ r2_hidden(X1,k2_yellow19(sK0,sK1))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f1362,f118])).

fof(f1362,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1361,f111])).

fof(f1361,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1358,f107])).

fof(f1358,plain,(
    ! [X0] :
      ( ~ l1_struct_0(sK0)
      | v2_struct_0(sK1)
      | v2_struct_0(sK0)
      | r1_waybel_0(sK0,sK1,X0)
      | ~ r2_hidden(X0,k2_yellow19(sK0,sK1)) ) ),
    inference(resolution,[],[f137,f110])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | r1_waybel_0(X0,X1,X2)
      | ~ r2_hidden(X2,k2_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f21832,plain,(
    r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21831,f106])).

fof(f21831,plain,
    ( r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f21829,f11786])).

fof(f21829,plain,
    ( r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21621,f5579])).

fof(f21621,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f21620,f106])).

fof(f21620,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f21602,f11786])).

fof(f21602,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,sK6(sK0,sK1,sK2))),k2_yellow19(sK0,sK1))
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f21585,f5580])).

fof(f5580,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_tops_1(sK0,sK6(sK0,sK1,X1)))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f5577])).

fof(f5577,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(X1,k10_yellow_6(sK0,sK1))
      | r2_hidden(X1,k1_tops_1(sK0,sK6(sK0,sK1,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f5575,f3079])).

fof(f3079,plain,(
    ! [X0,X1] :
      ( ~ m1_connsp_2(X1,sK0,X0)
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3078,f1664])).

fof(f3078,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f3077,f113])).

fof(f3077,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f3076,f111])).

fof(f3076,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0) ) ),
    inference(resolution,[],[f127,f112])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',d1_connsp_2)).

fof(f21585,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k2_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f21584,f796])).

fof(f21584,plain,(
    ! [X0] :
      ( r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k2_yellow19(sK0,sK1))
      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f21567,f106])).

fof(f21567,plain,(
    ! [X0] :
      ( r2_hidden(k1_tops_1(sK0,k1_tops_1(sK0,X0)),k2_yellow19(sK0,sK1))
      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,k1_tops_1(sK0,X0))
      | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f21531,f3169])).

fof(f3169,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_tops_1(sK0,k1_tops_1(sK0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f3168,f3079])).

fof(f3168,plain,(
    ! [X8,X7] :
      ( m1_connsp_2(k1_tops_1(sK0,X7),sK0,X8)
      | ~ r2_hidden(X8,k1_tops_1(sK0,X7))
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3167,f796])).

fof(f3167,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,k1_tops_1(sK0,X7))
      | m1_connsp_2(k1_tops_1(sK0,X7),sK0,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f3166,f112])).

fof(f3166,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,k1_tops_1(sK0,X7))
      | m1_connsp_2(k1_tops_1(sK0,X7),sK0,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f3162,f113])).

fof(f3162,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,k1_tops_1(sK0,X7))
      | m1_connsp_2(k1_tops_1(sK0,X7),sK0,X8)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f3156,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t13_yellow19.p',fc9_tops_1)).

fof(f21531,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK2,k1_tops_1(sK0,X2))
      | r2_hidden(k1_tops_1(sK0,X2),k2_yellow19(sK0,sK1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f21437,f2244])).

fof(f2244,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_waybel_7(sK0,X12,X11)
      | r2_hidden(k1_tops_1(sK0,X10),X12)
      | ~ r2_hidden(X11,k1_tops_1(sK0,X10))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2243,f796])).

fof(f2243,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X11,k1_tops_1(sK0,X10))
      | r2_hidden(k1_tops_1(sK0,X10),X12)
      | ~ r2_waybel_7(sK0,X12,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2242,f112])).

fof(f2242,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X11,k1_tops_1(sK0,X10))
      | r2_hidden(k1_tops_1(sK0,X10),X12)
      | ~ r2_waybel_7(sK0,X12,X11)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f2236,f113])).

fof(f2236,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X10),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X11,k1_tops_1(sK0,X10))
      | r2_hidden(k1_tops_1(sK0,X10),X12)
      | ~ r2_waybel_7(sK0,X12,X11)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_pre_topc(sK0) ) ),
    inference(resolution,[],[f2231,f159])).

fof(f2231,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X0,X2)
      | ~ r2_waybel_7(sK0,X2,X1) ) ),
    inference(subsumption_resolution,[],[f2230,f113])).

fof(f2230,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | ~ r2_hidden(X1,X0)
      | r2_hidden(X0,X2)
      | ~ r2_waybel_7(sK0,X2,X1) ) ),
    inference(resolution,[],[f142,f112])).

fof(f142,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X3,X1)
      | ~ r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f21437,plain,(
    r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2) ),
    inference(duplicate_literal_removal,[],[f21421])).

fof(f21421,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2) ),
    inference(resolution,[],[f21418,f633])).

fof(f21418,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK2),k2_yellow19(sK0,sK1))
      | r2_waybel_7(sK0,X0,sK2) ) ),
    inference(subsumption_resolution,[],[f21417,f11786])).

fof(f21417,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK2),k2_yellow19(sK0,sK1))
      | r2_waybel_7(sK0,X0,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f21415])).

fof(f21415,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,X0,sK2),k2_yellow19(sK0,sK1))
      | r2_waybel_7(sK0,X0,sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,sK1))
      | r2_waybel_7(sK0,X0,sK2) ) ),
    inference(resolution,[],[f2296,f551])).

fof(f2296,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2,sK7(sK0,X0,X1))
      | r2_hidden(sK7(sK0,X0,X1),k2_yellow19(sK0,sK1))
      | r2_waybel_7(sK0,X0,X1)
      | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ) ),
    inference(resolution,[],[f2241,f104])).

fof(f104,plain,
    ( r2_waybel_7(sK0,k2_yellow19(sK0,sK1),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,sK1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f2241,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r2_waybel_7(sK0,X9,X8)
      | r2_hidden(sK7(sK0,X6,X7),X9)
      | ~ r2_hidden(X8,sK7(sK0,X6,X7))
      | r2_waybel_7(sK0,X6,X7) ) ),
    inference(subsumption_resolution,[],[f2240,f900])).

fof(f2240,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(sK7(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,sK7(sK0,X6,X7))
      | r2_hidden(sK7(sK0,X6,X7),X9)
      | ~ r2_waybel_7(sK0,X9,X8)
      | r2_waybel_7(sK0,X6,X7) ) ),
    inference(subsumption_resolution,[],[f2239,f112])).

fof(f2239,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(sK7(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,sK7(sK0,X6,X7))
      | r2_hidden(sK7(sK0,X6,X7),X9)
      | ~ r2_waybel_7(sK0,X9,X8)
      | ~ v2_pre_topc(sK0)
      | r2_waybel_7(sK0,X6,X7) ) ),
    inference(subsumption_resolution,[],[f2235,f113])).

fof(f2235,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ m1_subset_1(sK7(sK0,X6,X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X8,sK7(sK0,X6,X7))
      | r2_hidden(sK7(sK0,X6,X7),X9)
      | ~ r2_waybel_7(sK0,X9,X8)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r2_waybel_7(sK0,X6,X7) ) ),
    inference(resolution,[],[f2231,f144])).
%------------------------------------------------------------------------------
