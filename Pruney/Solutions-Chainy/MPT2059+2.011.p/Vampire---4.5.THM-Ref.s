%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 (1165 expanded)
%              Number of leaves         :    9 ( 211 expanded)
%              Depth                    :   30
%              Number of atoms          :  711 (8375 expanded)
%              Number of equality atoms :   11 (  33 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f384,plain,(
    $false ),
    inference(subsumption_resolution,[],[f383,f295])).

fof(f295,plain,(
    r2_waybel_7(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f294,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <~> r2_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
                <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1)))
              <=> r2_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).

fof(f294,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f293,f33])).

fof(f33,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f293,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f292,f32])).

fof(f32,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f292,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f291,f31])).

fof(f31,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f12])).

fof(f291,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f290,f30])).

fof(f30,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f290,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f289,f203])).

fof(f203,plain,(
    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f97,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f97,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

% (16592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
fof(f289,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f288,f217])).

fof(f217,plain,(
    ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f205,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ v1_xboole_0(k2_struct_0(sK0)) ),
    inference(resolution,[],[f97,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f288,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f287,f97])).

fof(f287,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f286,f35])).

fof(f286,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f285,f276])).

fof(f276,plain,(
    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f275,f35])).

fof(f275,plain,
    ( v2_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f274,f217])).

fof(f274,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f273,f97])).

fof(f273,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f272])).

fof(f272,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f139,f46])).

fof(f139,plain,(
    ! [X5] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ l1_struct_0(X5)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(X5)
      | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5) ) ),
    inference(subsumption_resolution,[],[f138,f34])).

fof(f138,plain,(
    ! [X5] :
      ( v2_struct_0(X5)
      | ~ l1_struct_0(X5)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5) ) ),
    inference(subsumption_resolution,[],[f137,f33])).

fof(f137,plain,(
    ! [X5] :
      ( v2_struct_0(X5)
      | ~ l1_struct_0(X5)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5) ) ),
    inference(subsumption_resolution,[],[f114,f30])).

fof(f114,plain,(
    ! [X5] :
      ( v2_struct_0(X5)
      | ~ l1_struct_0(X5)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5)))
      | v1_xboole_0(sK1)
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5) ) ),
    inference(resolution,[],[f32,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f285,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f284,f244])).

fof(f244,plain,(
    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f243,f35])).

fof(f243,plain,
    ( v2_struct_0(sK0)
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f242,f217])).

fof(f242,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f241,f97])).

fof(f241,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f145,f46])).

fof(f145,plain,(
    ! [X8] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
      | ~ l1_struct_0(X8)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(X8)
      | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f144,f34])).

fof(f144,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f143,f33])).

fof(f143,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f117,f30])).

fof(f117,plain,(
    ! [X8] :
      ( v2_struct_0(X8)
      | ~ l1_struct_0(X8)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8)))
      | v1_xboole_0(sK1)
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v4_orders_2(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f284,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(subsumption_resolution,[],[f283,f234])).

fof(f234,plain,(
    ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f233,f35])).

fof(f233,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f232,f217])).

fof(f232,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f231,f97])).

fof(f231,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(duplicate_literal_removal,[],[f230])).

fof(f230,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f128,f46])).

fof(f128,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(X0)
      | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f127,f34])).

fof(f127,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f126,f33])).

fof(f126,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f125,f31])).

fof(f125,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f109,f30])).

fof(f109,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f32,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f283,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(resolution,[],[f196,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v7_waybel_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f196,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    inference(forward_demodulation,[],[f194,f124])).

fof(f124,plain,(
    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f123,f34])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f122,f33])).

fof(f122,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f121,f31])).

fof(f121,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f120,f30])).

fof(f120,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f119,f97])).

fof(f119,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f108,f35])).

fof(f108,plain,
    ( v2_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f32,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).

fof(f194,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f193,f29])).

fof(f29,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f193,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f192,f37])).

fof(f192,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f191,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f191,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f190,f35])).

fof(f190,plain,
    ( r2_waybel_7(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r2_hidden(X2,k10_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k10_yellow_6(X0,X1))
              <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).

fof(f27,plain,
    ( r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))
    | r2_waybel_7(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f383,plain,(
    ~ r2_waybel_7(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f382,f124])).

fof(f382,plain,(
    ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    inference(subsumption_resolution,[],[f381,f296])).

fof(f296,plain,(
    ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f295,f28])).

fof(f28,plain,
    ( ~ r2_waybel_7(sK0,sK1,sK2)
    | ~ r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f381,plain,
    ( ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f380,f276])).

fof(f380,plain,
    ( ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f379,f234])).

fof(f379,plain,
    ( v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(subsumption_resolution,[],[f368,f244])).

fof(f368,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f239,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v7_waybel_0(X0)
      | ~ v4_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f103,f37])).

fof(f103,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f102,f36])).

fof(f102,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ v4_orders_2(X0)
      | ~ v7_waybel_0(X0)
      | ~ l1_waybel_0(X0,sK0)
      | ~ r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2)
      | r2_hidden(sK2,k10_yellow_6(sK0,X0)) ) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r2_hidden(X2,k10_yellow_6(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f239,plain,(
    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f238,f35])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f237,f217])).

fof(f237,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f236,f97])).

fof(f236,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | ~ l1_struct_0(sK0) ),
    inference(resolution,[],[f136,f46])).

fof(f136,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_struct_0(X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | v2_struct_0(X2)
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f135,f34])).

fof(f135,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f134,f33])).

fof(f134,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f133,f31])).

fof(f133,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) ) ),
    inference(subsumption_resolution,[],[f111,f30])).

fof(f111,plain,(
    ! [X2] :
      ( v2_struct_0(X2)
      | ~ l1_struct_0(X2)
      | v1_xboole_0(k2_struct_0(sK0))
      | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2)))
      | v1_xboole_0(sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
      | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1)) ) ),
    inference(resolution,[],[f32,f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:15:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.48  % (16596)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (16596)Refutation not found, incomplete strategy% (16596)------------------------------
% 0.21/0.48  % (16596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (16596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (16596)Memory used [KB]: 6140
% 0.21/0.48  % (16596)Time elapsed: 0.074 s
% 0.21/0.48  % (16596)------------------------------
% 0.21/0.48  % (16596)------------------------------
% 0.21/0.49  % (16610)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (16608)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.51  % (16610)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f383,f295])).
% 0.21/0.51  fof(f295,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f294,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <~> r2_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,k3_yellow19(X0,k2_struct_0(X0),X1))) <=> r2_waybel_7(X0,X1,X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow19)).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f293,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f292,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f291,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f290,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~v1_xboole_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f289,f203])).
% 0.21/0.51  fof(f203,plain,(
% 0.21/0.51    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(resolution,[],[f97,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f37,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  % (16592)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  fof(f289,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f288,f217])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f205,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ~v2_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f97,f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f287,f97])).
% 0.21/0.51  fof(f287,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f286,f35])).
% 0.21/0.51  fof(f286,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f285,f276])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f275,f35])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    v2_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f274,f217])).
% 0.21/0.51  fof(f274,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f273,f97])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f272])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f139,f46])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ( ! [X5] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | ~l1_struct_0(X5) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(X5) | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f138,f34])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X5] : (v2_struct_0(X5) | ~l1_struct_0(X5) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f33])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X5] : (v2_struct_0(X5) | ~l1_struct_0(X5) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f114,f30])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    ( ! [X5] : (v2_struct_0(X5) | ~l1_struct_0(X5) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X5))) | v1_xboole_0(sK1) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(X5,k2_struct_0(sK0),sK1),X5)) )),
% 0.21/0.51    inference(resolution,[],[f32,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.51  fof(f285,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f284,f244])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f243,f35])).
% 0.21/0.51  fof(f243,plain,(
% 0.21/0.51    v2_struct_0(sK0) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f242,f217])).
% 0.21/0.51  fof(f242,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f241,f97])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f240])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f145,f46])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    ( ! [X8] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) | ~l1_struct_0(X8) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(X8) | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f144,f34])).
% 0.21/0.51  fof(f144,plain,(
% 0.21/0.51    ( ! [X8] : (v2_struct_0(X8) | ~l1_struct_0(X8) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f143,f33])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    ( ! [X8] : (v2_struct_0(X8) | ~l1_struct_0(X8) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f117,f30])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    ( ! [X8] : (v2_struct_0(X8) | ~l1_struct_0(X8) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X8))) | v1_xboole_0(sK1) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v4_orders_2(k3_yellow19(X8,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(resolution,[],[f32,f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v4_orders_2(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(subsumption_resolution,[],[f283,f234])).
% 0.21/0.51  fof(f234,plain,(
% 0.21/0.51    ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f233,f35])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f232,f217])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f231,f97])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f230])).
% 0.21/0.51  fof(f230,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f128,f46])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(X0) | ~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f127,f34])).
% 0.21/0.51  fof(f127,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f126,f33])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f125,f31])).
% 0.21/0.51  fof(f125,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f109,f30])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(X0,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(resolution,[],[f32,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.51  fof(f283,plain,(
% 0.21/0.51    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | v2_struct_0(sK0) | ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.51    inference(resolution,[],[f196,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v7_waybel_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f196,plain,(
% 0.21/0.51    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | r2_waybel_7(sK0,sK1,sK2) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f195])).
% 0.21/0.51  fof(f195,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f194,f124])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f123,f34])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f122,f33])).
% 0.21/0.51  fof(f122,plain,(
% 0.21/0.51    ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f121,f31])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f120,f30])).
% 0.21/0.51  fof(f120,plain,(
% 0.21/0.51    v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f119,f97])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f108,f35])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    v2_struct_0(sK0) | ~l1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | sK1 = k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(resolution,[],[f32,f47])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f37])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f191,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f191,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f190,f35])).
% 0.21/0.51  fof(f190,plain,(
% 0.21/0.51    r2_waybel_7(sK0,sK1,sK2) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(resolution,[],[f27,f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r2_hidden(X2,k10_yellow_6(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,k10_yellow_6(X0,X1)) <=> r2_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow19)).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1))) | r2_waybel_7(sK0,sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    ~r2_waybel_7(sK0,sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f382,f124])).
% 0.21/0.51  fof(f382,plain,(
% 0.21/0.51    ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f381,f296])).
% 0.21/0.51  fof(f296,plain,(
% 0.21/0.51    ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(resolution,[],[f295,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ~r2_waybel_7(sK0,sK1,sK2) | ~r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f381,plain,(
% 0.21/0.51    ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f380,f276])).
% 0.21/0.51  fof(f380,plain,(
% 0.21/0.51    ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f379,f234])).
% 0.21/0.51  fof(f379,plain,(
% 0.21/0.51    v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(subsumption_resolution,[],[f368,f244])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)))),
% 0.21/0.51    inference(resolution,[],[f239,f104])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ( ! [X0] : (~v7_waybel_0(X0) | ~v4_orders_2(X0) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f103,f37])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f102,f36])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,X0))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f100,f35])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~r2_waybel_7(sK0,k2_yellow19(sK0,X0),sK2) | r2_hidden(sK2,k10_yellow_6(sK0,X0))) )),
% 0.21/0.51    inference(resolution,[],[f29,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_waybel_7(X0,k2_yellow19(X0,X1),X2) | r2_hidden(X2,k10_yellow_6(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f239,plain,(
% 0.21/0.51    v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f238,f35])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    v2_struct_0(sK0) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f237,f217])).
% 0.21/0.51  fof(f237,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(subsumption_resolution,[],[f236,f97])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f235])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f136,f46])).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X2] : (~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | ~l1_struct_0(X2) | v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(X2) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f34])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X2] : (v2_struct_0(X2) | ~l1_struct_0(X2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f134,f33])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    ( ! [X2] : (v2_struct_0(X2) | ~l1_struct_0(X2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f133,f31])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    ( ! [X2] : (v2_struct_0(X2) | ~l1_struct_0(X2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f30])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ( ! [X2] : (v2_struct_0(X2) | ~l1_struct_0(X2) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(X2))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v7_waybel_0(k3_yellow19(X2,k2_struct_0(sK0),sK1))) )),
% 0.21/0.51    inference(resolution,[],[f32,f42])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (16610)------------------------------
% 0.21/0.51  % (16610)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (16610)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (16610)Memory used [KB]: 1918
% 0.21/0.51  % (16610)Time elapsed: 0.092 s
% 0.21/0.51  % (16610)------------------------------
% 0.21/0.51  % (16610)------------------------------
% 0.21/0.51  % (16588)Success in time 0.152 s
%------------------------------------------------------------------------------
