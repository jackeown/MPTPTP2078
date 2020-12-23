%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t6_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:53 EDT 2019

% Result     : Theorem 159.67s
% Output     : Refutation 159.67s
% Verified   : 
% Statistics : Number of formulae       :  204 (2682 expanded)
%              Number of leaves         :   38 ( 895 expanded)
%              Depth                    :   19
%              Number of atoms          : 1003 (35851 expanded)
%              Number of equality atoms :   46 ( 348 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178280,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f273,f280,f297,f23597,f174927,f177161,f178041,f178279])).

fof(f178279,plain,
    ( ~ spl13_0
    | spl13_63 ),
    inference(avatar_contradiction_clause,[],[f178278])).

fof(f178278,plain,
    ( $false
    | ~ spl13_0
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f248,f174874])).

fof(f174874,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f152,f153,f24477,f24841,f154,f174785,f185])).

fof(f185,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | r2_hidden(X4,X1)
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f124,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(X2,sK4(X0,X1,X2))
              & v3_pre_topc(sK4(X0,X1,X2),X0)
              & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f122,f123])).

fof(f123,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(X2,sK4(X0,X1,X2))
        & v3_pre_topc(sK4(X0,X1,X2),X0)
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f122,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f121])).

fof(f121,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ? [X3] :
                ( ~ r2_hidden(X3,X1)
                & r2_hidden(X2,X3)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X3] :
                ( r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X3)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',d5_waybel_7)).

fof(f174785,plain,(
    ! [X0] : r2_waybel_7(sK0,k1_yellow19(sK0,X0),X0) ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f69443])).

fof(f69443,plain,(
    ! [X4,X3] :
      ( r2_waybel_7(X3,k1_yellow19(X3,X4),X4)
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f69407,f44585])).

fof(f44585,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X2,X1)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f44569])).

fof(f44569,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(X1,u1_struct_0(X0))
      | r2_waybel_7(X0,X2,X1)
      | r2_waybel_7(X0,X2,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f2569,f188])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK4(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f2569,plain,(
    ! [X12,X10,X13,X11] :
      ( ~ r2_hidden(X13,sK4(X10,X11,X12))
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(X10)
      | m1_subset_1(X13,u1_struct_0(X10))
      | r2_waybel_7(X10,X11,X12) ) ),
    inference(resolution,[],[f186,f224])).

fof(f224,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f108])).

fof(f108,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f107])).

fof(f107,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t4_subset)).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f124])).

fof(f69407,plain,(
    ! [X4,X3] :
      ( r2_waybel_7(X3,k1_yellow19(X3,X4),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3) ) ),
    inference(duplicate_literal_removal,[],[f69406])).

fof(f69406,plain,(
    ! [X4,X3] :
      ( r2_waybel_7(X3,k1_yellow19(X3,X4),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_pre_topc(X3)
      | ~ v2_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3)) ) ),
    inference(resolution,[],[f6540,f240])).

fof(f240,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',d10_xboole_0)).

fof(f6540,plain,(
    ! [X19,X17,X18] :
      ( ~ r1_tarski(k1_yellow19(X17,X18),k1_yellow19(X17,X19))
      | r2_waybel_7(X17,k1_yellow19(X17,X19),X18)
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17)
      | ~ m1_subset_1(X19,u1_struct_0(X17)) ) ),
    inference(subsumption_resolution,[],[f6537,f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f53])).

fof(f53,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',fc1_yellow19)).

fof(f6537,plain,(
    ! [X19,X17,X18] :
      ( ~ r1_tarski(k1_yellow19(X17,X18),k1_yellow19(X17,X19))
      | r2_waybel_7(X17,k1_yellow19(X17,X19),X18)
      | ~ v13_waybel_0(k1_yellow19(X17,X19),k3_yellow_1(k2_struct_0(X17)))
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17)
      | ~ m1_subset_1(X19,u1_struct_0(X17)) ) ),
    inference(duplicate_literal_removal,[],[f6532])).

fof(f6532,plain,(
    ! [X19,X17,X18] :
      ( ~ r1_tarski(k1_yellow19(X17,X18),k1_yellow19(X17,X19))
      | r2_waybel_7(X17,k1_yellow19(X17,X19),X18)
      | ~ v13_waybel_0(k1_yellow19(X17,X19),k3_yellow_1(k2_struct_0(X17)))
      | ~ m1_subset_1(X18,u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17)
      | ~ m1_subset_1(X19,u1_struct_0(X17))
      | ~ l1_pre_topc(X17)
      | ~ v2_pre_topc(X17)
      | v2_struct_0(X17) ) ),
    inference(resolution,[],[f182,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',dt_k1_yellow19)).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | r2_waybel_7(X0,X2,X1)
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t4_yellow19)).

fof(f151,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f117,plain,
    ( ( ( ~ r2_hidden(sK1,sK3)
        & r2_waybel_7(sK0,sK3,sK2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(sK0)))
        & ~ v1_xboole_0(sK3)
        & r2_hidden(sK2,sK1)
        & m1_subset_1(sK2,u1_struct_0(sK0)) )
      | ~ v3_pre_topc(sK1,sK0) )
    & ( ! [X4] :
          ( ! [X5] :
              ( r2_hidden(sK1,X5)
              | ~ r2_waybel_7(sK0,X5,X4)
              | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
              | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
              | v1_xboole_0(X5) )
          | ~ r2_hidden(X4,sK1)
          | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f112,f116,f115,f114,f113])).

fof(f113,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X1,X3)
                      & r2_waybel_7(X0,X3,X2)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v3_pre_topc(X1,X0) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X1,X5)
                      | ~ r2_waybel_7(X0,X5,X4)
                      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                      | v1_xboole_0(X5) )
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(sK0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(sK0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(sK0)) )
            | ~ v3_pre_topc(X1,sK0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(sK0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(X0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ? [X2] :
              ( ? [X3] :
                  ( ~ r2_hidden(sK1,X3)
                  & r2_waybel_7(X0,X3,X2)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r2_hidden(X2,sK1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ v3_pre_topc(sK1,X0) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(sK1,X5)
                  | ~ r2_waybel_7(X0,X5,X4)
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                  | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                  | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                  | v1_xboole_0(X5) )
              | ~ r2_hidden(X4,sK1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | v3_pre_topc(sK1,X0) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X1,X3)
              & r2_waybel_7(X0,X3,X2)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
              & ~ v1_xboole_0(X3) )
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X1,X3)
            & r2_waybel_7(X0,X3,sK2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
            & ~ v1_xboole_0(X3) )
        & r2_hidden(sK2,X1)
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X1,X3)
          & r2_waybel_7(X0,X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
          & ~ v1_xboole_0(X3) )
     => ( ~ r2_hidden(X1,sK3)
        & r2_waybel_7(X0,sK3,X2)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
        & v13_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(sK3,k3_yellow_1(k2_struct_0(X0)))
        & ~ v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X4] :
                ( ! [X5] :
                    ( r2_hidden(X1,X5)
                    | ~ r2_waybel_7(X0,X5,X4)
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X5) )
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f111])).

fof(f111,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f110])).

fof(f110,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( ? [X3] :
                    ( ~ r2_hidden(X1,X3)
                    & r2_waybel_7(X0,X3,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ v3_pre_topc(X1,X0) )
          & ( ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X1,X3)
                    | ~ r2_waybel_7(X0,X3,X2)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                    | ~ v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | ~ v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                    | v1_xboole_0(X3) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                          & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ( r2_waybel_7(X0,X3,X2)
                         => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                        & v13_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(k2_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ( r2_waybel_7(X0,X3,X2)
                       => r2_hidden(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t6_yellow19)).

fof(f154,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f117])).

fof(f24841,plain,
    ( ~ r2_hidden(sK1,k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f24497,f24825,f183])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f120])).

fof(f120,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k1_yellow19(X0,X1))
                | ~ m1_connsp_2(X2,X0,X1) )
              & ( m1_connsp_2(X2,X0,X1)
                | ~ r2_hidden(X2,k1_yellow19(X0,X1)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f44,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t3_yellow19)).

fof(f24825,plain,
    ( ~ m1_connsp_2(sK1,sK0,o_2_3_yellow19(sK0,sK1))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f154,f24497,f24478,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f118])).

fof(f118,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f71])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',d1_connsp_2)).

fof(f24478,plain,
    ( ~ r2_hidden(o_2_3_yellow19(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f23783,f244])).

fof(f244,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f226])).

fof(f226,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f144])).

fof(f144,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK9(X0,X1,X2),X1)
            | ~ r2_hidden(sK9(X0,X1,X2),X0)
            | ~ r2_hidden(sK9(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
              & r2_hidden(sK9(X0,X1,X2),X0) )
            | r2_hidden(sK9(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f142,f143])).

fof(f143,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK9(X0,X1,X2),X1)
          | ~ r2_hidden(sK9(X0,X1,X2),X0)
          | ~ r2_hidden(sK9(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK9(X0,X1,X2),X1)
            & r2_hidden(sK9(X0,X1,X2),X0) )
          | r2_hidden(sK9(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f142,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f141])).

fof(f141,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f140])).

fof(f140,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',d5_xboole_0)).

fof(f23783,plain,
    ( r2_hidden(o_2_3_yellow19(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f5219,f23772,f193])).

fof(f193,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t2_subset)).

fof(f23772,plain,
    ( ~ v1_xboole_0(k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f281,f23598,f1790])).

fof(f1790,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK7(X4,X5),X5)
      | X4 = X5
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f208,f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t7_boole)).

fof(f208,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r2_hidden(sK7(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f129,f130])).

fof(f130,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK7(X0,X1),X1)
          | ~ r2_hidden(sK7(X0,X1),X0) )
        & ( r2_hidden(sK7(X0,X1),X1)
          | r2_hidden(sK7(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f129,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t2_tarski)).

fof(f23598,plain,
    ( o_0_0_xboole_0 != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f23590,f239])).

fof(f239,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f215,f165])).

fof(f165,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',d2_xboole_0)).

fof(f215,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t37_xboole_1)).

fof(f23590,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl13_63 ),
    inference(avatar_component_clause,[],[f23589])).

fof(f23589,plain,
    ( spl13_63
  <=> ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_63])])).

fof(f281,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(unit_resulting_resolution,[],[f164,f218])).

fof(f164,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',dt_o_0_0_xboole_0)).

fof(f5219,plain,(
    m1_subset_1(o_2_3_yellow19(sK0,sK1),k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f5208,f1572])).

fof(f1572,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f154,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',redefinition_k7_subset_1)).

fof(f5208,plain,(
    m1_subset_1(o_2_3_yellow19(sK0,sK1),k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f154,f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(o_2_3_yellow19(X0,X1),k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',dt_o_2_3_yellow19)).

fof(f24497,plain,
    ( m1_subset_1(o_2_3_yellow19(sK0,sK1),u1_struct_0(sK0))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f1727,f23783,f884])).

fof(f884,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r2_hidden(X0,X2)
      | m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f224,f214])).

fof(f214,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t3_subset)).

fof(f1727,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f1591,f213])).

fof(f213,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f1591,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f1572,f1416])).

fof(f1416,plain,(
    ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f154,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',dt_k7_subset_1)).

fof(f24477,plain,
    ( r2_hidden(o_2_3_yellow19(sK0,sK1),sK1)
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f23783,f245])).

fof(f245,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f225])).

fof(f225,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f144])).

fof(f153,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f152,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f248,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl13_0 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl13_0
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_0])])).

fof(f178041,plain,
    ( ~ spl13_4
    | spl13_7
    | ~ spl13_10
    | ~ spl13_64 ),
    inference(avatar_contradiction_clause,[],[f178040])).

fof(f178040,plain,
    ( $false
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_10
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f177866,f296])).

fof(f296,plain,
    ( r2_waybel_7(sK0,sK3,sK2)
    | ~ spl13_10 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl13_10
  <=> r2_waybel_7(sK0,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_10])])).

fof(f177866,plain,
    ( ~ r2_waybel_7(sK0,sK3,sK2)
    | ~ spl13_4
    | ~ spl13_7
    | ~ spl13_64 ),
    inference(unit_resulting_resolution,[],[f272,f152,f153,f279,f312,f175237,f4958])).

fof(f4958,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(X2))
      | ~ v3_pre_topc(X1,X2)
      | r2_hidden(X1,X3)
      | ~ r2_waybel_7(X2,X3,X0)
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f185,f214])).

fof(f175237,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl13_64 ),
    inference(backward_demodulation,[],[f23596,f91252])).

fof(f91252,plain,(
    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    inference(superposition,[],[f2353,f235])).

fof(f235,plain,(
    ! [X0] : k4_xboole_0(X0,o_0_0_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f166,f165])).

fof(f166,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t3_boole)).

fof(f2353,plain,(
    ! [X0] : v3_pre_topc(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),sK0) ),
    inference(unit_resulting_resolution,[],[f152,f153,f1591,f205])).

fof(f205,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f55])).

fof(f55,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',fc9_tops_1)).

fof(f23596,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ spl13_64 ),
    inference(avatar_component_clause,[],[f23595])).

fof(f23595,plain,
    ( spl13_64
  <=> k1_tops_1(sK0,sK1) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_64])])).

fof(f312,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f154,f213])).

fof(f279,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl13_7 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl13_7
  <=> ~ r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_7])])).

fof(f272,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl13_4 ),
    inference(avatar_component_clause,[],[f271])).

fof(f271,plain,
    ( spl13_4
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_4])])).

fof(f177161,plain,
    ( spl13_1
    | ~ spl13_64 ),
    inference(avatar_contradiction_clause,[],[f177160])).

fof(f177160,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_64 ),
    inference(subsumption_resolution,[],[f175237,f251])).

fof(f251,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl13_1 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl13_1
  <=> ~ v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl13_1])])).

fof(f174927,plain,
    ( spl13_1
    | spl13_63 ),
    inference(avatar_contradiction_clause,[],[f174926])).

fof(f174926,plain,
    ( $false
    | ~ spl13_1
    | ~ spl13_63 ),
    inference(subsumption_resolution,[],[f174793,f44834])).

fof(f44834,plain,
    ( r1_tarski(k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f153,f151,f152,f24497,f4393])).

fof(f4393,plain,(
    ! [X15,X16] :
      ( r1_tarski(k1_yellow19(X16,X15),u1_struct_0(k3_yellow_1(k2_struct_0(X16))))
      | ~ l1_pre_topc(X16)
      | ~ v2_pre_topc(X16)
      | v2_struct_0(X16)
      | ~ m1_subset_1(X15,u1_struct_0(X16)) ) ),
    inference(resolution,[],[f198,f213])).

fof(f174793,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)),u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl13_1
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f24477,f24655,f24841,f24656,f24657,f174785,f69768])).

fof(f69768,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | r2_hidden(sK1,X0)
        | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ r2_hidden(X1,sK1)
        | ~ r2_waybel_7(sK0,X0,X1) )
    | ~ spl13_1 ),
    inference(resolution,[],[f69450,f214])).

fof(f69450,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ r2_waybel_7(sK0,X5,X4)
        | r2_hidden(sK1,X5)
        | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(X5)
        | ~ r2_hidden(X4,sK1) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f69449,f1308])).

fof(f1308,plain,(
    ! [X1] :
      ( m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f1304,f192])).

fof(f192,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t1_subset)).

fof(f1304,plain,(
    ! [X10] :
      ( r2_hidden(X10,u1_struct_0(sK0))
      | ~ r2_hidden(X10,sK1) ) ),
    inference(subsumption_resolution,[],[f1293,f281])).

fof(f1293,plain,(
    ! [X10] :
      ( r2_hidden(X10,o_0_0_xboole_0)
      | r2_hidden(X10,u1_struct_0(sK0))
      | ~ r2_hidden(X10,sK1) ) ),
    inference(superposition,[],[f243,f371])).

fof(f371,plain,(
    o_0_0_xboole_0 = k4_xboole_0(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f312,f238])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | o_0_0_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f216,f165])).

fof(f216,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f243,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f227])).

fof(f227,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f144])).

fof(f69449,plain,
    ( ! [X4,X5] :
        ( r2_hidden(sK1,X5)
        | ~ r2_waybel_7(sK0,X5,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
        | v1_xboole_0(X5)
        | ~ r2_hidden(X4,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl13_1 ),
    inference(subsumption_resolution,[],[f155,f251])).

fof(f155,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK1,X5)
      | ~ r2_waybel_7(sK0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | ~ v2_waybel_0(X5,k3_yellow_1(k2_struct_0(sK0)))
      | v1_xboole_0(X5)
      | ~ r2_hidden(X4,sK1)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f117])).

fof(f24657,plain,
    ( v13_waybel_0(k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f24497,f201])).

fof(f24656,plain,
    ( v2_waybel_0(k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)),k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f24497,f200])).

fof(f200,plain,(
    ! [X0,X1] :
      ( v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f24655,plain,
    ( ~ v1_xboole_0(k1_yellow19(sK0,o_2_3_yellow19(sK0,sK1)))
    | ~ spl13_63 ),
    inference(unit_resulting_resolution,[],[f151,f152,f153,f24497,f199])).

fof(f199,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f23597,plain,
    ( ~ spl13_63
    | spl13_64 ),
    inference(avatar_split_clause,[],[f1464,f23595,f23589])).

fof(f1464,plain,
    ( k1_tops_1(sK0,sK1) = sK1
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1432,f212])).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f133])).

fof(f1432,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f153,f154,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow19__t6_yellow19.p',t44_tops_1)).

fof(f297,plain,
    ( ~ spl13_1
    | spl13_10 ),
    inference(avatar_split_clause,[],[f162,f295,f250])).

fof(f162,plain,
    ( r2_waybel_7(sK0,sK3,sK2)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f280,plain,
    ( ~ spl13_1
    | ~ spl13_7 ),
    inference(avatar_split_clause,[],[f163,f278,f250])).

fof(f163,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f117])).

fof(f273,plain,
    ( ~ spl13_1
    | spl13_4 ),
    inference(avatar_split_clause,[],[f157,f271,f250])).

fof(f157,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f117])).
%------------------------------------------------------------------------------
