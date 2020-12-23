%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  172 (3221 expanded)
%              Number of leaves         :   24 (1008 expanded)
%              Depth                    :   21
%              Number of atoms          :  830 (24934 expanded)
%              Number of equality atoms :    6 ( 225 expanded)
%              Maximal formula depth    :   13 (   7 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f207,f235])).

fof(f235,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f233,f227])).

fof(f227,plain,
    ( r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f111,f223,f225,f221,f194])).

fof(f194,plain,(
    ! [X33,X34,X32] :
      ( ~ v3_pre_topc(X32,sK0)
      | r2_hidden(X32,X33)
      | ~ r2_hidden(X34,X32)
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,X33,X34) ) ),
    inference(subsumption_resolution,[],[f193,f63])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | ~ r2_waybel_7(sK0,sK2,sK1) )
    & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
      | r2_waybel_7(sK0,sK2,sK1) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | r2_waybel_7(X0,X2,X1) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
                | ~ r2_waybel_7(sK0,X2,X1) )
              & ( r1_tarski(k1_yellow19(sK0,X1),X2)
                | r2_waybel_7(sK0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(k1_yellow19(sK0,X1),X2)
              | ~ r2_waybel_7(sK0,X2,X1) )
            & ( r1_tarski(k1_yellow19(sK0,X1),X2)
              | r2_waybel_7(sK0,X2,X1) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
            & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
            | ~ r2_waybel_7(sK0,X2,sK1) )
          & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
            | r2_waybel_7(sK0,X2,sK1) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
          & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),X2)
          | ~ r2_waybel_7(sK0,X2,sK1) )
        & ( r1_tarski(k1_yellow19(sK0,sK1),X2)
          | r2_waybel_7(sK0,X2,sK1) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0))) )
   => ( ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | ~ r2_waybel_7(sK0,sK2,sK1) )
      & ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
        | r2_waybel_7(sK0,sK2,sK1) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
      & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_tarski(k1_yellow19(X0,X1),X2)
                | ~ r2_waybel_7(X0,X2,X1) )
              & ( r1_tarski(k1_yellow19(X0,X1),X2)
                | r2_waybel_7(X0,X2,X1) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <~> r1_tarski(k1_yellow19(X0,X1),X2) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(f193,plain,(
    ! [X33,X34,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X32,X33)
      | ~ r2_hidden(X34,X32)
      | ~ v3_pre_topc(X32,sK0)
      | ~ r2_waybel_7(sK0,X33,X34)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f64])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f163,plain,(
    ! [X33,X34,X32] :
      ( ~ m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X32,X33)
      | ~ r2_hidden(X34,X32)
      | ~ v3_pre_topc(X32,sK0)
      | ~ r2_waybel_7(sK0,X33,X34)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f83,f138])).

fof(f138,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f119,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f119,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f64,f72])).

fof(f72,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).

fof(f51,plain,(
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

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f221,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f216,f184])).

fof(f184,plain,(
    ! [X17,X16] :
      ( m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X17,k1_tops_1(sK0,X16)) ) ),
    inference(subsumption_resolution,[],[f183,f63])).

fof(f183,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X17,k1_tops_1(sK0,X16))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f64])).

fof(f156,plain,(
    ! [X17,X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X17,k1_tops_1(sK0,X16))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f78,f138])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ( r2_hidden(X1,sK3(X0,X1,X2))
                & r1_tarski(sK3(X0,X1,X2),X2)
                & v3_pre_topc(sK3(X0,X1,X2),X0)
                & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X1,X4)
          & r1_tarski(X4,X2)
          & v3_pre_topc(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r2_hidden(X1,sK3(X0,X1,X2))
        & r1_tarski(sK3(X0,X1,X2),X2)
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_hidden(X1,k1_tops_1(X0,X2))
              | ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f216,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK7(k1_yellow19(sK0,sK1),sK2)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f121,f212,f214,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f168,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f168,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f63])).

fof(f167,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f64])).

fof(f148,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | r2_hidden(X0,k1_tops_1(sK0,X1))
      | ~ m1_connsp_2(X1,sK0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f73,f138])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f212,plain,
    ( m1_connsp_2(sK7(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f121,f209,f175])).

fof(f175,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k2_struct_0(sK0))
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8)) ) ),
    inference(subsumption_resolution,[],[f174,f62])).

fof(f174,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k2_struct_0(sK0))
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f63])).

fof(f173,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k2_struct_0(sK0))
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f64])).

fof(f152,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,k2_struct_0(sK0))
      | m1_connsp_2(X9,sK0,X8)
      | ~ r2_hidden(X9,k1_yellow19(sK0,X8))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f75,f138])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(f209,plain,
    ( r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f116,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK7(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f58,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f116,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl9_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f121,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f120,f119])).

fof(f120,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f65,f71])).

fof(f65,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f214,plain,
    ( m1_subset_1(sK7(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f121,f212,f199])).

fof(f199,plain,(
    ! [X37,X38] :
      ( m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X37,sK0,X38)
      | ~ m1_subset_1(X38,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f198,f62])).

fof(f198,plain,(
    ! [X37,X38] :
      ( m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X37,sK0,X38)
      | ~ m1_subset_1(X38,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f197,f63])).

fof(f197,plain,(
    ! [X37,X38] :
      ( m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X37,sK0,X38)
      | ~ m1_subset_1(X38,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f165,f64])).

fof(f165,plain,(
    ! [X37,X38] :
      ( m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X37,sK0,X38)
      | ~ m1_subset_1(X38,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f93,f138])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f225,plain,
    ( v3_pre_topc(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK0)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f216,f186])).

fof(f186,plain,(
    ! [X21,X20] :
      ( v3_pre_topc(sK3(sK0,X21,X20),sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X21,k1_tops_1(sK0,X20)) ) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f185,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(sK3(sK0,X21,X20),sK0)
      | ~ r2_hidden(X21,k1_tops_1(sK0,X20))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f64])).

fof(f158,plain,(
    ! [X21,X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(sK3(sK0,X21,X20),sK0)
      | ~ r2_hidden(X21,k1_tops_1(sK0,X20))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f79,f138])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f223,plain,
    ( r2_hidden(sK1,sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f216,f190])).

fof(f190,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X25,sK3(sK0,X25,X24))
      | ~ r2_hidden(X25,k1_tops_1(sK0,X24)) ) ),
    inference(subsumption_resolution,[],[f189,f63])).

fof(f189,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X25,sK3(sK0,X25,X24))
      | ~ r2_hidden(X25,k1_tops_1(sK0,X24))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f64])).

fof(f160,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X25,sK3(sK0,X25,X24))
      | ~ r2_hidden(X25,k1_tops_1(sK0,X24))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f81,f138])).

% (28878)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f111,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl9_1
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f233,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f220,f224,f107])).

fof(f107,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X4,X5)
      | sP8(X5,X1) ) ),
    inference(cnf_transformation,[],[f107_D])).

fof(f107_D,plain,(
    ! [X1,X5] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X5) )
    <=> ~ sP8(X5,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).

fof(f224,plain,
    ( r1_tarski(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK7(k1_yellow19(sK0,sK1),sK2))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f216,f188])).

fof(f188,plain,(
    ! [X23,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(sK3(sK0,X23,X22),X22)
      | ~ r2_hidden(X23,k1_tops_1(sK0,X22)) ) ),
    inference(subsumption_resolution,[],[f187,f63])).

fof(f187,plain,(
    ! [X23,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(sK3(sK0,X23,X22),X22)
      | ~ r2_hidden(X23,k1_tops_1(sK0,X22))
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f159,f64])).

fof(f159,plain,(
    ! [X23,X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(sK3(sK0,X23,X22),X22)
      | ~ r2_hidden(X23,k1_tops_1(sK0,X22))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f80,f138])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f220,plain,
    ( ~ sP8(sK7(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f101,f210,f100,f217,f108])).

fof(f108,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_tarski(X5,X0)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ sP8(X5,X1) ) ),
    inference(general_splitting,[],[f106,f107_D])).

fof(f106,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f88,f70,f70])).

fof(f70,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f88,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK6(X0,X1),X1)
            & r2_hidden(sK5(X0,X1),X1)
            & r1_tarski(sK6(X0,X1),X0)
            & r1_tarski(sK5(X0,X1),sK6(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X1)
        & r1_tarski(sK6(X0,X1),X0)
        & r1_tarski(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ? [X2,X3] :
              ( ~ r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) ) )
        & ( ! [X2,X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1)
              | ~ r1_tarski(X3,X0)
              | ~ r1_tarski(X2,X3) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f217,plain,
    ( r1_tarski(sK7(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f214,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f100,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f67,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f42])).

fof(f210,plain,
    ( ~ r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f116,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK7(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f101,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f66,f70])).

fof(f66,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f207,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f205,f204])).

fof(f204,plain,
    ( ~ m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f142,f121,f178])).

fof(f178,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X11,k1_yellow19(sK0,X10))
      | ~ m1_connsp_2(X11,sK0,X10) ) ),
    inference(subsumption_resolution,[],[f177,f62])).

fof(f177,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X11,k1_yellow19(sK0,X10))
      | ~ m1_connsp_2(X11,sK0,X10)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X11,k1_yellow19(sK0,X10))
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f64])).

fof(f153,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k2_struct_0(sK0))
      | r2_hidden(X11,k1_yellow19(sK0,X10))
      | ~ m1_connsp_2(X11,sK0,X10)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f76,f138])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f142,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f115,f125,f94])).

fof(f94,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f125,plain,
    ( ~ r2_hidden(sK4(sK0,sK2,sK1),sK2)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f112,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f112,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f115,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f205,plain,
    ( m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f124,f123,f139,f182])).

fof(f182,plain,(
    ! [X12,X13] :
      ( ~ v3_pre_topc(X12,sK0)
      | m1_connsp_2(X12,sK0,X13)
      | ~ r2_hidden(X13,X12)
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f181,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f181,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X12,sK0,X13)
      | ~ r2_hidden(X13,X12)
      | ~ v3_pre_topc(X12,sK0)
      | ~ m1_subset_1(X13,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f180,f62])).

fof(f180,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X12,sK0,X13)
      | ~ r2_hidden(X13,X12)
      | ~ v3_pre_topc(X12,sK0)
      | ~ m1_subset_1(X13,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f179,f63])).

fof(f179,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X12,sK0,X13)
      | ~ r2_hidden(X13,X12)
      | ~ v3_pre_topc(X12,sK0)
      | ~ m1_subset_1(X13,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f64])).

fof(f154,plain,(
    ! [X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X12,sK0,X13)
      | ~ r2_hidden(X13,X12)
      | ~ v3_pre_topc(X12,sK0)
      | ~ m1_subset_1(X13,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f138])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f139,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl9_1 ),
    inference(backward_demodulation,[],[f122,f138])).

fof(f122,plain,
    ( m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f112,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f123,plain,
    ( v3_pre_topc(sK4(sK0,sK2,sK1),sK0)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f112,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f124,plain,
    ( r2_hidden(sK1,sK4(sK0,sK2,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f63,f64,f112,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f118,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f68,f114,f110])).

fof(f68,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f117,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f69,f114,f110])).

fof(f69,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:14:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (28863)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.19/0.50  % (28876)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.19/0.50  % (28868)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.50  % (28879)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.19/0.50  % (28860)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.51  % (28876)Refutation not found, incomplete strategy% (28876)------------------------------
% 0.19/0.51  % (28876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (28871)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.19/0.51  % (28876)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (28876)Memory used [KB]: 10746
% 0.19/0.51  % (28876)Time elapsed: 0.055 s
% 0.19/0.51  % (28876)------------------------------
% 0.19/0.51  % (28876)------------------------------
% 0.19/0.51  % (28866)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.51  % (28867)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.52  % (28856)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.53  % (28874)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.19/0.53  % (28857)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.53  % (28854)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.53  % (28858)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.53  % (28855)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.53  % (28859)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.53  % (28872)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.19/0.54  % (28881)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.19/0.54  % (28877)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.54  % (28870)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.54  % (28864)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.54  % (28882)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.54  % (28869)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.54  % (28873)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.19/0.54  % (28883)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.19/0.54  % (28862)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.55  % (28861)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.55  % (28865)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.19/0.55  % (28875)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.55  % (28880)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.56  % (28880)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f236,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f117,f118,f207,f235])).
% 0.19/0.56  fof(f235,plain,(
% 0.19/0.56    ~spl9_1 | spl9_2),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f234])).
% 0.19/0.56  fof(f234,plain,(
% 0.19/0.56    $false | (~spl9_1 | spl9_2)),
% 0.19/0.56    inference(subsumption_resolution,[],[f233,f227])).
% 0.19/0.56  fof(f227,plain,(
% 0.19/0.56    r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2) | (~spl9_1 | spl9_2)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f111,f223,f225,f221,f194])).
% 0.19/0.56  fof(f194,plain,(
% 0.19/0.56    ( ! [X33,X34,X32] : (~v3_pre_topc(X32,sK0) | r2_hidden(X32,X33) | ~r2_hidden(X34,X32) | ~m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_waybel_7(sK0,X33,X34)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f193,f63])).
% 0.19/0.56  fof(f63,plain,(
% 0.19/0.56    v2_pre_topc(sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f42])).
% 0.19/0.56  fof(f42,plain,(
% 0.19/0.56    (((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).
% 0.19/0.56  fof(f39,plain,(
% 0.19/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f40,plain,(
% 0.19/0.56    ? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f41,plain,(
% 0.19/0.56    ? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) => ((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f38,plain,(
% 0.19/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.56    inference(flattening,[],[f37])).
% 0.19/0.56  fof(f37,plain,(
% 0.19/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f17])).
% 0.19/0.56  fof(f17,plain,(
% 0.19/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.56    inference(flattening,[],[f16])).
% 0.19/0.56  fof(f16,plain,(
% 0.19/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f15])).
% 0.19/0.56  fof(f15,negated_conjecture,(
% 0.19/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.19/0.56    inference(negated_conjecture,[],[f14])).
% 0.19/0.56  fof(f14,conjecture,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).
% 0.19/0.56  fof(f193,plain,(
% 0.19/0.56    ( ! [X33,X34,X32] : (~m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X32,X33) | ~r2_hidden(X34,X32) | ~v3_pre_topc(X32,sK0) | ~r2_waybel_7(sK0,X33,X34) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f163,f64])).
% 0.19/0.56  fof(f64,plain,(
% 0.19/0.56    l1_pre_topc(sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f42])).
% 0.19/0.56  fof(f163,plain,(
% 0.19/0.56    ( ! [X33,X34,X32] : (~m1_subset_1(X32,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X32,X33) | ~r2_hidden(X34,X32) | ~v3_pre_topc(X32,sK0) | ~r2_waybel_7(sK0,X33,X34) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f83,f138])).
% 0.19/0.56  fof(f138,plain,(
% 0.19/0.56    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f119,f71])).
% 0.19/0.56  fof(f71,plain,(
% 0.19/0.56    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f18])).
% 0.19/0.56  fof(f18,plain,(
% 0.19/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f4])).
% 0.19/0.56  fof(f4,axiom,(
% 0.19/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.19/0.56  fof(f119,plain,(
% 0.19/0.56    l1_struct_0(sK0)),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f64,f72])).
% 0.19/0.56  fof(f72,plain,(
% 0.19/0.56    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f19])).
% 0.19/0.56  fof(f19,plain,(
% 0.19/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.56    inference(ennf_transformation,[],[f5])).
% 0.19/0.56  fof(f5,axiom,(
% 0.19/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.56  fof(f83,plain,(
% 0.19/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f52])).
% 0.19/0.56  fof(f52,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f50,f51])).
% 0.19/0.56  fof(f51,plain,(
% 0.19/0.56    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(X2,sK4(X0,X1,X2)) & v3_pre_topc(sK4(X0,X1,X2),X0) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f50,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(rectify,[],[f49])).
% 0.19/0.56  fof(f49,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f29])).
% 0.19/0.56  fof(f29,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(flattening,[],[f28])).
% 0.19/0.56  fof(f28,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f11])).
% 0.19/0.56  fof(f11,axiom,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.19/0.56  fof(f221,plain,(
% 0.19/0.56    m1_subset_1(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f214,f216,f184])).
% 0.19/0.56  fof(f184,plain,(
% 0.19/0.56    ( ! [X17,X16] : (m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X17,k1_tops_1(sK0,X16))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f183,f63])).
% 0.19/0.56  fof(f183,plain,(
% 0.19/0.56    ( ! [X17,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X17,k1_tops_1(sK0,X16)) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f156,f64])).
% 0.19/0.56  fof(f156,plain,(
% 0.19/0.56    ( ! [X17,X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(sK3(sK0,X17,X16),k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X17,k1_tops_1(sK0,X16)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f78,f138])).
% 0.19/0.56  fof(f78,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f48])).
% 0.19/0.56  fof(f48,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & ((r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 0.19/0.56  fof(f47,plain,(
% 0.19/0.56    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (r2_hidden(X1,sK3(X0,X1,X2)) & r1_tarski(sK3(X0,X1,X2),X2) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f46,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(rectify,[],[f45])).
% 0.19/0.56  fof(f45,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : (((r2_hidden(X1,k1_tops_1(X0,X2)) | ! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f27])).
% 0.19/0.56  fof(f27,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.56    inference(flattening,[],[f26])).
% 0.19/0.56  fof(f26,plain,(
% 0.19/0.56    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,axiom,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 0.19/0.56  fof(f216,plain,(
% 0.19/0.56    r2_hidden(sK1,k1_tops_1(sK0,sK7(k1_yellow19(sK0,sK1),sK2))) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f121,f212,f214,f169])).
% 0.19/0.56  fof(f169,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f168,f62])).
% 0.19/0.56  fof(f62,plain,(
% 0.19/0.56    ~v2_struct_0(sK0)),
% 0.19/0.56    inference(cnf_transformation,[],[f42])).
% 0.19/0.56  fof(f168,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f167,f63])).
% 0.19/0.56  fof(f167,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f148,f64])).
% 0.19/0.56  fof(f148,plain,(
% 0.19/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k2_struct_0(sK0)) | r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f73,f138])).
% 0.19/0.56  fof(f73,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f43])).
% 0.19/0.56  fof(f43,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f21])).
% 0.19/0.56  fof(f21,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.56    inference(flattening,[],[f20])).
% 0.19/0.56  fof(f20,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f7])).
% 0.19/0.56  fof(f7,axiom,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.19/0.56  fof(f212,plain,(
% 0.19/0.56    m1_connsp_2(sK7(k1_yellow19(sK0,sK1),sK2),sK0,sK1) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f121,f209,f175])).
% 0.19/0.56  fof(f175,plain,(
% 0.19/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k2_struct_0(sK0)) | m1_connsp_2(X9,sK0,X8) | ~r2_hidden(X9,k1_yellow19(sK0,X8))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f174,f62])).
% 0.19/0.56  fof(f174,plain,(
% 0.19/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k2_struct_0(sK0)) | m1_connsp_2(X9,sK0,X8) | ~r2_hidden(X9,k1_yellow19(sK0,X8)) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f173,f63])).
% 0.19/0.56  fof(f173,plain,(
% 0.19/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k2_struct_0(sK0)) | m1_connsp_2(X9,sK0,X8) | ~r2_hidden(X9,k1_yellow19(sK0,X8)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f152,f64])).
% 0.19/0.56  fof(f152,plain,(
% 0.19/0.56    ( ! [X8,X9] : (~m1_subset_1(X8,k2_struct_0(sK0)) | m1_connsp_2(X9,sK0,X8) | ~r2_hidden(X9,k1_yellow19(sK0,X8)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f75,f138])).
% 0.19/0.56  fof(f75,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f44])).
% 0.19/0.56  fof(f44,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.56    inference(nnf_transformation,[],[f23])).
% 0.19/0.56  fof(f23,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.56    inference(flattening,[],[f22])).
% 0.19/0.56  fof(f22,plain,(
% 0.19/0.56    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f13])).
% 0.19/0.56  fof(f13,axiom,(
% 0.19/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).
% 0.19/0.56  fof(f209,plain,(
% 0.19/0.56    r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1)) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f116,f95])).
% 0.19/0.56  fof(f95,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK7(X0,X1),X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f60])).
% 0.19/0.56  fof(f60,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f58,f59])).
% 0.19/0.56  fof(f59,plain,(
% 0.19/0.56    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 0.19/0.56    introduced(choice_axiom,[])).
% 0.19/0.56  fof(f58,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(rectify,[],[f57])).
% 0.19/0.56  fof(f57,plain,(
% 0.19/0.56    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.19/0.56    inference(nnf_transformation,[],[f34])).
% 0.19/0.56  fof(f34,plain,(
% 0.19/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f1])).
% 0.19/0.56  fof(f1,axiom,(
% 0.19/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.56  fof(f116,plain,(
% 0.19/0.56    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | spl9_2),
% 0.19/0.56    inference(avatar_component_clause,[],[f114])).
% 0.19/0.56  fof(f114,plain,(
% 0.19/0.56    spl9_2 <=> r1_tarski(k1_yellow19(sK0,sK1),sK2)),
% 0.19/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.19/0.56  fof(f121,plain,(
% 0.19/0.56    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.19/0.56    inference(subsumption_resolution,[],[f120,f119])).
% 0.19/0.56  fof(f120,plain,(
% 0.19/0.56    m1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 0.19/0.56    inference(superposition,[],[f65,f71])).
% 0.19/0.56  fof(f65,plain,(
% 0.19/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.56    inference(cnf_transformation,[],[f42])).
% 0.19/0.56  fof(f214,plain,(
% 0.19/0.56    m1_subset_1(sK7(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f121,f212,f199])).
% 0.19/0.56  fof(f199,plain,(
% 0.19/0.56    ( ! [X37,X38] : (m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X37,sK0,X38) | ~m1_subset_1(X38,k2_struct_0(sK0))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f198,f62])).
% 0.19/0.56  fof(f198,plain,(
% 0.19/0.56    ( ! [X37,X38] : (m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X37,sK0,X38) | ~m1_subset_1(X38,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f197,f63])).
% 0.19/0.56  fof(f197,plain,(
% 0.19/0.56    ( ! [X37,X38] : (m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X37,sK0,X38) | ~m1_subset_1(X38,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f165,f64])).
% 0.19/0.56  fof(f165,plain,(
% 0.19/0.56    ( ! [X37,X38] : (m1_subset_1(X37,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X37,sK0,X38) | ~m1_subset_1(X38,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f93,f138])).
% 0.19/0.56  fof(f93,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f33])).
% 0.19/0.56  fof(f33,plain,(
% 0.19/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.56    inference(flattening,[],[f32])).
% 0.19/0.56  fof(f32,plain,(
% 0.19/0.56    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f8])).
% 0.19/0.56  fof(f8,axiom,(
% 0.19/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 0.19/0.56  fof(f225,plain,(
% 0.19/0.56    v3_pre_topc(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK0) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f214,f216,f186])).
% 0.19/0.56  fof(f186,plain,(
% 0.19/0.56    ( ! [X21,X20] : (v3_pre_topc(sK3(sK0,X21,X20),sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X21,k1_tops_1(sK0,X20))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f185,f63])).
% 0.19/0.56  fof(f185,plain,(
% 0.19/0.56    ( ! [X21,X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK3(sK0,X21,X20),sK0) | ~r2_hidden(X21,k1_tops_1(sK0,X20)) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f158,f64])).
% 0.19/0.56  fof(f158,plain,(
% 0.19/0.56    ( ! [X21,X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK3(sK0,X21,X20),sK0) | ~r2_hidden(X21,k1_tops_1(sK0,X20)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f79,f138])).
% 0.19/0.56  fof(f79,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (v3_pre_topc(sK3(X0,X1,X2),X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f48])).
% 0.19/0.56  fof(f223,plain,(
% 0.19/0.56    r2_hidden(sK1,sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2))) | spl9_2),
% 0.19/0.56    inference(unit_resulting_resolution,[],[f214,f216,f190])).
% 0.19/0.56  fof(f190,plain,(
% 0.19/0.56    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X25,sK3(sK0,X25,X24)) | ~r2_hidden(X25,k1_tops_1(sK0,X24))) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f189,f63])).
% 0.19/0.56  fof(f189,plain,(
% 0.19/0.56    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X25,sK3(sK0,X25,X24)) | ~r2_hidden(X25,k1_tops_1(sK0,X24)) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(subsumption_resolution,[],[f160,f64])).
% 0.19/0.56  fof(f160,plain,(
% 0.19/0.56    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X25,sK3(sK0,X25,X24)) | ~r2_hidden(X25,k1_tops_1(sK0,X24)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 0.19/0.56    inference(superposition,[],[f81,f138])).
% 0.19/0.56  % (28878)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.58  fof(f81,plain,(
% 1.58/0.58    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.58/0.58    inference(cnf_transformation,[],[f48])).
% 1.58/0.58  fof(f111,plain,(
% 1.58/0.58    r2_waybel_7(sK0,sK2,sK1) | ~spl9_1),
% 1.58/0.58    inference(avatar_component_clause,[],[f110])).
% 1.58/0.58  fof(f110,plain,(
% 1.58/0.58    spl9_1 <=> r2_waybel_7(sK0,sK2,sK1)),
% 1.58/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.58/0.58  fof(f233,plain,(
% 1.58/0.58    ~r2_hidden(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK2) | spl9_2),
% 1.58/0.58    inference(unit_resulting_resolution,[],[f220,f224,f107])).
% 1.74/0.58  fof(f107,plain,(
% 1.74/0.58    ( ! [X4,X5,X1] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5) | sP8(X5,X1)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f107_D])).
% 1.74/0.58  fof(f107_D,plain,(
% 1.74/0.58    ( ! [X1,X5] : (( ! [X4] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5)) ) <=> ~sP8(X5,X1)) )),
% 1.74/0.58    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP8])])).
% 1.74/0.58  fof(f224,plain,(
% 1.74/0.58    r1_tarski(sK3(sK0,sK1,sK7(k1_yellow19(sK0,sK1),sK2)),sK7(k1_yellow19(sK0,sK1),sK2)) | spl9_2),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f214,f216,f188])).
% 1.74/0.58  fof(f188,plain,(
% 1.74/0.58    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK3(sK0,X23,X22),X22) | ~r2_hidden(X23,k1_tops_1(sK0,X22))) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f187,f63])).
% 1.74/0.58  fof(f187,plain,(
% 1.74/0.58    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK3(sK0,X23,X22),X22) | ~r2_hidden(X23,k1_tops_1(sK0,X22)) | ~v2_pre_topc(sK0)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f159,f64])).
% 1.74/0.58  fof(f159,plain,(
% 1.74/0.58    ( ! [X23,X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(sK3(sK0,X23,X22),X22) | ~r2_hidden(X23,k1_tops_1(sK0,X22)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.74/0.58    inference(superposition,[],[f80,f138])).
% 1.74/0.58  fof(f80,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f48])).
% 1.74/0.58  fof(f220,plain,(
% 1.74/0.58    ~sP8(sK7(k1_yellow19(sK0,sK1),sK2),sK2) | spl9_2),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f101,f210,f100,f217,f108])).
% 1.74/0.58  fof(f108,plain,(
% 1.74/0.58    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X0) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~sP8(X5,X1)) )),
% 1.74/0.58    inference(general_splitting,[],[f106,f107_D])).
% 1.74/0.58  fof(f106,plain,(
% 1.74/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 1.74/0.58    inference(definition_unfolding,[],[f88,f70,f70])).
% 1.74/0.58  fof(f70,plain,(
% 1.74/0.58    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f10])).
% 1.74/0.58  fof(f10,axiom,(
% 1.74/0.58    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.74/0.58  fof(f88,plain,(
% 1.74/0.58    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f56])).
% 1.74/0.58  fof(f56,plain,(
% 1.74/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r1_tarski(sK6(X0,X1),X0) & r1_tarski(sK5(X0,X1),sK6(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.74/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f54,f55])).
% 1.74/0.58  fof(f55,plain,(
% 1.74/0.58    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK5(X0,X1),X1) & r1_tarski(sK6(X0,X1),X0) & r1_tarski(sK5(X0,X1),sK6(X0,X1))))),
% 1.74/0.58    introduced(choice_axiom,[])).
% 1.74/0.58  fof(f54,plain,(
% 1.74/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.74/0.58    inference(rectify,[],[f53])).
% 1.74/0.58  fof(f53,plain,(
% 1.74/0.58    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.74/0.58    inference(nnf_transformation,[],[f31])).
% 1.74/0.58  fof(f31,plain,(
% 1.74/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.74/0.58    inference(flattening,[],[f30])).
% 1.74/0.58  fof(f30,plain,(
% 1.74/0.58    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.74/0.58    inference(ennf_transformation,[],[f12])).
% 1.74/0.58  fof(f12,axiom,(
% 1.74/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 1.74/0.58  fof(f217,plain,(
% 1.74/0.58    r1_tarski(sK7(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0)) | spl9_2),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f214,f97])).
% 1.74/0.58  fof(f97,plain,(
% 1.74/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.74/0.58    inference(cnf_transformation,[],[f61])).
% 1.74/0.58  fof(f61,plain,(
% 1.74/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.74/0.58    inference(nnf_transformation,[],[f2])).
% 1.74/0.58  fof(f2,axiom,(
% 1.74/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.74/0.58  fof(f100,plain,(
% 1.74/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.74/0.58    inference(definition_unfolding,[],[f67,f70])).
% 1.74/0.58  fof(f67,plain,(
% 1.74/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.74/0.58    inference(cnf_transformation,[],[f42])).
% 1.74/0.58  fof(f210,plain,(
% 1.74/0.58    ~r2_hidden(sK7(k1_yellow19(sK0,sK1),sK2),sK2) | spl9_2),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f116,f96])).
% 1.74/0.58  fof(f96,plain,(
% 1.74/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK7(X0,X1),X1)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f60])).
% 1.74/0.58  fof(f101,plain,(
% 1.74/0.58    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.74/0.58    inference(definition_unfolding,[],[f66,f70])).
% 1.74/0.58  fof(f66,plain,(
% 1.74/0.58    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 1.74/0.58    inference(cnf_transformation,[],[f42])).
% 1.74/0.58  fof(f207,plain,(
% 1.74/0.58    spl9_1 | ~spl9_2),
% 1.74/0.58    inference(avatar_contradiction_clause,[],[f206])).
% 1.74/0.58  fof(f206,plain,(
% 1.74/0.58    $false | (spl9_1 | ~spl9_2)),
% 1.74/0.58    inference(subsumption_resolution,[],[f205,f204])).
% 1.74/0.58  fof(f204,plain,(
% 1.74/0.58    ~m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1) | (spl9_1 | ~spl9_2)),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f142,f121,f178])).
% 1.74/0.58  fof(f178,plain,(
% 1.74/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X11,k1_yellow19(sK0,X10)) | ~m1_connsp_2(X11,sK0,X10)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f177,f62])).
% 1.74/0.58  fof(f177,plain,(
% 1.74/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X11,k1_yellow19(sK0,X10)) | ~m1_connsp_2(X11,sK0,X10) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f176,f63])).
% 1.74/0.58  fof(f176,plain,(
% 1.74/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X11,k1_yellow19(sK0,X10)) | ~m1_connsp_2(X11,sK0,X10) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f153,f64])).
% 1.74/0.58  fof(f153,plain,(
% 1.74/0.58    ( ! [X10,X11] : (~m1_subset_1(X10,k2_struct_0(sK0)) | r2_hidden(X11,k1_yellow19(sK0,X10)) | ~m1_connsp_2(X11,sK0,X10) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(superposition,[],[f76,f138])).
% 1.74/0.58  fof(f76,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f44])).
% 1.74/0.58  fof(f142,plain,(
% 1.74/0.58    ~r2_hidden(sK4(sK0,sK2,sK1),k1_yellow19(sK0,sK1)) | (spl9_1 | ~spl9_2)),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f115,f125,f94])).
% 1.74/0.58  fof(f94,plain,(
% 1.74/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f60])).
% 1.74/0.58  fof(f125,plain,(
% 1.74/0.58    ~r2_hidden(sK4(sK0,sK2,sK1),sK2) | spl9_1),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f63,f64,f112,f87])).
% 1.74/0.58  fof(f87,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f52])).
% 1.74/0.58  fof(f112,plain,(
% 1.74/0.58    ~r2_waybel_7(sK0,sK2,sK1) | spl9_1),
% 1.74/0.58    inference(avatar_component_clause,[],[f110])).
% 1.74/0.58  fof(f115,plain,(
% 1.74/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~spl9_2),
% 1.74/0.58    inference(avatar_component_clause,[],[f114])).
% 1.74/0.58  fof(f205,plain,(
% 1.74/0.58    m1_connsp_2(sK4(sK0,sK2,sK1),sK0,sK1) | spl9_1),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f124,f123,f139,f182])).
% 1.74/0.58  fof(f182,plain,(
% 1.74/0.58    ( ! [X12,X13] : (~v3_pre_topc(X12,sK0) | m1_connsp_2(X12,sK0,X13) | ~r2_hidden(X13,X12) | ~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f181,f99])).
% 1.74/0.58  fof(f99,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f36])).
% 1.74/0.58  fof(f36,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.74/0.58    inference(flattening,[],[f35])).
% 1.74/0.58  fof(f35,plain,(
% 1.74/0.58    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.74/0.58    inference(ennf_transformation,[],[f3])).
% 1.74/0.58  fof(f3,axiom,(
% 1.74/0.58    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.74/0.58  fof(f181,plain,(
% 1.74/0.58    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X12,sK0,X13) | ~r2_hidden(X13,X12) | ~v3_pre_topc(X12,sK0) | ~m1_subset_1(X13,k2_struct_0(sK0))) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f180,f62])).
% 1.74/0.58  fof(f180,plain,(
% 1.74/0.58    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X12,sK0,X13) | ~r2_hidden(X13,X12) | ~v3_pre_topc(X12,sK0) | ~m1_subset_1(X13,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f179,f63])).
% 1.74/0.58  fof(f179,plain,(
% 1.74/0.58    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X12,sK0,X13) | ~r2_hidden(X13,X12) | ~v3_pre_topc(X12,sK0) | ~m1_subset_1(X13,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(subsumption_resolution,[],[f154,f64])).
% 1.74/0.58  fof(f154,plain,(
% 1.74/0.58    ( ! [X12,X13] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X12,sK0,X13) | ~r2_hidden(X13,X12) | ~v3_pre_topc(X12,sK0) | ~m1_subset_1(X13,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.74/0.58    inference(superposition,[],[f77,f138])).
% 1.74/0.58  fof(f77,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f25])).
% 1.74/0.58  fof(f25,plain,(
% 1.74/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.74/0.58    inference(flattening,[],[f24])).
% 1.74/0.58  fof(f24,plain,(
% 1.74/0.58    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.74/0.58    inference(ennf_transformation,[],[f9])).
% 1.74/0.58  fof(f9,axiom,(
% 1.74/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.74/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.74/0.58  fof(f139,plain,(
% 1.74/0.58    m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl9_1),
% 1.74/0.58    inference(backward_demodulation,[],[f122,f138])).
% 1.74/0.58  fof(f122,plain,(
% 1.74/0.58    m1_subset_1(sK4(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl9_1),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f63,f64,f112,f84])).
% 1.74/0.58  fof(f84,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f52])).
% 1.74/0.58  fof(f123,plain,(
% 1.74/0.58    v3_pre_topc(sK4(sK0,sK2,sK1),sK0) | spl9_1),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f63,f64,f112,f85])).
% 1.74/0.58  fof(f85,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK4(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f52])).
% 1.74/0.58  fof(f124,plain,(
% 1.74/0.58    r2_hidden(sK1,sK4(sK0,sK2,sK1)) | spl9_1),
% 1.74/0.58    inference(unit_resulting_resolution,[],[f63,f64,f112,f86])).
% 1.74/0.58  fof(f86,plain,(
% 1.74/0.58    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK4(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.74/0.58    inference(cnf_transformation,[],[f52])).
% 1.74/0.58  fof(f118,plain,(
% 1.74/0.58    spl9_1 | spl9_2),
% 1.74/0.58    inference(avatar_split_clause,[],[f68,f114,f110])).
% 1.74/0.58  fof(f68,plain,(
% 1.74/0.58    r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)),
% 1.74/0.58    inference(cnf_transformation,[],[f42])).
% 1.74/0.58  fof(f117,plain,(
% 1.74/0.58    ~spl9_1 | ~spl9_2),
% 1.74/0.58    inference(avatar_split_clause,[],[f69,f114,f110])).
% 1.74/0.58  fof(f69,plain,(
% 1.74/0.58    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)),
% 1.74/0.58    inference(cnf_transformation,[],[f42])).
% 1.74/0.58  % SZS output end Proof for theBenchmark
% 1.74/0.58  % (28880)------------------------------
% 1.74/0.58  % (28880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.58  % (28880)Termination reason: Refutation
% 1.74/0.58  
% 1.74/0.58  % (28880)Memory used [KB]: 10874
% 1.74/0.58  % (28880)Time elapsed: 0.155 s
% 1.74/0.58  % (28880)------------------------------
% 1.74/0.58  % (28880)------------------------------
% 1.74/0.58  % (28853)Success in time 0.228 s
%------------------------------------------------------------------------------
