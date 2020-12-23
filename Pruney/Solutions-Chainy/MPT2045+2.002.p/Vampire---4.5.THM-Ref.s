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
% DateTime   : Thu Dec  3 13:23:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  166 (1763 expanded)
%              Number of leaves         :   25 ( 554 expanded)
%              Depth                    :   21
%              Number of atoms          :  745 (13526 expanded)
%              Number of equality atoms :    6 ( 123 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f230,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f116,f117,f200,f229])).

fof(f229,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f227,f220])).

fof(f220,plain,
    ( r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f110,f210,f211,f212,f181])).

fof(f181,plain,(
    ! [X19,X17,X18] :
      ( ~ v3_pre_topc(X17,sK0)
      | r2_hidden(X17,X18)
      | ~ r2_hidden(X19,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_waybel_7(sK0,X18,X19) ) ),
    inference(subsumption_resolution,[],[f180,f64])).

fof(f64,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f180,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X17,X18)
      | ~ r2_hidden(X19,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ r2_waybel_7(sK0,X18,X19)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f156,f65])).

fof(f65,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f156,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | r2_hidden(X17,X18)
      | ~ r2_hidden(X19,X17)
      | ~ v3_pre_topc(X17,sK0)
      | ~ r2_waybel_7(sK0,X18,X19)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f80,f137])).

fof(f137,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f118,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f118,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f65,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X2,X4)
      | ~ v3_pre_topc(X4,X0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_waybel_7(X0,X1,X2)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_waybel_7(X0,X1,X2)
            | ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(X2,sK3(X0,X1,X2))
              & v3_pre_topc(sK3(X0,X1,X2),X0)
              & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) )
          & ( ! [X4] :
                ( r2_hidden(X4,X1)
                | ~ r2_hidden(X2,X4)
                | ~ v3_pre_topc(X4,X0)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_waybel_7(X0,X1,X2) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X3)
          & v3_pre_topc(X3,X0)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(X2,sK3(X0,X1,X2))
        & v3_pre_topc(sK3(X0,X1,X2),X0)
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f212,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f207,f189])).

fof(f189,plain,(
    ! [X27] :
      ( m1_subset_1(k1_tops_1(sK0,X27),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f161,f65])).

fof(f161,plain,(
    ! [X27] :
      ( m1_subset_1(k1_tops_1(sK0,X27),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f92,f137])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f207,plain,
    ( m1_subset_1(sK6(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f120,f205,f186])).

fof(f186,plain,(
    ! [X23,X22] :
      ( ~ m1_subset_1(X23,k2_struct_0(sK0))
      | ~ m1_connsp_2(X22,sK0,X23)
      | m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f185,plain,(
    ! [X23,X22] :
      ( m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X22,sK0,X23)
      | ~ m1_subset_1(X23,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f184,f64])).

fof(f184,plain,(
    ! [X23,X22] :
      ( m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X22,sK0,X23)
      | ~ m1_subset_1(X23,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f158,f65])).

fof(f158,plain,(
    ! [X23,X22] :
      ( m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_connsp_2(X22,sK0,X23)
      | ~ m1_subset_1(X23,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f90,f137])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f205,plain,
    ( m1_connsp_2(sK6(k1_yellow19(sK0,sK1),sK2),sK0,sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f120,f202,f172])).

fof(f172,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k2_struct_0(sK0))
      | m1_connsp_2(X10,sK0,X9)
      | ~ r2_hidden(X10,k1_yellow19(sK0,X9)) ) ),
    inference(subsumption_resolution,[],[f171,f63])).

fof(f171,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k2_struct_0(sK0))
      | m1_connsp_2(X10,sK0,X9)
      | ~ r2_hidden(X10,k1_yellow19(sK0,X9))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f170,f64])).

fof(f170,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k2_struct_0(sK0))
      | m1_connsp_2(X10,sK0,X9)
      | ~ r2_hidden(X10,k1_yellow19(sK0,X9))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f65])).

fof(f152,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k2_struct_0(sK0))
      | m1_connsp_2(X10,sK0,X9)
      | ~ r2_hidden(X10,k1_yellow19(sK0,X9))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f77,f137])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f202,plain,
    ( r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f115,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK6(X0,X1),X1)
          & r2_hidden(sK6(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK6(X0,X1),X1)
        & r2_hidden(sK6(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f115,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl8_2
  <=> r1_tarski(k1_yellow19(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f120,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f119,f118])).

fof(f119,plain,
    ( m1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f66,f72])).

fof(f66,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f211,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f207,f188])).

fof(f188,plain,(
    ! [X26] :
      ( v3_pre_topc(k1_tops_1(sK0,X26),sK0)
      | ~ m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f187,f64])).

fof(f187,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X26),sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(subsumption_resolution,[],[f160,f65])).

fof(f160,plain,(
    ! [X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k1_tops_1(sK0,X26),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0) ) ),
    inference(superposition,[],[f91,f137])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f210,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f120,f205,f207,f166])).

fof(f166,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X2))
      | ~ m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f165,f63])).

fof(f165,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X2))
      | ~ m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f64])).

fof(f164,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X2))
      | ~ m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f148,f65])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k2_struct_0(sK0))
      | r2_hidden(X1,k1_tops_1(sK0,X2))
      | ~ m1_connsp_2(X2,sK0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f75,f137])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f110,plain,
    ( r2_waybel_7(sK0,sK2,sK1)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_1
  <=> r2_waybel_7(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f227,plain,
    ( ~ r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f209,f216,f106])).

fof(f106,plain,(
    ! [X4,X5,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X4,X5)
      | sP7(X5,X1) ) ),
    inference(cnf_transformation,[],[f106_D])).

fof(f106_D,plain,(
    ! [X1,X5] :
      ( ! [X4] :
          ( ~ r2_hidden(X4,X1)
          | ~ r1_tarski(X4,X5) )
    <=> ~ sP7(X5,X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).

fof(f216,plain,
    ( ~ sP7(sK6(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f100,f203,f99,f213,f107])).

fof(f107,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_tarski(X5,X0)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))
      | ~ sP7(X5,X1) ) ),
    inference(general_splitting,[],[f105,f106_D])).

fof(f105,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) ) ),
    inference(definition_unfolding,[],[f85,f71,f71])).

fof(f71,plain,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).

fof(f85,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r1_tarski(X5,X0)
      | ~ r1_tarski(X4,X5)
      | ~ v13_waybel_0(X1,k3_yellow_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v13_waybel_0(X1,k3_yellow_1(X0))
          | ( ~ r2_hidden(sK5(X0,X1),X1)
            & r2_hidden(sK4(X0,X1),X1)
            & r1_tarski(sK5(X0,X1),X0)
            & r1_tarski(sK4(X0,X1),sK5(X0,X1)) ) )
        & ( ! [X4,X5] :
              ( r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1)
              | ~ r1_tarski(X5,X0)
              | ~ r1_tarski(X4,X5) )
          | ~ v13_waybel_0(X1,k3_yellow_1(X0)) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(X3,X1)
          & r2_hidden(X2,X1)
          & r1_tarski(X3,X0)
          & r1_tarski(X2,X3) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1)
        & r1_tarski(sK5(X0,X1),X0)
        & r1_tarski(sK4(X0,X1),sK5(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X2,X1)
            | ~ r1_tarski(X3,X0)
            | ~ r1_tarski(X2,X3) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))
     => ( v13_waybel_0(X1,k3_yellow_1(X0))
      <=> ! [X2,X3] :
            ( ( r2_hidden(X2,X1)
              & r1_tarski(X3,X0)
              & r1_tarski(X2,X3) )
           => r2_hidden(X3,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).

fof(f213,plain,
    ( r1_tarski(sK6(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f207,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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

fof(f99,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0)))))) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f47])).

fof(f203,plain,
    ( ~ r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),sK2)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f115,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK6(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f100,plain,(
    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0)))) ),
    inference(definition_unfolding,[],[f67,f71])).

fof(f67,plain,(
    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f209,plain,
    ( r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK6(k1_yellow19(sK0,sK1),sK2))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f207,f163])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(subsumption_resolution,[],[f147,f65])).

fof(f147,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(superposition,[],[f74,f137])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f200,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f198,f197])).

fof(f197,plain,
    ( ~ m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1)
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f141,f120,f175])).

fof(f175,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k2_struct_0(sK0))
      | r2_hidden(X12,k1_yellow19(sK0,X11))
      | ~ m1_connsp_2(X12,sK0,X11) ) ),
    inference(subsumption_resolution,[],[f174,f63])).

fof(f174,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k2_struct_0(sK0))
      | r2_hidden(X12,k1_yellow19(sK0,X11))
      | ~ m1_connsp_2(X12,sK0,X11)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f173,f64])).

fof(f173,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k2_struct_0(sK0))
      | r2_hidden(X12,k1_yellow19(sK0,X11))
      | ~ m1_connsp_2(X12,sK0,X11)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f153,f65])).

fof(f153,plain,(
    ! [X12,X11] :
      ( ~ m1_subset_1(X11,k2_struct_0(sK0))
      | r2_hidden(X12,k1_yellow19(sK0,X11))
      | ~ m1_connsp_2(X12,sK0,X11)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f78,f137])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k1_yellow19(X0,X1))
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f141,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),k1_yellow19(sK0,sK1))
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f114,f124,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f124,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f64,f65,f111,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f111,plain,
    ( ~ r2_waybel_7(sK0,sK2,sK1)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f109])).

fof(f114,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f198,plain,
    ( m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f123,f122,f138,f179])).

fof(f179,plain,(
    ! [X14,X13] :
      ( m1_connsp_2(X13,sK0,X14)
      | ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r2_hidden(X14,X13)
      | ~ v3_pre_topc(X13,sK0) ) ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f178,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X13,sK0,X14)
      | ~ r2_hidden(X14,X13)
      | ~ v3_pre_topc(X13,sK0)
      | ~ m1_subset_1(X14,k2_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f177,f63])).

fof(f177,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X13,sK0,X14)
      | ~ r2_hidden(X14,X13)
      | ~ v3_pre_topc(X13,sK0)
      | ~ m1_subset_1(X14,k2_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f176,f64])).

fof(f176,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X13,sK0,X14)
      | ~ r2_hidden(X14,X13)
      | ~ v3_pre_topc(X13,sK0)
      | ~ m1_subset_1(X14,k2_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f154,f65])).

fof(f154,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_connsp_2(X13,sK0,X14)
      | ~ r2_hidden(X14,X13)
      | ~ v3_pre_topc(X13,sK0)
      | ~ m1_subset_1(X14,k2_struct_0(sK0))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f79,f137])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_connsp_2(X1,X0,X2)
      | ~ r2_hidden(X2,X1)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f138,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl8_1 ),
    inference(backward_demodulation,[],[f121,f137])).

fof(f121,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f64,f65,f111,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f122,plain,
    ( v3_pre_topc(sK3(sK0,sK2,sK1),sK0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f64,f65,f111,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f123,plain,
    ( r2_hidden(sK1,sK3(sK0,sK2,sK1))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f64,f65,f111,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | r2_hidden(X2,sK3(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f69,f113,f109])).

fof(f69,plain,
    ( r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f116,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f70,f113,f109])).

fof(f70,plain,
    ( ~ r1_tarski(k1_yellow19(sK0,sK1),sK2)
    | ~ r2_waybel_7(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:26:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (2761)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (2769)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (2753)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (2769)Refutation not found, incomplete strategy% (2769)------------------------------
% 0.21/0.51  % (2769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (2751)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (2769)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (2769)Memory used [KB]: 10746
% 0.21/0.52  % (2769)Time elapsed: 0.062 s
% 0.21/0.52  % (2769)------------------------------
% 0.21/0.52  % (2769)------------------------------
% 0.21/0.52  % (2758)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (2750)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (2748)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (2776)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.53  % (2774)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (2772)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (2747)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (2749)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (2752)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (2773)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (2770)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (2765)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (2762)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (2756)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (2754)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (2764)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (2766)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (2768)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (2757)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (2755)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.55  % (2775)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (2760)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (2767)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (2773)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.49/0.57  % SZS output start Proof for theBenchmark
% 1.49/0.57  fof(f230,plain,(
% 1.49/0.57    $false),
% 1.49/0.57    inference(avatar_sat_refutation,[],[f116,f117,f200,f229])).
% 1.49/0.57  fof(f229,plain,(
% 1.49/0.57    ~spl8_1 | spl8_2),
% 1.49/0.57    inference(avatar_contradiction_clause,[],[f228])).
% 1.49/0.57  fof(f228,plain,(
% 1.49/0.57    $false | (~spl8_1 | spl8_2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f227,f220])).
% 1.49/0.57  fof(f220,plain,(
% 1.49/0.57    r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2) | (~spl8_1 | spl8_2)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f110,f210,f211,f212,f181])).
% 1.49/0.57  fof(f181,plain,(
% 1.49/0.57    ( ! [X19,X17,X18] : (~v3_pre_topc(X17,sK0) | r2_hidden(X17,X18) | ~r2_hidden(X19,X17) | ~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_waybel_7(sK0,X18,X19)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f180,f64])).
% 1.49/0.57  fof(f64,plain,(
% 1.49/0.57    v2_pre_topc(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f47,plain,(
% 1.49/0.57    (((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f46,f45,f44])).
% 1.49/0.57  fof(f44,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f45,plain,(
% 1.49/0.57    ? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(sK0,X1),X2) | ~r2_waybel_7(sK0,X2,X1)) & (r1_tarski(k1_yellow19(sK0,X1),X2) | r2_waybel_7(sK0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f46,plain,(
% 1.49/0.57    ? [X2] : ((~r1_tarski(k1_yellow19(sK0,sK1),X2) | ~r2_waybel_7(sK0,X2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),X2) | r2_waybel_7(sK0,X2,sK1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(sK0)))) => ((~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)) & (r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) & v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0))))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f43,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f42])).
% 1.49/0.57  fof(f42,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1)) & (r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f19])).
% 1.49/0.57  fof(f19,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f18])).
% 1.49/0.57  fof(f18,plain,(
% 1.49/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_waybel_7(X0,X2,X1) <~> r1_tarski(k1_yellow19(X0,X1),X2)) & (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f17])).
% 1.49/0.57  fof(f17,negated_conjecture,(
% 1.49/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 1.49/0.57    inference(negated_conjecture,[],[f16])).
% 1.49/0.57  fof(f16,conjecture,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).
% 1.49/0.57  fof(f180,plain,(
% 1.49/0.57    ( ! [X19,X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X17,X18) | ~r2_hidden(X19,X17) | ~v3_pre_topc(X17,sK0) | ~r2_waybel_7(sK0,X18,X19) | ~v2_pre_topc(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f156,f65])).
% 1.49/0.57  fof(f65,plain,(
% 1.49/0.57    l1_pre_topc(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f156,plain,(
% 1.49/0.57    ( ! [X19,X17,X18] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | r2_hidden(X17,X18) | ~r2_hidden(X19,X17) | ~v3_pre_topc(X17,sK0) | ~r2_waybel_7(sK0,X18,X19) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f80,f137])).
% 1.49/0.57  fof(f137,plain,(
% 1.49/0.57    k2_struct_0(sK0) = u1_struct_0(sK0)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f118,f72])).
% 1.49/0.57  fof(f72,plain,(
% 1.49/0.57    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f20])).
% 1.49/0.57  fof(f20,plain,(
% 1.49/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f4])).
% 1.49/0.57  fof(f4,axiom,(
% 1.49/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.49/0.57  fof(f118,plain,(
% 1.49/0.57    l1_struct_0(sK0)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f65,f73])).
% 1.49/0.57  fof(f73,plain,(
% 1.49/0.57    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f21])).
% 1.49/0.57  fof(f21,plain,(
% 1.49/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f5])).
% 1.49/0.57  fof(f5,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.49/0.57  fof(f80,plain,(
% 1.49/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_waybel_7(X0,X1,X2) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f53])).
% 1.49/0.57  fof(f53,plain,(
% 1.49/0.57    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | (~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(X2,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 1.49/0.57  fof(f52,plain,(
% 1.49/0.57    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) => (~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(X2,sK3(X0,X1,X2)) & v3_pre_topc(sK3(X0,X1,X2),X0) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f51,plain,(
% 1.49/0.57    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (r2_hidden(X4,X1) | ~r2_hidden(X2,X4) | ~v3_pre_topc(X4,X0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(rectify,[],[f50])).
% 1.49/0.57  fof(f50,plain,(
% 1.49/0.57    ! [X0] : (! [X1,X2] : ((r2_waybel_7(X0,X1,X2) | ? [X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X3) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_waybel_7(X0,X1,X2))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f30])).
% 1.49/0.57  fof(f30,plain,(
% 1.49/0.57    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f29])).
% 1.49/0.57  fof(f29,plain,(
% 1.49/0.57    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f13])).
% 1.49/0.57  fof(f13,axiom,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).
% 1.49/0.57  fof(f212,plain,(
% 1.49/0.57    m1_subset_1(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f207,f189])).
% 1.49/0.57  fof(f189,plain,(
% 1.49/0.57    ( ! [X27] : (m1_subset_1(k1_tops_1(sK0,X27),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f161,f65])).
% 1.49/0.57  fof(f161,plain,(
% 1.49/0.57    ( ! [X27] : (m1_subset_1(k1_tops_1(sK0,X27),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f92,f137])).
% 1.49/0.57  fof(f92,plain,(
% 1.49/0.57    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f38])).
% 1.49/0.57  fof(f38,plain,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f37])).
% 1.49/0.57  fof(f37,plain,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f6])).
% 1.49/0.57  fof(f6,axiom,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 1.49/0.57  fof(f207,plain,(
% 1.49/0.57    m1_subset_1(sK6(k1_yellow19(sK0,sK1),sK2),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f120,f205,f186])).
% 1.49/0.57  fof(f186,plain,(
% 1.49/0.57    ( ! [X23,X22] : (~m1_subset_1(X23,k2_struct_0(sK0)) | ~m1_connsp_2(X22,sK0,X23) | m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f185,f63])).
% 1.49/0.57  fof(f63,plain,(
% 1.49/0.57    ~v2_struct_0(sK0)),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f185,plain,(
% 1.49/0.57    ( ! [X23,X22] : (m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X22,sK0,X23) | ~m1_subset_1(X23,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f184,f64])).
% 1.49/0.57  fof(f184,plain,(
% 1.49/0.57    ( ! [X23,X22] : (m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X22,sK0,X23) | ~m1_subset_1(X23,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f158,f65])).
% 1.49/0.57  fof(f158,plain,(
% 1.49/0.57    ( ! [X23,X22] : (m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_connsp_2(X22,sK0,X23) | ~m1_subset_1(X23,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f90,f137])).
% 1.49/0.57  fof(f90,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f34])).
% 1.49/0.57  fof(f34,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f33])).
% 1.49/0.57  fof(f33,plain,(
% 1.49/0.57    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f10])).
% 1.49/0.57  fof(f10,axiom,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.49/0.57  fof(f205,plain,(
% 1.49/0.57    m1_connsp_2(sK6(k1_yellow19(sK0,sK1),sK2),sK0,sK1) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f120,f202,f172])).
% 1.49/0.57  fof(f172,plain,(
% 1.49/0.57    ( ! [X10,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | m1_connsp_2(X10,sK0,X9) | ~r2_hidden(X10,k1_yellow19(sK0,X9))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f171,f63])).
% 1.49/0.57  fof(f171,plain,(
% 1.49/0.57    ( ! [X10,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | m1_connsp_2(X10,sK0,X9) | ~r2_hidden(X10,k1_yellow19(sK0,X9)) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f170,f64])).
% 1.49/0.57  fof(f170,plain,(
% 1.49/0.57    ( ! [X10,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | m1_connsp_2(X10,sK0,X9) | ~r2_hidden(X10,k1_yellow19(sK0,X9)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f152,f65])).
% 1.49/0.57  fof(f152,plain,(
% 1.49/0.57    ( ! [X10,X9] : (~m1_subset_1(X9,k2_struct_0(sK0)) | m1_connsp_2(X10,sK0,X9) | ~r2_hidden(X10,k1_yellow19(sK0,X9)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f77,f137])).
% 1.49/0.57  fof(f77,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f49])).
% 1.49/0.57  fof(f49,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(X2,X0,X1) | ~r2_hidden(X2,k1_yellow19(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f26])).
% 1.49/0.57  fof(f26,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f25])).
% 1.49/0.57  fof(f25,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f15])).
% 1.49/0.57  fof(f15,axiom,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).
% 1.49/0.57  fof(f202,plain,(
% 1.49/0.57    r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),k1_yellow19(sK0,sK1)) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f115,f94])).
% 1.49/0.57  fof(f94,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f61])).
% 1.49/0.57  fof(f61,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f60])).
% 1.49/0.57  fof(f60,plain,(
% 1.49/0.57    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK6(X0,X1),X1) & r2_hidden(sK6(X0,X1),X0)))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f59,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(rectify,[],[f58])).
% 1.49/0.57  fof(f58,plain,(
% 1.49/0.57    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.49/0.57    inference(nnf_transformation,[],[f39])).
% 1.49/0.57  fof(f39,plain,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f1])).
% 1.49/0.57  fof(f1,axiom,(
% 1.49/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.57  fof(f115,plain,(
% 1.49/0.57    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | spl8_2),
% 1.49/0.57    inference(avatar_component_clause,[],[f113])).
% 1.49/0.57  fof(f113,plain,(
% 1.49/0.57    spl8_2 <=> r1_tarski(k1_yellow19(sK0,sK1),sK2)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.49/0.57  fof(f120,plain,(
% 1.49/0.57    m1_subset_1(sK1,k2_struct_0(sK0))),
% 1.49/0.57    inference(subsumption_resolution,[],[f119,f118])).
% 1.49/0.57  fof(f119,plain,(
% 1.49/0.57    m1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_struct_0(sK0)),
% 1.49/0.57    inference(superposition,[],[f66,f72])).
% 1.49/0.57  fof(f66,plain,(
% 1.49/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f211,plain,(
% 1.49/0.57    v3_pre_topc(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK0) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f207,f188])).
% 1.49/0.57  fof(f188,plain,(
% 1.49/0.57    ( ! [X26] : (v3_pre_topc(k1_tops_1(sK0,X26),sK0) | ~m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f187,f64])).
% 1.49/0.57  fof(f187,plain,(
% 1.49/0.57    ( ! [X26] : (~m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X26),sK0) | ~v2_pre_topc(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f160,f65])).
% 1.49/0.57  fof(f160,plain,(
% 1.49/0.57    ( ! [X26] : (~m1_subset_1(X26,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X26),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f91,f137])).
% 1.49/0.57  fof(f91,plain,(
% 1.49/0.57    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f36])).
% 1.49/0.57  fof(f36,plain,(
% 1.49/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.57    inference(flattening,[],[f35])).
% 1.49/0.57  fof(f35,plain,(
% 1.49/0.57    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f7])).
% 1.49/0.57  fof(f7,axiom,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.49/0.57  fof(f210,plain,(
% 1.49/0.57    r2_hidden(sK1,k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2))) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f120,f205,f207,f166])).
% 1.49/0.57  fof(f166,plain,(
% 1.49/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X2)) | ~m1_connsp_2(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f165,f63])).
% 1.49/0.57  fof(f165,plain,(
% 1.49/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X2)) | ~m1_connsp_2(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f164,f64])).
% 1.49/0.57  fof(f164,plain,(
% 1.49/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X2)) | ~m1_connsp_2(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f148,f65])).
% 1.49/0.57  fof(f148,plain,(
% 1.49/0.57    ( ! [X2,X1] : (~m1_subset_1(X1,k2_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X2)) | ~m1_connsp_2(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f75,f137])).
% 1.49/0.57  fof(f75,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f48])).
% 1.49/0.57  fof(f48,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(nnf_transformation,[],[f24])).
% 1.49/0.57  fof(f24,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f23])).
% 1.49/0.57  fof(f23,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f9])).
% 1.49/0.57  fof(f9,axiom,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 1.49/0.57  fof(f110,plain,(
% 1.49/0.57    r2_waybel_7(sK0,sK2,sK1) | ~spl8_1),
% 1.49/0.57    inference(avatar_component_clause,[],[f109])).
% 1.49/0.57  fof(f109,plain,(
% 1.49/0.57    spl8_1 <=> r2_waybel_7(sK0,sK2,sK1)),
% 1.49/0.57    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.49/0.57  fof(f227,plain,(
% 1.49/0.57    ~r2_hidden(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK2) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f209,f216,f106])).
% 1.49/0.57  fof(f106,plain,(
% 1.49/0.57    ( ! [X4,X5,X1] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5) | sP7(X5,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f106_D])).
% 1.49/0.57  fof(f106_D,plain,(
% 1.49/0.57    ( ! [X1,X5] : (( ! [X4] : (~r2_hidden(X4,X1) | ~r1_tarski(X4,X5)) ) <=> ~sP7(X5,X1)) )),
% 1.49/0.57    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP7])])).
% 1.49/0.57  fof(f216,plain,(
% 1.49/0.57    ~sP7(sK6(k1_yellow19(sK0,sK1),sK2),sK2) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f100,f203,f99,f213,f107])).
% 1.49/0.57  fof(f107,plain,(
% 1.49/0.57    ( ! [X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_tarski(X5,X0) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0))))) | ~sP7(X5,X1)) )),
% 1.49/0.57    inference(general_splitting,[],[f105,f106_D])).
% 1.49/0.57  fof(f105,plain,(
% 1.49/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_lattice3(k1_lattice3(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(X0)))))) )),
% 1.49/0.57    inference(definition_unfolding,[],[f85,f71,f71])).
% 1.49/0.57  fof(f71,plain,(
% 1.49/0.57    ( ! [X0] : (k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f12])).
% 1.49/0.57  fof(f12,axiom,(
% 1.49/0.57    ! [X0] : k3_yellow_1(X0) = k3_lattice3(k1_lattice3(X0))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_yellow_1)).
% 1.49/0.57  fof(f85,plain,(
% 1.49/0.57    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5) | ~v13_waybel_0(X1,k3_yellow_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0))))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f57])).
% 1.49/0.57  fof(f57,plain,(
% 1.49/0.57    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & r1_tarski(sK5(X0,X1),X0) & r1_tarski(sK4(X0,X1),sK5(X0,X1)))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.49/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f55,f56])).
% 1.49/0.57  fof(f56,plain,(
% 1.49/0.57    ! [X1,X0] : (? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => (~r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1) & r1_tarski(sK5(X0,X1),X0) & r1_tarski(sK4(X0,X1),sK5(X0,X1))))),
% 1.49/0.57    introduced(choice_axiom,[])).
% 1.49/0.57  fof(f55,plain,(
% 1.49/0.57    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X4,X5] : (r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | ~r1_tarski(X5,X0) | ~r1_tarski(X4,X5)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.49/0.57    inference(rectify,[],[f54])).
% 1.49/0.57  fof(f54,plain,(
% 1.49/0.57    ! [X0,X1] : (((v13_waybel_0(X1,k3_yellow_1(X0)) | ? [X2,X3] : (~r2_hidden(X3,X1) & r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3))) & (! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)) | ~v13_waybel_0(X1,k3_yellow_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.49/0.57    inference(nnf_transformation,[],[f32])).
% 1.49/0.57  fof(f32,plain,(
% 1.49/0.57    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.49/0.57    inference(flattening,[],[f31])).
% 1.49/0.57  fof(f31,plain,(
% 1.49/0.57    ! [X0,X1] : ((v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : (r2_hidden(X3,X1) | (~r2_hidden(X2,X1) | ~r1_tarski(X3,X0) | ~r1_tarski(X2,X3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))))),
% 1.49/0.57    inference(ennf_transformation,[],[f14])).
% 1.49/0.57  fof(f14,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X0)))) => (v13_waybel_0(X1,k3_yellow_1(X0)) <=> ! [X2,X3] : ((r2_hidden(X2,X1) & r1_tarski(X3,X0) & r1_tarski(X2,X3)) => r2_hidden(X3,X1))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_waybel_7)).
% 1.49/0.57  fof(f213,plain,(
% 1.49/0.57    r1_tarski(sK6(k1_yellow19(sK0,sK1),sK2),k2_struct_0(sK0)) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f207,f96])).
% 1.49/0.57  fof(f96,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.49/0.57    inference(cnf_transformation,[],[f62])).
% 1.49/0.57  fof(f62,plain,(
% 1.49/0.57    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.49/0.57    inference(nnf_transformation,[],[f2])).
% 1.49/0.57  fof(f2,axiom,(
% 1.49/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.57  fof(f99,plain,(
% 1.49/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_lattice3(k1_lattice3(k2_struct_0(sK0))))))),
% 1.49/0.57    inference(definition_unfolding,[],[f68,f71])).
% 1.49/0.57  fof(f68,plain,(
% 1.49/0.57    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f203,plain,(
% 1.49/0.57    ~r2_hidden(sK6(k1_yellow19(sK0,sK1),sK2),sK2) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f115,f95])).
% 1.49/0.57  fof(f95,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK6(X0,X1),X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f61])).
% 1.49/0.57  fof(f100,plain,(
% 1.49/0.57    v13_waybel_0(sK2,k3_lattice3(k1_lattice3(k2_struct_0(sK0))))),
% 1.49/0.57    inference(definition_unfolding,[],[f67,f71])).
% 1.49/0.57  fof(f67,plain,(
% 1.49/0.57    v13_waybel_0(sK2,k3_yellow_1(k2_struct_0(sK0)))),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f209,plain,(
% 1.49/0.57    r1_tarski(k1_tops_1(sK0,sK6(k1_yellow19(sK0,sK1),sK2)),sK6(k1_yellow19(sK0,sK1),sK2)) | spl8_2),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f207,f163])).
% 1.49/0.57  fof(f163,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f147,f65])).
% 1.49/0.57  fof(f147,plain,(
% 1.49/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0) | ~l1_pre_topc(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f74,f137])).
% 1.49/0.57  fof(f74,plain,(
% 1.49/0.57    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f22])).
% 1.49/0.57  fof(f22,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.49/0.57    inference(ennf_transformation,[],[f8])).
% 1.49/0.57  fof(f8,axiom,(
% 1.49/0.57    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.49/0.57  fof(f200,plain,(
% 1.49/0.57    spl8_1 | ~spl8_2),
% 1.49/0.57    inference(avatar_contradiction_clause,[],[f199])).
% 1.49/0.57  fof(f199,plain,(
% 1.49/0.57    $false | (spl8_1 | ~spl8_2)),
% 1.49/0.57    inference(subsumption_resolution,[],[f198,f197])).
% 1.49/0.57  fof(f197,plain,(
% 1.49/0.57    ~m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1) | (spl8_1 | ~spl8_2)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f141,f120,f175])).
% 1.49/0.57  fof(f175,plain,(
% 1.49/0.57    ( ! [X12,X11] : (~m1_subset_1(X11,k2_struct_0(sK0)) | r2_hidden(X12,k1_yellow19(sK0,X11)) | ~m1_connsp_2(X12,sK0,X11)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f174,f63])).
% 1.49/0.57  fof(f174,plain,(
% 1.49/0.57    ( ! [X12,X11] : (~m1_subset_1(X11,k2_struct_0(sK0)) | r2_hidden(X12,k1_yellow19(sK0,X11)) | ~m1_connsp_2(X12,sK0,X11) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f173,f64])).
% 1.49/0.57  fof(f173,plain,(
% 1.49/0.57    ( ! [X12,X11] : (~m1_subset_1(X11,k2_struct_0(sK0)) | r2_hidden(X12,k1_yellow19(sK0,X11)) | ~m1_connsp_2(X12,sK0,X11) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f153,f65])).
% 1.49/0.57  fof(f153,plain,(
% 1.49/0.57    ( ! [X12,X11] : (~m1_subset_1(X11,k2_struct_0(sK0)) | r2_hidden(X12,k1_yellow19(sK0,X11)) | ~m1_connsp_2(X12,sK0,X11) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f78,f137])).
% 1.49/0.57  fof(f78,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_hidden(X2,k1_yellow19(X0,X1)) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f49])).
% 1.49/0.57  fof(f141,plain,(
% 1.49/0.57    ~r2_hidden(sK3(sK0,sK2,sK1),k1_yellow19(sK0,sK1)) | (spl8_1 | ~spl8_2)),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f114,f124,f93])).
% 1.49/0.57  fof(f93,plain,(
% 1.49/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f61])).
% 1.49/0.57  fof(f124,plain,(
% 1.49/0.57    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | spl8_1),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f64,f65,f111,f84])).
% 1.49/0.57  fof(f84,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f53])).
% 1.49/0.57  fof(f111,plain,(
% 1.49/0.57    ~r2_waybel_7(sK0,sK2,sK1) | spl8_1),
% 1.49/0.57    inference(avatar_component_clause,[],[f109])).
% 1.49/0.57  fof(f114,plain,(
% 1.49/0.57    r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~spl8_2),
% 1.49/0.57    inference(avatar_component_clause,[],[f113])).
% 1.49/0.57  fof(f198,plain,(
% 1.49/0.57    m1_connsp_2(sK3(sK0,sK2,sK1),sK0,sK1) | spl8_1),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f123,f122,f138,f179])).
% 1.49/0.57  fof(f179,plain,(
% 1.49/0.57    ( ! [X14,X13] : (m1_connsp_2(X13,sK0,X14) | ~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | ~r2_hidden(X14,X13) | ~v3_pre_topc(X13,sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f178,f98])).
% 1.49/0.57  fof(f98,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f41])).
% 1.49/0.57  fof(f41,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.49/0.57    inference(flattening,[],[f40])).
% 1.49/0.57  fof(f40,plain,(
% 1.49/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.49/0.57    inference(ennf_transformation,[],[f3])).
% 1.49/0.57  fof(f3,axiom,(
% 1.49/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.49/0.57  fof(f178,plain,(
% 1.49/0.57    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X13,sK0,X14) | ~r2_hidden(X14,X13) | ~v3_pre_topc(X13,sK0) | ~m1_subset_1(X14,k2_struct_0(sK0))) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f177,f63])).
% 1.49/0.57  fof(f177,plain,(
% 1.49/0.57    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X13,sK0,X14) | ~r2_hidden(X14,X13) | ~v3_pre_topc(X13,sK0) | ~m1_subset_1(X14,k2_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f176,f64])).
% 1.49/0.57  fof(f176,plain,(
% 1.49/0.57    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X13,sK0,X14) | ~r2_hidden(X14,X13) | ~v3_pre_topc(X13,sK0) | ~m1_subset_1(X14,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(subsumption_resolution,[],[f154,f65])).
% 1.49/0.57  fof(f154,plain,(
% 1.49/0.57    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_connsp_2(X13,sK0,X14) | ~r2_hidden(X14,X13) | ~v3_pre_topc(X13,sK0) | ~m1_subset_1(X14,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) )),
% 1.49/0.57    inference(superposition,[],[f79,f137])).
% 1.49/0.57  fof(f79,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f28])).
% 1.49/0.57  fof(f28,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.57    inference(flattening,[],[f27])).
% 1.49/0.57  fof(f27,plain,(
% 1.49/0.57    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.57    inference(ennf_transformation,[],[f11])).
% 1.49/0.57  fof(f11,axiom,(
% 1.49/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 1.49/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 1.49/0.57  fof(f138,plain,(
% 1.49/0.57    m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(k2_struct_0(sK0))) | spl8_1),
% 1.49/0.57    inference(backward_demodulation,[],[f121,f137])).
% 1.49/0.57  fof(f121,plain,(
% 1.49/0.57    m1_subset_1(sK3(sK0,sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl8_1),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f64,f65,f111,f81])).
% 1.49/0.57  fof(f81,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f53])).
% 1.49/0.57  fof(f122,plain,(
% 1.49/0.57    v3_pre_topc(sK3(sK0,sK2,sK1),sK0) | spl8_1),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f64,f65,f111,f82])).
% 1.49/0.57  fof(f82,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | v3_pre_topc(sK3(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f53])).
% 1.49/0.57  fof(f123,plain,(
% 1.49/0.57    r2_hidden(sK1,sK3(sK0,sK2,sK1)) | spl8_1),
% 1.49/0.57    inference(unit_resulting_resolution,[],[f64,f65,f111,f83])).
% 1.49/0.57  fof(f83,plain,(
% 1.49/0.57    ( ! [X2,X0,X1] : (r2_waybel_7(X0,X1,X2) | r2_hidden(X2,sK3(X0,X1,X2)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.57    inference(cnf_transformation,[],[f53])).
% 1.49/0.57  fof(f117,plain,(
% 1.49/0.57    spl8_1 | spl8_2),
% 1.49/0.57    inference(avatar_split_clause,[],[f69,f113,f109])).
% 1.49/0.57  fof(f69,plain,(
% 1.49/0.57    r1_tarski(k1_yellow19(sK0,sK1),sK2) | r2_waybel_7(sK0,sK2,sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  fof(f116,plain,(
% 1.49/0.57    ~spl8_1 | ~spl8_2),
% 1.49/0.57    inference(avatar_split_clause,[],[f70,f113,f109])).
% 1.49/0.57  fof(f70,plain,(
% 1.49/0.57    ~r1_tarski(k1_yellow19(sK0,sK1),sK2) | ~r2_waybel_7(sK0,sK2,sK1)),
% 1.49/0.57    inference(cnf_transformation,[],[f47])).
% 1.49/0.57  % SZS output end Proof for theBenchmark
% 1.49/0.57  % (2773)------------------------------
% 1.49/0.57  % (2773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (2773)Termination reason: Refutation
% 1.49/0.57  
% 1.49/0.57  % (2773)Memory used [KB]: 10874
% 1.49/0.57  % (2773)Time elapsed: 0.156 s
% 1.49/0.57  % (2773)------------------------------
% 1.49/0.57  % (2773)------------------------------
% 1.49/0.57  % (2746)Success in time 0.212 s
%------------------------------------------------------------------------------
