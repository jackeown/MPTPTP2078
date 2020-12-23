%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1984+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:38 EST 2020

% Result     : Theorem 8.34s
% Output     : Refutation 8.34s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 716 expanded)
%              Number of leaves         :   13 ( 301 expanded)
%              Depth                    :   20
%              Number of atoms          :  785 (10282 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   18 (   8 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35087,plain,(
    $false ),
    inference(subsumption_resolution,[],[f35086,f34329])).

fof(f34329,plain,(
    r2_hidden(sK85(sK49,sK51,sK52),sK51) ),
    inference(subsumption_resolution,[],[f34328,f9027])).

fof(f9027,plain,(
    v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(global_subsumption,[],[f5635,f9026])).

fof(f9026,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))) ),
    inference(subsumption_resolution,[],[f9025,f5747])).

fof(f5747,plain,(
    ! [X0] : ~ v2_struct_0(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4241])).

fof(f4241,plain,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3109])).

fof(f3109,axiom,(
    ! [X0] :
      ( v5_orders_2(k3_yellow_1(X0))
      & v4_orders_2(k3_yellow_1(X0))
      & v3_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0))
      & ~ v2_struct_0(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_yellow_1)).

fof(f9025,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9024,f5748])).

fof(f5748,plain,(
    ! [X0] : v3_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4241])).

fof(f9024,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9023,f5749])).

fof(f5749,plain,(
    ! [X0] : v4_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4241])).

fof(f9023,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9022,f5750])).

fof(f5750,plain,(
    ! [X0] : v5_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4241])).

fof(f9022,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9021,f5745])).

fof(f5745,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(cnf_transformation,[],[f4248])).

fof(f4248,plain,(
    ! [X0] : l1_orders_2(k3_yellow_1(X0)) ),
    inference(pure_predicate_removal,[],[f3085])).

fof(f3085,axiom,(
    ! [X0] :
      ( l1_orders_2(k3_yellow_1(X0))
      & v1_orders_2(k3_yellow_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_1)).

fof(f9021,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ l1_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9020,f5631])).

fof(f5631,plain,(
    ~ v1_xboole_0(sK52) ),
    inference(cnf_transformation,[],[f4944])).

fof(f4944,plain,
    ( ! [X4] :
        ( ~ r2_waybel_7(sK49,sK52,X4)
        | ~ r2_hidden(X4,sK51)
        | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
    & r2_hidden(sK50,sK52)
    & m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    & v3_waybel_7(sK52,k3_yellow_1(u1_struct_0(sK49)))
    & v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    & v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    & ~ v1_xboole_0(sK52)
    & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),sK50,sK51)
    & m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
    & m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
    & l1_pre_topc(sK49)
    & v2_pre_topc(sK49)
    & ~ v2_struct_0(sK49) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49,sK50,sK51,sK52])],[f4260,f4943,f4942,f4941,f4940])).

fof(f4940,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_waybel_7(X0,X3,X4)
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_hidden(X1,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                    & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                    & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                    & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                    & ~ v1_xboole_0(X3) )
                & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
                & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
            & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(sK49,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
      & l1_pre_topc(sK49)
      & v2_pre_topc(sK49)
      & ~ v2_struct_0(sK49) ) ),
    introduced(choice_axiom,[])).

fof(f4941,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( ~ r2_waybel_7(sK49,X3,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
                & r2_hidden(X1,X3)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
                & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
                & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
                & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
                & ~ v1_xboole_0(X3) )
            & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),X1,X2)
            & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
        & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r2_waybel_7(sK49,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
              & r2_hidden(sK50,X3)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
              & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
              & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
              & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
              & ~ v1_xboole_0(X3) )
          & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),sK50,X2)
          & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
      & m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) ) ),
    introduced(choice_axiom,[])).

fof(f4942,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r2_waybel_7(sK49,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
            & r2_hidden(sK50,X3)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
            & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
            & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
            & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
            & ~ v1_xboole_0(X3) )
        & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),sK50,X2)
        & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_waybel_7(sK49,X3,X4)
              | ~ r2_hidden(X4,sK51)
              | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
          & r2_hidden(sK50,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
          & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
          & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
          & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
          & ~ v1_xboole_0(X3) )
      & r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),sK50,sK51)
      & m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) ) ),
    introduced(choice_axiom,[])).

fof(f4943,plain,
    ( ? [X3] :
        ( ! [X4] :
            ( ~ r2_waybel_7(sK49,X3,X4)
            | ~ r2_hidden(X4,sK51)
            | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
        & r2_hidden(sK50,X3)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
        & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(sK49)))
        & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
        & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
        & ~ v1_xboole_0(X3) )
   => ( ! [X4] :
          ( ~ r2_waybel_7(sK49,sK52,X4)
          | ~ r2_hidden(X4,sK51)
          | ~ m1_subset_1(X4,u1_struct_0(sK49)) )
      & r2_hidden(sK50,sK52)
      & m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      & v3_waybel_7(sK52,k3_yellow_1(u1_struct_0(sK49)))
      & v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      & v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      & ~ v1_xboole_0(sK52) ) ),
    introduced(choice_axiom,[])).

fof(f4260,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f4259])).

fof(f4259,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( ~ r2_waybel_7(X0,X3,X4)
                      | ~ r2_hidden(X4,X2)
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  & r2_hidden(X1,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  & ~ v1_xboole_0(X3) )
              & r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              & m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          & m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4203])).

fof(f4203,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
               => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
                 => ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                        & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ~ ( r2_waybel_7(X0,X3,X4)
                                  & r2_hidden(X4,X2) ) )
                          & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f4202])).

fof(f4202,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v3_waybel_7(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r2_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_waybel_7)).

fof(f9020,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | v1_xboole_0(sK52)
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ l1_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9019,f5632])).

fof(f5632,plain,(
    v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9019,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | v1_xboole_0(sK52)
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ l1_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(subsumption_resolution,[],[f9013,f5633])).

fof(f5633,plain,(
    v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9013,plain,
    ( v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | v1_xboole_0(sK52)
    | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
    | ~ l1_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v5_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v4_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | ~ v3_orders_2(k3_yellow_1(u1_struct_0(sK49)))
    | v2_struct_0(k3_yellow_1(u1_struct_0(sK49))) ),
    inference(resolution,[],[f5634,f5680])).

fof(f5680,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_waybel_7(X1,X0)
      | ~ v13_waybel_0(X1,X0)
      | ~ v2_waybel_0(X1,X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4287])).

fof(f4287,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4286])).

fof(f4286,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & v1_subset_1(X1,u1_struct_0(X0))
            & ~ v1_xboole_0(X1) )
          | ~ v3_waybel_7(X1,X0)
          | ~ v13_waybel_0(X1,X0)
          | ~ v2_waybel_0(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4104])).

fof(f4104,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_waybel_7(X1,X0)
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & v1_subset_1(X1,u1_struct_0(X0))
              & ~ v1_xboole_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_waybel_7)).

fof(f5634,plain,(
    v3_waybel_7(sK52,k3_yellow_1(u1_struct_0(sK49))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f5635,plain,(
    m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f34328,plain,
    ( r2_hidden(sK85(sK49,sK51,sK52),sK51)
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34327,f5632])).

fof(f34327,plain,
    ( r2_hidden(sK85(sK49,sK51,sK52),sK51)
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34326,f5633])).

fof(f34326,plain,
    ( r2_hidden(sK85(sK49,sK51,sK52),sK51)
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34246,f5636])).

fof(f5636,plain,(
    r2_hidden(sK50,sK52) ),
    inference(cnf_transformation,[],[f4944])).

fof(f34246,plain,
    ( ~ r2_hidden(sK50,sK52)
    | r2_hidden(sK85(sK49,sK51,sK52),sK51)
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(resolution,[],[f9869,f5635])).

fof(f9869,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ r2_hidden(sK50,X4)
      | r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ) ),
    inference(subsumption_resolution,[],[f9868,f5770])).

fof(f5770,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f5026])).

fof(f5026,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK82(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK82])],[f5024,f5025])).

fof(f5025,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK82(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5024,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f5023])).

fof(f5023,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f9868,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4) ) ),
    inference(subsumption_resolution,[],[f9867,f5625])).

fof(f5625,plain,(
    ~ v2_struct_0(sK49) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9867,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9866,f5626])).

fof(f5626,plain,(
    v2_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9866,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9865,f5627])).

fof(f5627,plain,(
    l1_pre_topc(sK49) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9865,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9864,f5628])).

fof(f5628,plain,(
    m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9864,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9841,f5629])).

fof(f5629,plain,(
    m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49)))) ),
    inference(cnf_transformation,[],[f4944])).

fof(f9841,plain,(
    ! [X4] :
      ( r2_hidden(sK85(sK49,sK51,X4),sK51)
      | ~ r2_hidden(sK50,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X4,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X4,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X4)
      | ~ m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(resolution,[],[f5630,f5781])).

fof(f5781,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK85(X0,X2,X3),X2)
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5032])).

fof(f5032,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_waybel_7(X0,X3,sK85(X0,X2,X3))
                    & r2_hidden(sK85(X0,X2,X3),X2)
                    & m1_subset_1(sK85(X0,X2,X3),u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK85])],[f4331,f5031])).

fof(f5031,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( r1_waybel_7(X0,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( r1_waybel_7(X0,X3,sK85(X0,X2,X3))
        & r2_hidden(sK85(X0,X2,X3),X2)
        & m1_subset_1(sK85(X0,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f4331,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4330])).

fof(f4330,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ? [X4] :
                      ( r1_waybel_7(X0,X3,X4)
                      & r2_hidden(X4,X2)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r2_hidden(X1,X3)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                  | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                  | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                  | v1_xboole_0(X3) )
              | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
          | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0)))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4201])).

fof(f4201,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
             => ( r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
                      & v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
                      & v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
                      & ~ v1_xboole_0(X3) )
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_waybel_7(X0,X3,X4)
                                & r2_hidden(X4,X2) ) )
                        & r2_hidden(X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_waybel_7)).

fof(f5630,plain,(
    r1_waybel_3(k2_yellow_1(u1_pre_topc(sK49)),sK50,sK51) ),
    inference(cnf_transformation,[],[f4944])).

fof(f35086,plain,(
    ~ r2_hidden(sK85(sK49,sK51,sK52),sK51) ),
    inference(subsumption_resolution,[],[f35083,f34812])).

fof(f34812,plain,(
    m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49)) ),
    inference(subsumption_resolution,[],[f34811,f9027])).

fof(f34811,plain,
    ( m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34810,f5632])).

fof(f34810,plain,
    ( m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34809,f5633])).

fof(f34809,plain,
    ( m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49))
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34729,f5636])).

fof(f34729,plain,
    ( ~ r2_hidden(sK50,sK52)
    | m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49))
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(resolution,[],[f9863,f5635])).

fof(f9863,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ r2_hidden(sK50,X3)
      | m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ) ),
    inference(subsumption_resolution,[],[f9862,f5770])).

fof(f9862,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f9861,f5625])).

fof(f9861,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9860,f5626])).

fof(f9860,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9859,f5627])).

fof(f9859,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9858,f5628])).

fof(f9858,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9840,f5629])).

fof(f9840,plain,(
    ! [X3] :
      ( m1_subset_1(sK85(sK49,sK51,X3),u1_struct_0(sK49))
      | ~ r2_hidden(sK50,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(resolution,[],[f5630,f5780])).

fof(f5780,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK85(X0,X2,X3),u1_struct_0(X0))
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5032])).

fof(f35083,plain,
    ( ~ m1_subset_1(sK85(sK49,sK51,sK52),u1_struct_0(sK49))
    | ~ r2_hidden(sK85(sK49,sK51,sK52),sK51) ),
    inference(resolution,[],[f35075,f11191])).

fof(f11191,plain,(
    ! [X0] :
      ( ~ r1_waybel_7(sK49,sK52,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r2_hidden(X0,sK51) ) ),
    inference(subsumption_resolution,[],[f11190,f5625])).

fof(f11190,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11189,f5626])).

fof(f11189,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11188,f5627])).

fof(f11188,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11187,f5631])).

fof(f11187,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | v1_xboole_0(sK52)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11186,f5632])).

fof(f11186,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | v1_xboole_0(sK52)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11185,f5633])).

fof(f11185,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | v1_xboole_0(sK52)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11184,f5634])).

fof(f11184,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ v3_waybel_7(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | v1_xboole_0(sK52)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f11179,f5635])).

fof(f11179,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK51)
      | ~ m1_subset_1(X0,u1_struct_0(sK49))
      | ~ r1_waybel_7(sK49,sK52,X0)
      | ~ m1_subset_1(sK52,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v3_waybel_7(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
      | v1_xboole_0(sK52)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(resolution,[],[f5637,f5643])).

fof(f5643,plain,(
    ! [X2,X0,X1] :
      ( r2_waybel_7(X0,X1,X2)
      | ~ r1_waybel_7(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f4949])).

fof(f4949,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_7(X0,X1,X2)
                | ~ r2_waybel_7(X0,X1,X2) )
              & ( r2_waybel_7(X0,X1,X2)
                | ~ r1_waybel_7(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f4264])).

fof(f4264,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f4263])).

fof(f4263,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
          | ~ v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4200])).

fof(f4200,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
            & v3_waybel_7(X1,k3_yellow_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( r1_waybel_7(X0,X1,X2)
            <=> r2_waybel_7(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_waybel_7)).

fof(f5637,plain,(
    ! [X4] :
      ( ~ r2_waybel_7(sK49,sK52,X4)
      | ~ r2_hidden(X4,sK51)
      | ~ m1_subset_1(X4,u1_struct_0(sK49)) ) ),
    inference(cnf_transformation,[],[f4944])).

fof(f35075,plain,(
    r1_waybel_7(sK49,sK52,sK85(sK49,sK51,sK52)) ),
    inference(subsumption_resolution,[],[f35074,f9027])).

fof(f35074,plain,
    ( r1_waybel_7(sK49,sK52,sK85(sK49,sK51,sK52))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f35073,f5632])).

fof(f35073,plain,
    ( r1_waybel_7(sK49,sK52,sK85(sK49,sK51,sK52))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f35072,f5633])).

fof(f35072,plain,
    ( r1_waybel_7(sK49,sK52,sK85(sK49,sK51,sK52))
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(subsumption_resolution,[],[f34992,f5636])).

fof(f34992,plain,
    ( ~ r2_hidden(sK50,sK52)
    | r1_waybel_7(sK49,sK52,sK85(sK49,sK51,sK52))
    | ~ v13_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v2_waybel_0(sK52,k3_yellow_1(u1_struct_0(sK49)))
    | ~ v1_subset_1(sK52,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ),
    inference(resolution,[],[f9875,f5635])).

fof(f9875,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ r2_hidden(sK50,X5)
      | r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))) ) ),
    inference(subsumption_resolution,[],[f9874,f5770])).

fof(f9874,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5) ) ),
    inference(subsumption_resolution,[],[f9873,f5625])).

fof(f9873,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9872,f5626])).

fof(f9872,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9871,f5627])).

fof(f9871,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5)
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9870,f5628])).

fof(f9870,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5)
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(subsumption_resolution,[],[f9842,f5629])).

fof(f9842,plain,(
    ! [X5] :
      ( r1_waybel_7(sK49,X5,sK85(sK49,sK51,X5))
      | ~ r2_hidden(sK50,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(sK49)))))
      | ~ v13_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v2_waybel_0(X5,k3_yellow_1(u1_struct_0(sK49)))
      | ~ v1_subset_1(X5,u1_struct_0(k3_yellow_1(u1_struct_0(sK49))))
      | v1_xboole_0(X5)
      | ~ m1_subset_1(sK51,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ m1_subset_1(sK50,u1_struct_0(k2_yellow_1(u1_pre_topc(sK49))))
      | ~ l1_pre_topc(sK49)
      | ~ v2_pre_topc(sK49)
      | v2_struct_0(sK49) ) ),
    inference(resolution,[],[f5630,f5782])).

fof(f5782,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_waybel_7(X0,X3,sK85(X0,X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k3_yellow_1(u1_struct_0(X0)))))
      | ~ v13_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v2_waybel_0(X3,k3_yellow_1(u1_struct_0(X0)))
      | ~ v1_subset_1(X3,u1_struct_0(k3_yellow_1(u1_struct_0(X0))))
      | v1_xboole_0(X3)
      | ~ r1_waybel_3(k2_yellow_1(u1_pre_topc(X0)),X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ m1_subset_1(X1,u1_struct_0(k2_yellow_1(u1_pre_topc(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f5032])).
%------------------------------------------------------------------------------
