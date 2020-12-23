%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1655+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 54.77s
% Output     : Refutation 54.77s
% Verified   : 
% Statistics : Number of formulae       :  114 (16217 expanded)
%              Number of leaves         :   16 (5088 expanded)
%              Depth                    :   17
%              Number of atoms          :  659 (143478 expanded)
%              Number of equality atoms :   14 ( 869 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221708,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f104,f204074,f221707])).

fof(f221707,plain,
    ( ~ spl9_1
    | spl9_2 ),
    inference(avatar_contradiction_clause,[],[f221706])).

fof(f221706,plain,
    ( $false
    | ~ spl9_1
    | spl9_2 ),
    inference(subsumption_resolution,[],[f221617,f205138])).

fof(f205138,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f37,f38,f40,f204118,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f204118,plain,
    ( m1_subset_1(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),u1_struct_0(sK0))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f97,f204097,f204095,f41,f204101,f204099,f44])).

fof(f44,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ( ! [X4] :
                    ( ~ r1_orders_2(X0,X4,sK3(X0,X1))
                    | ~ r1_orders_2(X0,X4,sK2(X0,X1))
                    | ~ r2_hidden(X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_hidden(sK3(X0,X1),X1)
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X6)
                        & r1_orders_2(X0,sK4(X0,X1,X5,X6),X5)
                        & r2_hidden(sK4(X0,X1,X5,X6),X1)
                        & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( ~ r1_orders_2(X0,X4,X3)
                  | ~ r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_orders_2(X0,X4,X3)
                | ~ r1_orders_2(X0,X4,sK2(X0,X1))
                | ~ r2_hidden(X4,X1)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(X3,X1)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_orders_2(X0,X4,X3)
              | ~ r1_orders_2(X0,X4,sK2(X0,X1))
              | ~ r2_hidden(X4,X1)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r1_orders_2(X0,X4,sK3(X0,X1))
            | ~ r1_orders_2(X0,X4,sK2(X0,X1))
            | ~ r2_hidden(X4,X1)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X5,X1,X0] :
      ( ? [X7] :
          ( r1_orders_2(X0,X7,X6)
          & r1_orders_2(X0,X7,X5)
          & r2_hidden(X7,X1)
          & m1_subset_1(X7,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,sK4(X0,X1,X5,X6),X6)
        & r1_orders_2(X0,sK4(X0,X1,X5,X6),X5)
        & r2_hidden(sK4(X0,X1,X5,X6),X1)
        & m1_subset_1(sK4(X0,X1,X5,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X5] :
                  ( ! [X6] :
                      ( ? [X7] :
                          ( r1_orders_2(X0,X7,X6)
                          & r1_orders_2(X0,X7,X5)
                          & r2_hidden(X7,X1)
                          & m1_subset_1(X7,u1_struct_0(X0)) )
                      | ~ r2_hidden(X6,X1)
                      | ~ r2_hidden(X5,X1)
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ! [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r2_hidden(X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r2_hidden(X3,X1)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( ? [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(X3,X1)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v2_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( ? [X4] :
                        ( r1_orders_2(X0,X4,X3)
                        & r1_orders_2(X0,X4,X2)
                        & r2_hidden(X4,X1)
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    | ~ r2_hidden(X3,X1)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ~ ( r1_orders_2(X0,X4,X3)
                                & r1_orders_2(X0,X4,X2)
                                & r2_hidden(X4,X1) ) )
                        & r2_hidden(X3,X1)
                        & r2_hidden(X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_waybel_0)).

fof(f204099,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204077,f204079,f68])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ( ( ! [X4] :
                          ( ~ r2_hidden(X4,X1)
                          | ~ r1_orders_2(X0,X4,sK5(X0,X1,X2))
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r2_hidden(sK5(X0,X1,X2),X2) )
                    & ( ( r2_hidden(sK6(X0,X1,X2),X1)
                        & r1_orders_2(X0,sK6(X0,X1,X2),sK5(X0,X1,X2))
                        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
                      | r2_hidden(sK5(X0,X1,X2),X2) )
                    & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ( r2_hidden(sK7(X0,X1,X6),X1)
                            & r1_orders_2(X0,sK7(X0,X1,X6),X6)
                            & m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f32,f35,f34,f33])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r1_orders_2(X0,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r1_orders_2(X0,X5,X3)
                & m1_subset_1(X5,u1_struct_0(X0)) )
            | r2_hidden(X3,X2) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r1_orders_2(X0,X4,sK5(X0,X1,X2))
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r1_orders_2(X0,X5,sK5(X0,X1,X2))
              & m1_subset_1(X5,u1_struct_0(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r1_orders_2(X0,X5,sK5(X0,X1,X2))
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r1_orders_2(X0,sK6(X0,X1,X2),sK5(X0,X1,X2))
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r1_orders_2(X0,X8,X6)
          & m1_subset_1(X8,u1_struct_0(X0)) )
     => ( r2_hidden(sK7(X0,X1,X6),X1)
        & r1_orders_2(X0,sK7(X0,X1,X6),X6)
        & m1_subset_1(sK7(X0,X1,X6),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r1_orders_2(X0,X5,X3)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X6] :
                      ( ( ( r2_hidden(X6,X2)
                          | ! [X7] :
                              ( ~ r2_hidden(X7,X1)
                              | ~ r1_orders_2(X0,X7,X6)
                              | ~ m1_subset_1(X7,u1_struct_0(X0)) ) )
                        & ( ? [X8] :
                              ( r2_hidden(X8,X1)
                              & r1_orders_2(X0,X8,X6)
                              & m1_subset_1(X8,u1_struct_0(X0)) )
                          | ~ r2_hidden(X6,X2) ) )
                      | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k4_waybel_0(X0,X1) = X2
                  | ? [X3] :
                      ( ( ! [X4] :
                            ( ~ r2_hidden(X4,X1)
                            | ~ r1_orders_2(X0,X4,X3)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        | ~ r2_hidden(X3,X2) )
                      & ( ? [X4] :
                            ( r2_hidden(X4,X1)
                            & r1_orders_2(X0,X4,X3)
                            & m1_subset_1(X4,u1_struct_0(X0)) )
                        | r2_hidden(X3,X2) )
                      & m1_subset_1(X3,u1_struct_0(X0)) ) )
                & ( ! [X3] :
                      ( ( ( r2_hidden(X3,X2)
                          | ! [X4] :
                              ( ~ r2_hidden(X4,X1)
                              | ~ r1_orders_2(X0,X4,X3)
                              | ~ m1_subset_1(X4,u1_struct_0(X0)) ) )
                        & ( ? [X4] :
                              ( r2_hidden(X4,X1)
                              & r1_orders_2(X0,X4,X3)
                              & m1_subset_1(X4,u1_struct_0(X0)) )
                          | ~ r2_hidden(X3,X2) ) )
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | k4_waybel_0(X0,X1) != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) )
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k4_waybel_0(X0,X1) = X2
              <=> ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_hidden(X3,X2)
                    <=> ? [X4] :
                          ( r2_hidden(X4,X1)
                          & r1_orders_2(X0,X4,X3)
                          & m1_subset_1(X4,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_waybel_0)).

fof(f204079,plain,
    ( r2_hidden(sK2(sK0,k4_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f126,f102,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f102,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_2
  <=> v2_waybel_0(k4_waybel_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f204077,plain,
    ( m1_subset_1(sK2(sK0,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f126,f102,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f126,plain,(
    m1_subset_1(k4_waybel_0(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f40,f41,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0) )
     => m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(f204101,plain,
    ( r2_hidden(sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1))),sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204077,f204079,f66])).

fof(f66,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | r2_hidden(sK7(X0,X1,X6),X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
      | ~ v2_waybel_0(sK1,sK0) )
    & ( v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
      | v2_waybel_0(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
              | ~ v2_waybel_0(X1,X0) )
            & ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
              | v2_waybel_0(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_waybel_0(k4_waybel_0(sK0,X1),sK0)
            | ~ v2_waybel_0(X1,sK0) )
          & ( v2_waybel_0(k4_waybel_0(sK0,X1),sK0)
            | v2_waybel_0(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ( ~ v2_waybel_0(k4_waybel_0(sK0,X1),sK0)
          | ~ v2_waybel_0(X1,sK0) )
        & ( v2_waybel_0(k4_waybel_0(sK0,X1),sK0)
          | v2_waybel_0(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
        | ~ v2_waybel_0(sK1,sK0) )
      & ( v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
        | v2_waybel_0(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
            | ~ v2_waybel_0(X1,X0) )
          & ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_waybel_0(k4_waybel_0(X0,X1),X0)
            | ~ v2_waybel_0(X1,X0) )
          & ( v2_waybel_0(k4_waybel_0(X0,X1),X0)
            | v2_waybel_0(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> v2_waybel_0(k4_waybel_0(X0,X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_waybel_0(X1,X0)
          <~> v2_waybel_0(k4_waybel_0(X0,X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_waybel_0(X1,X0)
            <=> v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_waybel_0(X1,X0)
          <=> v2_waybel_0(k4_waybel_0(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_waybel_0)).

fof(f204095,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),u1_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204076,f204078,f68])).

fof(f204078,plain,
    ( r2_hidden(sK3(sK0,k4_waybel_0(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f126,f102,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f204076,plain,
    ( m1_subset_1(sK3(sK0,k4_waybel_0(sK0,sK1)),u1_struct_0(sK0))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f126,f102,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f204097,plain,
    ( r2_hidden(sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK1)
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204076,f204078,f66])).

fof(f97,plain,
    ( v2_waybel_0(sK1,sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl9_1
  <=> v2_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f40,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f38,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f221617,plain,
    ( ~ r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f204122,f204118,f41,f126,f204118,f221598,f65])).

fof(f65,plain,(
    ! [X6,X0,X7,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X6,k4_waybel_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r1_orders_2(X0,X7,X6)
      | ~ m1_subset_1(X7,u1_struct_0(X0))
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f221598,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),k4_waybel_0(sK0,sK1))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f102,f126,f204118,f221475,f221575,f52])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,sK3(X0,X1))
      | ~ r1_orders_2(X0,X4,sK2(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f221575,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK2(sK0,k4_waybel_0(sK0,sK1)))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f39,f40,f204077,f204100,f204099,f204118,f204130,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f204130,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1))))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f97,f204097,f204095,f41,f204101,f204099,f47])).

fof(f47,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK4(X0,X1,X5,X6),X6) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f204100,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1))),sK2(sK0,k4_waybel_0(sK0,sK1)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204077,f204079,f67])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( ~ r2_hidden(X6,k4_waybel_0(X0,X1))
      | r1_orders_2(X0,sK7(X0,X1,X6),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(k4_waybel_0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X6,X2,X0,X1] :
      ( r1_orders_2(X0,sK7(X0,X1,X6),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | k4_waybel_0(X0,X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f39,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f221475,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK3(sK0,k4_waybel_0(sK0,sK1)))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f39,f40,f204076,f204096,f204095,f204118,f204126,f63])).

fof(f204126,plain,
    ( r1_orders_2(sK0,sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))))
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f97,f204097,f204095,f41,f204101,f204099,f46])).

fof(f46,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_orders_2(X0,sK4(X0,X1,X5,X6),X5) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f204096,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK3(sK0,k4_waybel_0(sK0,sK1)))
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f204076,f204078,f67])).

fof(f204122,plain,
    ( r2_hidden(sK4(sK0,sK1,sK7(sK0,sK1,sK3(sK0,k4_waybel_0(sK0,sK1))),sK7(sK0,sK1,sK2(sK0,k4_waybel_0(sK0,sK1)))),sK1)
    | ~ spl9_1
    | spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f97,f204097,f204095,f41,f204101,f204099,f45])).

fof(f45,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X6,X1)
      | ~ r2_hidden(X5,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v2_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(sK4(X0,X1,X5,X6),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f204074,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f204073])).

fof(f204073,plain,
    ( $false
    | spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f204057,f204016])).

fof(f204016,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),sK3(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f39,f40,f144,f226,f214,f664,f665,f63])).

fof(f665,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f214,f218,f67])).

fof(f218,plain,
    ( r2_hidden(sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),k4_waybel_0(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f141,f196,f101,f144,f126,f197,f45])).

fof(f197,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_waybel_0(sK0,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f144,f145,f137,f144,f41,f126,f65])).

fof(f137,plain,
    ( r2_hidden(sK3(sK0,sK1),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f98,f41,f51])).

fof(f98,plain,
    ( ~ v2_waybel_0(sK1,sK0)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f145,plain,
    ( r1_orders_2(sK0,sK3(sK0,sK1),sK3(sK0,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f37,f38,f40,f144,f62])).

fof(f101,plain,
    ( v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f196,plain,
    ( r2_hidden(sK2(sK0,sK1),k4_waybel_0(sK0,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f141,f142,f135,f141,f41,f126,f65])).

fof(f135,plain,
    ( r2_hidden(sK2(sK0,sK1),sK1)
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f98,f41,f50])).

fof(f142,plain,
    ( r1_orders_2(sK0,sK2(sK0,sK1),sK2(sK0,sK1))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f37,f38,f40,f141,f62])).

fof(f141,plain,
    ( m1_subset_1(sK2(sK0,sK1),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f98,f41,f48])).

fof(f664,plain,
    ( m1_subset_1(sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f214,f218,f68])).

fof(f214,plain,
    ( m1_subset_1(sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),u1_struct_0(sK0))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f141,f196,f101,f144,f126,f197,f44])).

fof(f226,plain,
    ( r1_orders_2(sK0,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),sK3(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f141,f196,f101,f144,f126,f197,f47])).

fof(f144,plain,
    ( m1_subset_1(sK3(sK0,sK1),u1_struct_0(sK0))
    | spl9_1 ),
    inference(unit_resulting_resolution,[],[f40,f98,f41,f49])).

fof(f204057,plain,
    ( ~ r1_orders_2(sK0,sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),sK3(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f98,f41,f666,f664,f204015,f52])).

fof(f204015,plain,
    ( r1_orders_2(sK0,sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),sK2(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f39,f40,f141,f222,f214,f664,f665,f63])).

fof(f222,plain,
    ( r1_orders_2(sK0,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1)),sK2(sK0,sK1))
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f141,f196,f101,f144,f126,f197,f46])).

fof(f666,plain,
    ( r2_hidden(sK7(sK0,sK1,sK4(sK0,k4_waybel_0(sK0,sK1),sK2(sK0,sK1),sK3(sK0,sK1))),sK1)
    | spl9_1
    | ~ spl9_2 ),
    inference(unit_resulting_resolution,[],[f40,f41,f126,f214,f218,f66])).

fof(f104,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f42,f100,f96])).

fof(f42,plain,
    ( v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
    | v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f43,f100,f96])).

fof(f43,plain,
    ( ~ v2_waybel_0(k4_waybel_0(sK0,sK1),sK0)
    | ~ v2_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------
