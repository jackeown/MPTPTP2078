%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:04 EST 2020

% Result     : CounterSatisfiable 1.67s
% Output     : Saturation 1.67s
% Verified   : 
% Statistics : Number of formulae       :  148 (1462 expanded)
%              Number of clauses        :  106 ( 377 expanded)
%              Number of leaves         :   11 ( 508 expanded)
%              Depth                    :   21
%              Number of atoms          :  542 (11932 expanded)
%              Number of equality atoms :  252 (2905 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( ( v13_waybel_0(X2,X0)
                         => v13_waybel_0(X3,X1) )
                        & ( v12_waybel_0(X2,X0)
                         => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => ( ( v13_waybel_0(X2,X0)
                           => v13_waybel_0(X3,X1) )
                          & ( v12_waybel_0(X2,X0)
                           => v12_waybel_0(X3,X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ~ v13_waybel_0(X3,X1)
              & v13_waybel_0(X2,X0) )
            | ( ~ v12_waybel_0(X3,X1)
              & v12_waybel_0(X2,X0) ) )
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ( ~ v13_waybel_0(sK3,X1)
            & v13_waybel_0(X2,X0) )
          | ( ~ v12_waybel_0(sK3,X1)
            & v12_waybel_0(X2,X0) ) )
        & sK3 = X2
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ~ v13_waybel_0(X3,X1)
                  & v13_waybel_0(X2,X0) )
                | ( ~ v12_waybel_0(X3,X1)
                  & v12_waybel_0(X2,X0) ) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ( ( ~ v13_waybel_0(X3,X1)
                & v13_waybel_0(sK2,X0) )
              | ( ~ v12_waybel_0(X3,X1)
                & v12_waybel_0(sK2,X0) ) )
            & sK2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,X0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,X0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ~ v13_waybel_0(X3,sK1)
                    & v13_waybel_0(X2,X0) )
                  | ( ~ v12_waybel_0(X3,sK1)
                    & v12_waybel_0(X2,X0) ) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ~ v13_waybel_0(X3,X1)
                        & v13_waybel_0(X2,X0) )
                      | ( ~ v12_waybel_0(X3,X1)
                        & v12_waybel_0(X2,X0) ) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ v13_waybel_0(X3,X1)
                      & v13_waybel_0(X2,sK0) )
                    | ( ~ v12_waybel_0(X3,X1)
                      & v12_waybel_0(X2,sK0) ) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( ~ v13_waybel_0(sK3,sK1)
        & v13_waybel_0(sK2,sK0) )
      | ( ~ v12_waybel_0(sK3,sK1)
        & v12_waybel_0(sK2,sK0) ) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f21,f20,f19,f18])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                        & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
                    & k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( k4_waybel_0(X0,X2) = k4_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( k4_waybel_0(X0,X3) = k4_waybel_0(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f33,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_waybel_0(X0,X2) = k3_waybel_0(X1,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( k3_waybel_0(X0,X3) = k3_waybel_0(X1,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v12_waybel_0(X1,X0)
          <=> r1_tarski(k3_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v12_waybel_0(X1,X0)
              | ~ r1_tarski(k3_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k3_waybel_0(X0,X1),X1)
              | ~ v12_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v12_waybel_0(X1,X0)
      | ~ r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f41,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_waybel_0(X0,X1),X1)
      | ~ v12_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> r1_tarski(k4_waybel_0(X0,X1),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ~ r1_tarski(k4_waybel_0(X0,X1),X1) )
            & ( r1_tarski(k4_waybel_0(X0,X1),X1)
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_waybel_0(X0,X1),X1)
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_159,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_838,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_16,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_841,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1273,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_841])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_0,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_50,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1274,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_841])).

cnf(c_1291,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1274])).

cnf(c_1376,plain,
    ( u1_struct_0(sK0) = X0
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1273,c_18,c_50,c_1291])).

cnf(c_1377,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1376])).

cnf(c_1382,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1377])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | k4_waybel_0(X1,X0) = k4_waybel_0(X2,X0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_840,plain,
    ( k4_waybel_0(X0,X1) = k4_waybel_0(X2,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1885,plain,
    ( k4_waybel_0(X0,X1) = k4_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_840])).

cnf(c_1714,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(demodulation,[status(thm)],[c_1382,c_16])).

cnf(c_1894,plain,
    ( k4_waybel_0(X0,X1) = k4_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1885,c_1382,c_1714])).

cnf(c_19,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2274,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | k4_waybel_0(X0,X1) = k4_waybel_0(sK0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1894,c_19])).

cnf(c_2275,plain,
    ( k4_waybel_0(X0,X1) = k4_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2274])).

cnf(c_2285,plain,
    ( k4_waybel_0(sK1,X0) = k4_waybel_0(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2275])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_20,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2564,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k4_waybel_0(sK1,X0) = k4_waybel_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2285,c_20])).

cnf(c_2565,plain,
    ( k4_waybel_0(sK1,X0) = k4_waybel_0(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2564])).

cnf(c_2572,plain,
    ( k4_waybel_0(sK1,sK3) = k4_waybel_0(sK0,sK3) ),
    inference(superposition,[status(thm)],[c_838,c_2565])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | k3_waybel_0(X1,X0) = k3_waybel_0(X2,X0)
    | g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_839,plain,
    ( k3_waybel_0(X0,X1) = k3_waybel_0(X2,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X2),u1_orders_2(X2))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1774,plain,
    ( k3_waybel_0(X0,X1) = k3_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK0))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_839])).

cnf(c_1783,plain,
    ( k3_waybel_0(X0,X1) = k3_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1774,c_1382,c_1714])).

cnf(c_2172,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | k3_waybel_0(X0,X1) = k3_waybel_0(sK0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_19])).

cnf(c_2173,plain,
    ( k3_waybel_0(X0,X1) = k3_waybel_0(sK0,X1)
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2172])).

cnf(c_2183,plain,
    ( k3_waybel_0(sK1,X0) = k3_waybel_0(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2173])).

cnf(c_2351,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | k3_waybel_0(sK1,X0) = k3_waybel_0(sK0,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2183,c_20])).

cnf(c_2352,plain,
    ( k3_waybel_0(sK1,X0) = k3_waybel_0(sK0,X0)
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2351])).

cnf(c_2359,plain,
    ( k3_waybel_0(sK0,sK3) = k3_waybel_0(sK1,sK3) ),
    inference(superposition,[status(thm)],[c_838,c_2352])).

cnf(c_5,plain,
    ( ~ r1_tarski(k3_waybel_0(X0,X1),X1)
    | v12_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_9,negated_conjecture,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_274,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ r1_tarski(k3_waybel_0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_9])).

cnf(c_275,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_277,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_275,c_17,c_14])).

cnf(c_6,plain,
    ( r1_tarski(k3_waybel_0(X0,X1),X1)
    | ~ v12_waybel_0(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_10,negated_conjecture,
    ( ~ v13_waybel_0(sK3,sK1)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_302,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | r1_tarski(k3_waybel_0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | sK0 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_10])).

cnf(c_303,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | r1_tarski(k3_waybel_0(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_302])).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_305,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | r1_tarski(k3_waybel_0(sK0,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_303,c_18,c_15])).

cnf(c_457,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_277,c_305])).

cnf(c_13,negated_conjecture,
    ( sK2 = sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_459,plain,
    ( k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | ~ v13_waybel_0(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_457,c_13])).

cnf(c_460,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3) ),
    inference(renaming,[status(thm)],[c_459])).

cnf(c_828,plain,
    ( k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_460])).

cnf(c_871,plain,
    ( k3_waybel_0(sK0,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_828,c_13])).

cnf(c_2363,plain,
    ( k3_waybel_0(sK1,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2359,c_871])).

cnf(c_2368,plain,
    ( v13_waybel_0(sK3,sK1) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2363])).

cnf(c_11,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | ~ v12_waybel_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_260,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ r1_tarski(k3_waybel_0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_261,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_263,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ r1_tarski(k3_waybel_0(sK1,sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_261,c_17,c_14])).

cnf(c_12,negated_conjecture,
    ( v13_waybel_0(sK2,sK0)
    | v12_waybel_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_288,plain,
    ( v13_waybel_0(sK2,sK0)
    | r1_tarski(k3_waybel_0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | sK0 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_12])).

cnf(c_289,plain,
    ( v13_waybel_0(sK2,sK0)
    | r1_tarski(k3_waybel_0(sK0,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_291,plain,
    ( v13_waybel_0(sK2,sK0)
    | r1_tarski(k3_waybel_0(sK0,sK2),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_18,c_15])).

cnf(c_472,plain,
    ( v13_waybel_0(sK2,sK0)
    | k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_263,c_291])).

cnf(c_474,plain,
    ( k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_13])).

cnf(c_475,plain,
    ( v13_waybel_0(sK2,sK0)
    | k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3) ),
    inference(renaming,[status(thm)],[c_474])).

cnf(c_827,plain,
    ( k3_waybel_0(sK0,sK2) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_866,plain,
    ( k3_waybel_0(sK0,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_827,c_13])).

cnf(c_2364,plain,
    ( k3_waybel_0(sK1,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,sK0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2359,c_866])).

cnf(c_2365,plain,
    ( v13_waybel_0(sK3,sK0) = iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2364])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_842,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1354,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_842])).

cnf(c_1355,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_842])).

cnf(c_1372,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1355])).

cnf(c_1501,plain,
    ( u1_orders_2(sK0) = X1
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1354,c_18,c_50,c_1372])).

cnf(c_1502,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_1501])).

cnf(c_1507,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_1502])).

cnf(c_843,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1717,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_843])).

cnf(c_1905,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1717,c_19])).

cnf(c_2019,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1507,c_1905])).

cnf(c_1509,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1 ),
    inference(demodulation,[status(thm)],[c_1507,c_1502])).

cnf(c_1384,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(demodulation,[status(thm)],[c_1382,c_1377])).

cnf(c_8,plain,
    ( ~ v13_waybel_0(X0,X1)
    | r1_tarski(k4_waybel_0(X1,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_394,plain,
    ( ~ v13_waybel_0(X0,X1)
    | v13_waybel_0(sK2,sK0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | k4_waybel_0(X1,X0) != k3_waybel_0(sK1,sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_263])).

cnf(c_395,plain,
    ( v13_waybel_0(sK2,sK0)
    | ~ v13_waybel_0(sK3,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | k4_waybel_0(X0,sK3) != k3_waybel_0(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_831,plain,
    ( k4_waybel_0(X0,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK2,sK0) = iProver_top
    | v13_waybel_0(sK3,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_914,plain,
    ( k4_waybel_0(X0,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,X0) != iProver_top
    | v13_waybel_0(sK3,sK0) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_831,c_13])).

cnf(c_316,plain,
    ( v13_waybel_0(sK2,sK0)
    | sK0 != sK1
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_12])).

cnf(c_318,plain,
    ( sK0 != sK1
    | v13_waybel_0(sK2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_13])).

cnf(c_319,plain,
    ( v13_waybel_0(sK2,sK0)
    | sK0 != sK1 ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_834,plain,
    ( sK0 != sK1
    | v13_waybel_0(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_855,plain,
    ( sK0 != sK1
    | v13_waybel_0(sK3,sK0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_834,c_13])).

cnf(c_373,plain,
    ( ~ v13_waybel_0(X0,X1)
    | ~ v13_waybel_0(sK3,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | k4_waybel_0(X1,X0) != k3_waybel_0(sK1,sK3)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_277])).

cnf(c_374,plain,
    ( ~ v13_waybel_0(sK3,X0)
    | ~ v13_waybel_0(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_orders_2(X0)
    | k4_waybel_0(X0,sK3) != k3_waybel_0(sK1,sK3) ),
    inference(unflattening,[status(thm)],[c_373])).

cnf(c_832,plain,
    ( k4_waybel_0(X0,sK3) != k3_waybel_0(sK1,sK3)
    | v13_waybel_0(sK3,X0) != iProver_top
    | v13_waybel_0(sK3,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_374])).

cnf(c_341,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | sK0 != sK1
    | sK2 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_10])).

cnf(c_343,plain,
    ( sK0 != sK1
    | ~ v13_waybel_0(sK3,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_13])).

cnf(c_344,plain,
    ( ~ v13_waybel_0(sK3,sK1)
    | sK0 != sK1 ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_833,plain,
    ( sK0 != sK1
    | v13_waybel_0(sK3,sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_836,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_835,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).


%------------------------------------------------------------------------------
