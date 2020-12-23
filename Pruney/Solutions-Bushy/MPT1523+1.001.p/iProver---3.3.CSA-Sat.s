%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1523+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:46 EST 2020

% Result     : CounterSatisfiable 2.04s
% Output     : Saturation 2.04s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 989 expanded)
%              Number of clauses        :   86 ( 224 expanded)
%              Number of leaves         :   14 ( 410 expanded)
%              Depth                    :   13
%              Number of atoms          :  530 (10922 expanded)
%              Number of equality atoms :  204 (2820 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( X3 = X5
                                & X2 = X4 )
                             => ( ( r2_orders_2(X0,X2,X3)
                                 => r2_orders_2(X1,X4,X5) )
                                & ( r1_orders_2(X0,X2,X3)
                                 => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X1))
                             => ( ( X3 = X5
                                  & X2 = X4 )
                               => ( ( r2_orders_2(X0,X2,X3)
                                   => r2_orders_2(X1,X4,X5) )
                                  & ( r1_orders_2(X0,X2,X3)
                                   => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f21,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ( ( ~ r2_orders_2(X1,X4,X5)
              & r2_orders_2(X0,X2,X3) )
            | ( ~ r1_orders_2(X1,X4,X5)
              & r1_orders_2(X0,X2,X3) ) )
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ( ( ~ r2_orders_2(X1,X4,sK5)
            & r2_orders_2(X0,X2,X3) )
          | ( ~ r1_orders_2(X1,X4,sK5)
            & r1_orders_2(X0,X2,X3) ) )
        & sK5 = X3
        & X2 = X4
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ( ( ~ r2_orders_2(X1,X4,X5)
                  & r2_orders_2(X0,X2,X3) )
                | ( ~ r1_orders_2(X1,X4,X5)
                  & r1_orders_2(X0,X2,X3) ) )
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ( ( ~ r2_orders_2(X1,sK4,X5)
                & r2_orders_2(X0,X2,X3) )
              | ( ~ r1_orders_2(X1,sK4,X5)
                & r1_orders_2(X0,X2,X3) ) )
            & X3 = X5
            & sK4 = X2
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( ( ~ r2_orders_2(X1,X4,X5)
                      & r2_orders_2(X0,X2,X3) )
                    | ( ~ r1_orders_2(X1,X4,X5)
                      & r1_orders_2(X0,X2,X3) ) )
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ( ( ~ r2_orders_2(X1,X4,X5)
                    & r2_orders_2(X0,X2,sK3) )
                  | ( ~ r1_orders_2(X1,X4,X5)
                    & r1_orders_2(X0,X2,sK3) ) )
                & sK3 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( ( ~ r2_orders_2(X1,X4,X5)
                          & r2_orders_2(X0,X2,X3) )
                        | ( ~ r1_orders_2(X1,X4,X5)
                          & r1_orders_2(X0,X2,X3) ) )
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( ( ~ r2_orders_2(X1,X4,X5)
                        & r2_orders_2(X0,sK2,X3) )
                      | ( ~ r1_orders_2(X1,X4,X5)
                        & r1_orders_2(X0,sK2,X3) ) )
                    & X3 = X5
                    & sK2 = X4
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(X0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(X0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( ( ~ r2_orders_2(sK1,X4,X5)
                            & r2_orders_2(X0,X2,X3) )
                          | ( ~ r1_orders_2(sK1,X4,X5)
                            & r1_orders_2(X0,X2,X3) ) )
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK1)) )
                    & m1_subset_1(X4,u1_struct_0(sK1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( ( ~ r2_orders_2(X1,X4,X5)
                                & r2_orders_2(X0,X2,X3) )
                              | ( ~ r1_orders_2(X1,X4,X5)
                                & r1_orders_2(X0,X2,X3) ) )
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( ( ~ r2_orders_2(X1,X4,X5)
                              & r2_orders_2(sK0,X2,X3) )
                            | ( ~ r1_orders_2(X1,X4,X5)
                              & r1_orders_2(sK0,X2,X3) ) )
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( ~ r2_orders_2(sK1,sK4,sK5)
        & r2_orders_2(sK0,sK2,sK3) )
      | ( ~ r1_orders_2(sK1,sK4,sK5)
        & r1_orders_2(sK0,sK2,sK3) ) )
    & sK3 = sK5
    & sK2 = sK4
    & m1_subset_1(sK5,u1_struct_0(sK1))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))
    & l1_orders_2(sK1)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f21,f20,f19,f18,f17,f16])).

fof(f36,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f24])).

fof(f32,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(X0,X1,X2)
      | X1 = X2
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f41,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

fof(f40,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f22])).

fof(f43,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ r1_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_175,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_173,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_170,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_631,plain,
    ( X0_2 = X0_2 ),
    theory(equality)).

cnf(c_15,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_905,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_223,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_19])).

cnf(c_224,plain,
    ( ~ r2_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_223])).

cnf(c_901,plain,
    ( r2_orders_2(sK1,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_2136,plain,
    ( r2_orders_2(sK1,sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_901])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_906,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2135,plain,
    ( r2_orders_2(sK1,sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_901])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_281,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_282,plain,
    ( ~ r2_orders_2(sK0,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_281])).

cnf(c_899,plain,
    ( r2_orders_2(sK0,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_282])).

cnf(c_18,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_907,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1494,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_907])).

cnf(c_5,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_36,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ l1_orders_2(sK0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1495,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_907])).

cnf(c_1512,plain,
    ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1495])).

cnf(c_1596,plain,
    ( u1_struct_0(sK0) = X0
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1494,c_20,c_36,c_1512])).

cnf(c_1597,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK0) = X0 ),
    inference(renaming,[status(thm)],[c_1596])).

cnf(c_1602,plain,
    ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(equality_resolution,[status(thm)],[c_1597])).

cnf(c_2074,plain,
    ( r2_orders_2(sK0,X0,X0) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_899,c_1602])).

cnf(c_2081,plain,
    ( r2_orders_2(sK0,sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_905,c_2074])).

cnf(c_2080,plain,
    ( r2_orders_2(sK0,sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_906,c_2074])).

cnf(c_2,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_205,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_19])).

cnf(c_206,plain,
    ( r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_205])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | X2 = X1 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_293,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X2 = X1
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_294,plain,
    ( ~ r1_orders_2(sK0,X0,X1)
    | r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_293])).

cnf(c_445,plain,
    ( r2_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK1,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | X0 != X2
    | X1 != X3
    | X1 = X0
    | sK0 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_206,c_294])).

cnf(c_446,plain,
    ( r2_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0
    | sK0 != sK1 ),
    inference(unflattening,[status(thm)],[c_445])).

cnf(c_895,plain,
    ( X0 = X1
    | sK0 != sK1
    | r2_orders_2(sK0,X1,X0) = iProver_top
    | r2_orders_2(sK1,X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1978,plain,
    ( X0 = X1
    | sK0 != sK1
    | r2_orders_2(sK0,X0,X1) = iProver_top
    | r2_orders_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_895,c_1602])).

cnf(c_235,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | X2 = X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_19])).

cnf(c_236,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_235])).

cnf(c_263,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_264,plain,
    ( r1_orders_2(sK0,X0,X1)
    | ~ r2_orders_2(sK0,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
    inference(unflattening,[status(thm)],[c_263])).

cnf(c_473,plain,
    ( ~ r2_orders_2(sK0,X0,X1)
    | r2_orders_2(sK1,X2,X3)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | X0 != X2
    | X1 != X3
    | X3 = X2
    | sK0 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_236,c_264])).

cnf(c_474,plain,
    ( ~ r2_orders_2(sK0,X0,X1)
    | r2_orders_2(sK1,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | X1 = X0
    | sK0 != sK1 ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_894,plain,
    ( X0 = X1
    | sK0 != sK1
    | r2_orders_2(sK0,X1,X0) != iProver_top
    | r2_orders_2(sK1,X1,X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_1731,plain,
    ( X0 = X1
    | sK0 != sK1
    | r2_orders_2(sK0,X0,X1) != iProver_top
    | r2_orders_2(sK1,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1602,c_894])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_908,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1519,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_908])).

cnf(c_21,plain,
    ( l1_orders_2(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_35,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_37,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
    | l1_orders_2(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_1520,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1
    | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_908])).

cnf(c_1614,plain,
    ( u1_orders_2(sK0) = X1
    | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1519,c_21,c_37,c_1520])).

cnf(c_1615,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK0) = X1 ),
    inference(renaming,[status(thm)],[c_1614])).

cnf(c_1620,plain,
    ( u1_orders_2(sK1) = u1_orders_2(sK0) ),
    inference(equality_resolution,[status(thm)],[c_1615])).

cnf(c_1622,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK1) = X1 ),
    inference(demodulation,[status(thm)],[c_1620,c_1615])).

cnf(c_1604,plain,
    ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK1) = X0 ),
    inference(demodulation,[status(thm)],[c_1602,c_1597])).

cnf(c_10,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,negated_conjecture,
    ( r1_orders_2(sK0,sK2,sK3)
    | r2_orders_2(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_348,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | sK3 != sK5
    | sK2 != sK4
    | sK0 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_11])).

cnf(c_13,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_12,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_350,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | sK0 != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_348,c_13,c_12])).

cnf(c_898,plain,
    ( sK0 != sK1
    | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_930,plain,
    ( sK0 != sK1
    | r2_orders_2(sK0,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_898,c_12,c_13])).

cnf(c_429,plain,
    ( r2_orders_2(sK0,X0,X1)
    | r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(X1,u1_struct_0(sK0))
    | ~ m1_subset_1(X0,u1_struct_0(sK0))
    | X1 = X0
    | sK3 != X1
    | sK2 != X0
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_294])).

cnf(c_430,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK3 = sK2 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_432,plain,
    ( r2_orders_2(sK0,sK2,sK3)
    | sK3 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_430,c_17,c_16])).

cnf(c_896,plain,
    ( sK3 = sK2
    | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_925,plain,
    ( sK5 = sK4
    | r2_orders_2(sK0,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_896,c_12,c_13])).

cnf(c_8,negated_conjecture,
    ( ~ r1_orders_2(sK1,sK4,sK5)
    | ~ r2_orders_2(sK1,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_400,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,sK4,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | sK5 != X1
    | sK4 != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_206])).

cnf(c_401,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_403,plain,
    ( ~ r2_orders_2(sK1,sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_15,c_14])).

cnf(c_897,plain,
    ( r2_orders_2(sK1,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_198,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_19])).

cnf(c_199,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_198])).

cnf(c_902,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_199])).


%------------------------------------------------------------------------------
