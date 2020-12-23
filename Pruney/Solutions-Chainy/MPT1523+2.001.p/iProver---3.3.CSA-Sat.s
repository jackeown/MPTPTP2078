%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:22 EST 2020

% Result     : CounterSatisfiable 1.91s
% Output     : Saturation 1.91s
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:07:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.91/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/0.98  
% 1.91/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/0.98  
% 1.91/0.98  ------  iProver source info
% 1.91/0.98  
% 1.91/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.91/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/0.98  git: non_committed_changes: false
% 1.91/0.98  git: last_make_outside_of_git: false
% 1.91/0.98  
% 1.91/0.98  ------ 
% 1.91/0.98  
% 1.91/0.98  ------ Input Options
% 1.91/0.98  
% 1.91/0.98  --out_options                           all
% 1.91/0.98  --tptp_safe_out                         true
% 1.91/0.98  --problem_path                          ""
% 1.91/0.98  --include_path                          ""
% 1.91/0.98  --clausifier                            res/vclausify_rel
% 1.91/0.98  --clausifier_options                    --mode clausify
% 1.91/0.98  --stdin                                 false
% 1.91/0.98  --stats_out                             all
% 1.91/0.98  
% 1.91/0.98  ------ General Options
% 1.91/0.98  
% 1.91/0.98  --fof                                   false
% 1.91/0.98  --time_out_real                         305.
% 1.91/0.98  --time_out_virtual                      -1.
% 1.91/0.98  --symbol_type_check                     false
% 1.91/0.98  --clausify_out                          false
% 1.91/0.98  --sig_cnt_out                           false
% 1.91/0.98  --trig_cnt_out                          false
% 1.91/0.98  --trig_cnt_out_tolerance                1.
% 1.91/0.98  --trig_cnt_out_sk_spl                   false
% 1.91/0.98  --abstr_cl_out                          false
% 1.91/0.98  
% 1.91/0.98  ------ Global Options
% 1.91/0.98  
% 1.91/0.98  --schedule                              default
% 1.91/0.98  --add_important_lit                     false
% 1.91/0.98  --prop_solver_per_cl                    1000
% 1.91/0.98  --min_unsat_core                        false
% 1.91/0.98  --soft_assumptions                      false
% 1.91/0.98  --soft_lemma_size                       3
% 1.91/0.98  --prop_impl_unit_size                   0
% 1.91/0.98  --prop_impl_unit                        []
% 1.91/0.98  --share_sel_clauses                     true
% 1.91/0.98  --reset_solvers                         false
% 1.91/0.98  --bc_imp_inh                            [conj_cone]
% 1.91/0.98  --conj_cone_tolerance                   3.
% 1.91/0.98  --extra_neg_conj                        none
% 1.91/0.98  --large_theory_mode                     true
% 1.91/0.98  --prolific_symb_bound                   200
% 1.91/0.98  --lt_threshold                          2000
% 1.91/0.98  --clause_weak_htbl                      true
% 1.91/0.98  --gc_record_bc_elim                     false
% 1.91/0.98  
% 1.91/0.98  ------ Preprocessing Options
% 1.91/0.98  
% 1.91/0.98  --preprocessing_flag                    true
% 1.91/0.98  --time_out_prep_mult                    0.1
% 1.91/0.98  --splitting_mode                        input
% 1.91/0.98  --splitting_grd                         true
% 1.91/0.98  --splitting_cvd                         false
% 1.91/0.98  --splitting_cvd_svl                     false
% 1.91/0.98  --splitting_nvd                         32
% 1.91/0.98  --sub_typing                            true
% 1.91/0.98  --prep_gs_sim                           true
% 1.91/0.98  --prep_unflatten                        true
% 1.91/0.98  --prep_res_sim                          true
% 1.91/0.98  --prep_upred                            true
% 1.91/0.98  --prep_sem_filter                       exhaustive
% 1.91/0.98  --prep_sem_filter_out                   false
% 1.91/0.98  --pred_elim                             true
% 1.91/0.98  --res_sim_input                         true
% 1.91/0.98  --eq_ax_congr_red                       true
% 1.91/0.98  --pure_diseq_elim                       true
% 1.91/0.98  --brand_transform                       false
% 1.91/0.98  --non_eq_to_eq                          false
% 1.91/0.98  --prep_def_merge                        true
% 1.91/0.98  --prep_def_merge_prop_impl              false
% 1.91/0.98  --prep_def_merge_mbd                    true
% 1.91/0.98  --prep_def_merge_tr_red                 false
% 1.91/0.98  --prep_def_merge_tr_cl                  false
% 1.91/0.98  --smt_preprocessing                     true
% 1.91/0.98  --smt_ac_axioms                         fast
% 1.91/0.98  --preprocessed_out                      false
% 1.91/0.98  --preprocessed_stats                    false
% 1.91/0.98  
% 1.91/0.98  ------ Abstraction refinement Options
% 1.91/0.98  
% 1.91/0.98  --abstr_ref                             []
% 1.91/0.98  --abstr_ref_prep                        false
% 1.91/0.98  --abstr_ref_until_sat                   false
% 1.91/0.98  --abstr_ref_sig_restrict                funpre
% 1.91/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/0.98  --abstr_ref_under                       []
% 1.91/0.98  
% 1.91/0.98  ------ SAT Options
% 1.91/0.98  
% 1.91/0.98  --sat_mode                              false
% 1.91/0.98  --sat_fm_restart_options                ""
% 1.91/0.98  --sat_gr_def                            false
% 1.91/0.98  --sat_epr_types                         true
% 1.91/0.98  --sat_non_cyclic_types                  false
% 1.91/0.98  --sat_finite_models                     false
% 1.91/0.98  --sat_fm_lemmas                         false
% 1.91/0.98  --sat_fm_prep                           false
% 1.91/0.98  --sat_fm_uc_incr                        true
% 1.91/0.98  --sat_out_model                         small
% 1.91/0.98  --sat_out_clauses                       false
% 1.91/0.98  
% 1.91/0.98  ------ QBF Options
% 1.91/0.98  
% 1.91/0.98  --qbf_mode                              false
% 1.91/0.98  --qbf_elim_univ                         false
% 1.91/0.98  --qbf_dom_inst                          none
% 1.91/0.98  --qbf_dom_pre_inst                      false
% 1.91/0.98  --qbf_sk_in                             false
% 1.91/0.98  --qbf_pred_elim                         true
% 1.91/0.98  --qbf_split                             512
% 1.91/0.98  
% 1.91/0.98  ------ BMC1 Options
% 1.91/0.98  
% 1.91/0.98  --bmc1_incremental                      false
% 1.91/0.98  --bmc1_axioms                           reachable_all
% 1.91/0.98  --bmc1_min_bound                        0
% 1.91/0.98  --bmc1_max_bound                        -1
% 1.91/0.98  --bmc1_max_bound_default                -1
% 1.91/0.98  --bmc1_symbol_reachability              true
% 1.91/0.98  --bmc1_property_lemmas                  false
% 1.91/0.98  --bmc1_k_induction                      false
% 1.91/0.98  --bmc1_non_equiv_states                 false
% 1.91/0.98  --bmc1_deadlock                         false
% 1.91/0.98  --bmc1_ucm                              false
% 1.91/0.98  --bmc1_add_unsat_core                   none
% 1.91/0.98  --bmc1_unsat_core_children              false
% 1.91/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/0.98  --bmc1_out_stat                         full
% 1.91/0.98  --bmc1_ground_init                      false
% 1.91/0.98  --bmc1_pre_inst_next_state              false
% 1.91/0.98  --bmc1_pre_inst_state                   false
% 1.91/0.98  --bmc1_pre_inst_reach_state             false
% 1.91/0.98  --bmc1_out_unsat_core                   false
% 1.91/0.98  --bmc1_aig_witness_out                  false
% 1.91/0.98  --bmc1_verbose                          false
% 1.91/0.98  --bmc1_dump_clauses_tptp                false
% 1.91/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.91/0.98  --bmc1_dump_file                        -
% 1.91/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.91/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.91/0.98  --bmc1_ucm_extend_mode                  1
% 1.91/0.98  --bmc1_ucm_init_mode                    2
% 1.91/0.98  --bmc1_ucm_cone_mode                    none
% 1.91/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.91/0.98  --bmc1_ucm_relax_model                  4
% 1.91/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.91/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/0.98  --bmc1_ucm_layered_model                none
% 1.91/0.98  --bmc1_ucm_max_lemma_size               10
% 1.91/0.98  
% 1.91/0.98  ------ AIG Options
% 1.91/0.98  
% 1.91/0.98  --aig_mode                              false
% 1.91/0.98  
% 1.91/0.98  ------ Instantiation Options
% 1.91/0.98  
% 1.91/0.98  --instantiation_flag                    true
% 1.91/0.98  --inst_sos_flag                         false
% 1.91/0.98  --inst_sos_phase                        true
% 1.91/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/0.98  --inst_lit_sel_side                     num_symb
% 1.91/0.98  --inst_solver_per_active                1400
% 1.91/0.98  --inst_solver_calls_frac                1.
% 1.91/0.98  --inst_passive_queue_type               priority_queues
% 1.91/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/0.98  --inst_passive_queues_freq              [25;2]
% 1.91/0.98  --inst_dismatching                      true
% 1.91/0.98  --inst_eager_unprocessed_to_passive     true
% 1.91/0.98  --inst_prop_sim_given                   true
% 1.91/0.98  --inst_prop_sim_new                     false
% 1.91/0.98  --inst_subs_new                         false
% 1.91/0.98  --inst_eq_res_simp                      false
% 1.91/0.98  --inst_subs_given                       false
% 1.91/0.98  --inst_orphan_elimination               true
% 1.91/0.98  --inst_learning_loop_flag               true
% 1.91/0.98  --inst_learning_start                   3000
% 1.91/0.98  --inst_learning_factor                  2
% 1.91/0.98  --inst_start_prop_sim_after_learn       3
% 1.91/0.98  --inst_sel_renew                        solver
% 1.91/0.98  --inst_lit_activity_flag                true
% 1.91/0.98  --inst_restr_to_given                   false
% 1.91/0.98  --inst_activity_threshold               500
% 1.91/0.98  --inst_out_proof                        true
% 1.91/0.98  
% 1.91/0.98  ------ Resolution Options
% 1.91/0.98  
% 1.91/0.98  --resolution_flag                       true
% 1.91/0.98  --res_lit_sel                           adaptive
% 1.91/0.98  --res_lit_sel_side                      none
% 1.91/0.98  --res_ordering                          kbo
% 1.91/0.98  --res_to_prop_solver                    active
% 1.91/0.98  --res_prop_simpl_new                    false
% 1.91/0.98  --res_prop_simpl_given                  true
% 1.91/0.98  --res_passive_queue_type                priority_queues
% 1.91/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/0.98  --res_passive_queues_freq               [15;5]
% 1.91/0.98  --res_forward_subs                      full
% 1.91/0.98  --res_backward_subs                     full
% 1.91/0.98  --res_forward_subs_resolution           true
% 1.91/0.98  --res_backward_subs_resolution          true
% 1.91/0.98  --res_orphan_elimination                true
% 1.91/0.98  --res_time_limit                        2.
% 1.91/0.98  --res_out_proof                         true
% 1.91/0.98  
% 1.91/0.98  ------ Superposition Options
% 1.91/0.98  
% 1.91/0.98  --superposition_flag                    true
% 1.91/0.98  --sup_passive_queue_type                priority_queues
% 1.91/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.91/0.98  --demod_completeness_check              fast
% 1.91/0.98  --demod_use_ground                      true
% 1.91/0.98  --sup_to_prop_solver                    passive
% 1.91/0.98  --sup_prop_simpl_new                    true
% 1.91/0.98  --sup_prop_simpl_given                  true
% 1.91/0.98  --sup_fun_splitting                     false
% 1.91/0.98  --sup_smt_interval                      50000
% 1.91/0.98  
% 1.91/0.98  ------ Superposition Simplification Setup
% 1.91/0.98  
% 1.91/0.98  --sup_indices_passive                   []
% 1.91/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_full_bw                           [BwDemod]
% 1.91/0.98  --sup_immed_triv                        [TrivRules]
% 1.91/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_immed_bw_main                     []
% 1.91/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.98  
% 1.91/0.98  ------ Combination Options
% 1.91/0.98  
% 1.91/0.98  --comb_res_mult                         3
% 1.91/0.98  --comb_sup_mult                         2
% 1.91/0.98  --comb_inst_mult                        10
% 1.91/0.98  
% 1.91/0.98  ------ Debug Options
% 1.91/0.98  
% 1.91/0.98  --dbg_backtrace                         false
% 1.91/0.98  --dbg_dump_prop_clauses                 false
% 1.91/0.98  --dbg_dump_prop_clauses_file            -
% 1.91/0.98  --dbg_out_stat                          false
% 1.91/0.98  ------ Parsing...
% 1.91/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/0.98  
% 1.91/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.91/0.98  
% 1.91/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/0.98  
% 1.91/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/0.98  ------ Proving...
% 1.91/0.98  ------ Problem Properties 
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  clauses                                 18
% 1.91/0.98  conjectures                             7
% 1.91/0.98  EPR                                     5
% 1.91/0.98  Horn                                    15
% 1.91/0.98  unary                                   10
% 1.91/0.98  binary                                  4
% 1.91/0.98  lits                                    40
% 1.91/0.98  lits eq                                 13
% 1.91/0.98  fd_pure                                 0
% 1.91/0.98  fd_pseudo                               0
% 1.91/0.98  fd_cond                                 0
% 1.91/0.98  fd_pseudo_cond                          4
% 1.91/0.98  AC symbols                              0
% 1.91/0.98  
% 1.91/0.98  ------ Schedule dynamic 5 is on 
% 1.91/0.98  
% 1.91/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  ------ 
% 1.91/0.98  Current options:
% 1.91/0.98  ------ 
% 1.91/0.98  
% 1.91/0.98  ------ Input Options
% 1.91/0.98  
% 1.91/0.98  --out_options                           all
% 1.91/0.98  --tptp_safe_out                         true
% 1.91/0.98  --problem_path                          ""
% 1.91/0.98  --include_path                          ""
% 1.91/0.98  --clausifier                            res/vclausify_rel
% 1.91/0.98  --clausifier_options                    --mode clausify
% 1.91/0.98  --stdin                                 false
% 1.91/0.98  --stats_out                             all
% 1.91/0.98  
% 1.91/0.98  ------ General Options
% 1.91/0.98  
% 1.91/0.98  --fof                                   false
% 1.91/0.98  --time_out_real                         305.
% 1.91/0.98  --time_out_virtual                      -1.
% 1.91/0.98  --symbol_type_check                     false
% 1.91/0.98  --clausify_out                          false
% 1.91/0.98  --sig_cnt_out                           false
% 1.91/0.98  --trig_cnt_out                          false
% 1.91/0.98  --trig_cnt_out_tolerance                1.
% 1.91/0.98  --trig_cnt_out_sk_spl                   false
% 1.91/0.98  --abstr_cl_out                          false
% 1.91/0.98  
% 1.91/0.98  ------ Global Options
% 1.91/0.98  
% 1.91/0.98  --schedule                              default
% 1.91/0.98  --add_important_lit                     false
% 1.91/0.98  --prop_solver_per_cl                    1000
% 1.91/0.98  --min_unsat_core                        false
% 1.91/0.98  --soft_assumptions                      false
% 1.91/0.98  --soft_lemma_size                       3
% 1.91/0.98  --prop_impl_unit_size                   0
% 1.91/0.98  --prop_impl_unit                        []
% 1.91/0.98  --share_sel_clauses                     true
% 1.91/0.98  --reset_solvers                         false
% 1.91/0.98  --bc_imp_inh                            [conj_cone]
% 1.91/0.98  --conj_cone_tolerance                   3.
% 1.91/0.98  --extra_neg_conj                        none
% 1.91/0.98  --large_theory_mode                     true
% 1.91/0.98  --prolific_symb_bound                   200
% 1.91/0.98  --lt_threshold                          2000
% 1.91/0.98  --clause_weak_htbl                      true
% 1.91/0.98  --gc_record_bc_elim                     false
% 1.91/0.98  
% 1.91/0.98  ------ Preprocessing Options
% 1.91/0.98  
% 1.91/0.98  --preprocessing_flag                    true
% 1.91/0.98  --time_out_prep_mult                    0.1
% 1.91/0.98  --splitting_mode                        input
% 1.91/0.98  --splitting_grd                         true
% 1.91/0.98  --splitting_cvd                         false
% 1.91/0.98  --splitting_cvd_svl                     false
% 1.91/0.98  --splitting_nvd                         32
% 1.91/0.98  --sub_typing                            true
% 1.91/0.98  --prep_gs_sim                           true
% 1.91/0.98  --prep_unflatten                        true
% 1.91/0.98  --prep_res_sim                          true
% 1.91/0.98  --prep_upred                            true
% 1.91/0.98  --prep_sem_filter                       exhaustive
% 1.91/0.98  --prep_sem_filter_out                   false
% 1.91/0.98  --pred_elim                             true
% 1.91/0.98  --res_sim_input                         true
% 1.91/0.98  --eq_ax_congr_red                       true
% 1.91/0.98  --pure_diseq_elim                       true
% 1.91/0.98  --brand_transform                       false
% 1.91/0.98  --non_eq_to_eq                          false
% 1.91/0.98  --prep_def_merge                        true
% 1.91/0.98  --prep_def_merge_prop_impl              false
% 1.91/0.98  --prep_def_merge_mbd                    true
% 1.91/0.98  --prep_def_merge_tr_red                 false
% 1.91/0.98  --prep_def_merge_tr_cl                  false
% 1.91/0.98  --smt_preprocessing                     true
% 1.91/0.98  --smt_ac_axioms                         fast
% 1.91/0.98  --preprocessed_out                      false
% 1.91/0.98  --preprocessed_stats                    false
% 1.91/0.98  
% 1.91/0.98  ------ Abstraction refinement Options
% 1.91/0.98  
% 1.91/0.98  --abstr_ref                             []
% 1.91/0.98  --abstr_ref_prep                        false
% 1.91/0.98  --abstr_ref_until_sat                   false
% 1.91/0.98  --abstr_ref_sig_restrict                funpre
% 1.91/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/0.98  --abstr_ref_under                       []
% 1.91/0.98  
% 1.91/0.98  ------ SAT Options
% 1.91/0.98  
% 1.91/0.98  --sat_mode                              false
% 1.91/0.98  --sat_fm_restart_options                ""
% 1.91/0.98  --sat_gr_def                            false
% 1.91/0.98  --sat_epr_types                         true
% 1.91/0.98  --sat_non_cyclic_types                  false
% 1.91/0.98  --sat_finite_models                     false
% 1.91/0.98  --sat_fm_lemmas                         false
% 1.91/0.98  --sat_fm_prep                           false
% 1.91/0.98  --sat_fm_uc_incr                        true
% 1.91/0.98  --sat_out_model                         small
% 1.91/0.98  --sat_out_clauses                       false
% 1.91/0.98  
% 1.91/0.98  ------ QBF Options
% 1.91/0.98  
% 1.91/0.98  --qbf_mode                              false
% 1.91/0.98  --qbf_elim_univ                         false
% 1.91/0.98  --qbf_dom_inst                          none
% 1.91/0.98  --qbf_dom_pre_inst                      false
% 1.91/0.98  --qbf_sk_in                             false
% 1.91/0.98  --qbf_pred_elim                         true
% 1.91/0.98  --qbf_split                             512
% 1.91/0.98  
% 1.91/0.98  ------ BMC1 Options
% 1.91/0.98  
% 1.91/0.98  --bmc1_incremental                      false
% 1.91/0.98  --bmc1_axioms                           reachable_all
% 1.91/0.98  --bmc1_min_bound                        0
% 1.91/0.98  --bmc1_max_bound                        -1
% 1.91/0.98  --bmc1_max_bound_default                -1
% 1.91/0.98  --bmc1_symbol_reachability              true
% 1.91/0.98  --bmc1_property_lemmas                  false
% 1.91/0.98  --bmc1_k_induction                      false
% 1.91/0.98  --bmc1_non_equiv_states                 false
% 1.91/0.98  --bmc1_deadlock                         false
% 1.91/0.98  --bmc1_ucm                              false
% 1.91/0.98  --bmc1_add_unsat_core                   none
% 1.91/0.98  --bmc1_unsat_core_children              false
% 1.91/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/0.98  --bmc1_out_stat                         full
% 1.91/0.98  --bmc1_ground_init                      false
% 1.91/0.98  --bmc1_pre_inst_next_state              false
% 1.91/0.98  --bmc1_pre_inst_state                   false
% 1.91/0.98  --bmc1_pre_inst_reach_state             false
% 1.91/0.98  --bmc1_out_unsat_core                   false
% 1.91/0.98  --bmc1_aig_witness_out                  false
% 1.91/0.98  --bmc1_verbose                          false
% 1.91/0.98  --bmc1_dump_clauses_tptp                false
% 1.91/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.91/0.98  --bmc1_dump_file                        -
% 1.91/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.91/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.91/0.98  --bmc1_ucm_extend_mode                  1
% 1.91/0.98  --bmc1_ucm_init_mode                    2
% 1.91/0.98  --bmc1_ucm_cone_mode                    none
% 1.91/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.91/0.98  --bmc1_ucm_relax_model                  4
% 1.91/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.91/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/0.98  --bmc1_ucm_layered_model                none
% 1.91/0.98  --bmc1_ucm_max_lemma_size               10
% 1.91/0.98  
% 1.91/0.98  ------ AIG Options
% 1.91/0.98  
% 1.91/0.98  --aig_mode                              false
% 1.91/0.98  
% 1.91/0.98  ------ Instantiation Options
% 1.91/0.98  
% 1.91/0.98  --instantiation_flag                    true
% 1.91/0.98  --inst_sos_flag                         false
% 1.91/0.98  --inst_sos_phase                        true
% 1.91/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/0.98  --inst_lit_sel_side                     none
% 1.91/0.98  --inst_solver_per_active                1400
% 1.91/0.98  --inst_solver_calls_frac                1.
% 1.91/0.98  --inst_passive_queue_type               priority_queues
% 1.91/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/0.98  --inst_passive_queues_freq              [25;2]
% 1.91/0.98  --inst_dismatching                      true
% 1.91/0.98  --inst_eager_unprocessed_to_passive     true
% 1.91/0.98  --inst_prop_sim_given                   true
% 1.91/0.98  --inst_prop_sim_new                     false
% 1.91/0.98  --inst_subs_new                         false
% 1.91/0.98  --inst_eq_res_simp                      false
% 1.91/0.98  --inst_subs_given                       false
% 1.91/0.98  --inst_orphan_elimination               true
% 1.91/0.98  --inst_learning_loop_flag               true
% 1.91/0.98  --inst_learning_start                   3000
% 1.91/0.98  --inst_learning_factor                  2
% 1.91/0.98  --inst_start_prop_sim_after_learn       3
% 1.91/0.98  --inst_sel_renew                        solver
% 1.91/0.98  --inst_lit_activity_flag                true
% 1.91/0.98  --inst_restr_to_given                   false
% 1.91/0.98  --inst_activity_threshold               500
% 1.91/0.98  --inst_out_proof                        true
% 1.91/0.98  
% 1.91/0.98  ------ Resolution Options
% 1.91/0.98  
% 1.91/0.98  --resolution_flag                       false
% 1.91/0.98  --res_lit_sel                           adaptive
% 1.91/0.98  --res_lit_sel_side                      none
% 1.91/0.98  --res_ordering                          kbo
% 1.91/0.98  --res_to_prop_solver                    active
% 1.91/0.98  --res_prop_simpl_new                    false
% 1.91/0.98  --res_prop_simpl_given                  true
% 1.91/0.98  --res_passive_queue_type                priority_queues
% 1.91/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/0.98  --res_passive_queues_freq               [15;5]
% 1.91/0.98  --res_forward_subs                      full
% 1.91/0.98  --res_backward_subs                     full
% 1.91/0.98  --res_forward_subs_resolution           true
% 1.91/0.98  --res_backward_subs_resolution          true
% 1.91/0.98  --res_orphan_elimination                true
% 1.91/0.98  --res_time_limit                        2.
% 1.91/0.98  --res_out_proof                         true
% 1.91/0.98  
% 1.91/0.98  ------ Superposition Options
% 1.91/0.98  
% 1.91/0.98  --superposition_flag                    true
% 1.91/0.98  --sup_passive_queue_type                priority_queues
% 1.91/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.91/0.98  --demod_completeness_check              fast
% 1.91/0.98  --demod_use_ground                      true
% 1.91/0.98  --sup_to_prop_solver                    passive
% 1.91/0.98  --sup_prop_simpl_new                    true
% 1.91/0.98  --sup_prop_simpl_given                  true
% 1.91/0.98  --sup_fun_splitting                     false
% 1.91/0.98  --sup_smt_interval                      50000
% 1.91/0.98  
% 1.91/0.98  ------ Superposition Simplification Setup
% 1.91/0.98  
% 1.91/0.98  --sup_indices_passive                   []
% 1.91/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_full_bw                           [BwDemod]
% 1.91/0.98  --sup_immed_triv                        [TrivRules]
% 1.91/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_immed_bw_main                     []
% 1.91/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/0.98  
% 1.91/0.98  ------ Combination Options
% 1.91/0.98  
% 1.91/0.98  --comb_res_mult                         3
% 1.91/0.98  --comb_sup_mult                         2
% 1.91/0.98  --comb_inst_mult                        10
% 1.91/0.98  
% 1.91/0.98  ------ Debug Options
% 1.91/0.98  
% 1.91/0.98  --dbg_backtrace                         false
% 1.91/0.98  --dbg_dump_prop_clauses                 false
% 1.91/0.98  --dbg_dump_prop_clauses_file            -
% 1.91/0.98  --dbg_out_stat                          false
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  ------ Proving...
% 1.91/0.98  
% 1.91/0.98  
% 1.91/0.98  % SZS status CounterSatisfiable for theBenchmark.p
% 1.91/0.98  
% 1.91/0.98  % SZS output start Saturation for theBenchmark.p
% 1.91/0.98  
% 1.91/0.98  fof(f5,conjecture,(
% 1.91/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 1.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.98  
% 1.91/0.98  fof(f6,negated_conjecture,(
% 1.91/0.98    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => ((X3 = X5 & X2 = X4) => ((r2_orders_2(X0,X2,X3) => r2_orders_2(X1,X4,X5)) & (r1_orders_2(X0,X2,X3) => r1_orders_2(X1,X4,X5)))))))))))),
% 1.91/0.98    inference(negated_conjecture,[],[f5])).
% 1.91/0.98  
% 1.91/0.98  fof(f11,plain,(
% 1.91/0.98    ? [X0] : (? [X1] : ((? [X2] : (? [X3] : (? [X4] : (? [X5] : ((((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & (X3 = X5 & X2 = X4)) & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 1.91/0.98    inference(ennf_transformation,[],[f6])).
% 1.91/0.98  
% 1.91/0.98  fof(f12,plain,(
% 1.91/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 1.91/0.98    inference(flattening,[],[f11])).
% 1.91/0.98  
% 1.91/0.98  fof(f21,plain,(
% 1.91/0.98    ( ! [X4,X2,X0,X3,X1] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) => (((~r2_orders_2(X1,X4,sK5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,sK5) & r1_orders_2(X0,X2,X3))) & sK5 = X3 & X2 = X4 & m1_subset_1(sK5,u1_struct_0(X1)))) )),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f20,plain,(
% 1.91/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) => (? [X5] : (((~r2_orders_2(X1,sK4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,sK4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & sK4 = X2 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(X1)))) )),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f19,plain,(
% 1.91/0.98    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,sK3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,sK3))) & sK3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK3,u1_struct_0(X0)))) )),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f18,plain,(
% 1.91/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,sK2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,sK2,X3))) & X3 = X5 & sK2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f17,plain,(
% 1.91/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(sK1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(sK1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(sK1))) & m1_subset_1(X4,u1_struct_0(sK1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & l1_orders_2(sK1))) )),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f16,plain,(
% 1.91/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(X0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(X0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (((~r2_orders_2(X1,X4,X5) & r2_orders_2(sK0,X2,X3)) | (~r1_orders_2(X1,X4,X5) & r1_orders_2(sK0,X2,X3))) & X3 = X5 & X2 = X4 & m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK0))) & m1_subset_1(X2,u1_struct_0(sK0))) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(sK0))),
% 1.91/0.98    introduced(choice_axiom,[])).
% 1.91/0.98  
% 1.91/0.98  fof(f22,plain,(
% 1.91/0.98    (((((((~r2_orders_2(sK1,sK4,sK5) & r2_orders_2(sK0,sK2,sK3)) | (~r1_orders_2(sK1,sK4,sK5) & r1_orders_2(sK0,sK2,sK3))) & sK3 = sK5 & sK2 = sK4 & m1_subset_1(sK5,u1_struct_0(sK1))) & m1_subset_1(sK4,u1_struct_0(sK1))) & m1_subset_1(sK3,u1_struct_0(sK0))) & m1_subset_1(sK2,u1_struct_0(sK0))) & g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) & l1_orders_2(sK1)) & l1_orders_2(sK0)),
% 1.91/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f12,f21,f20,f19,f18,f17,f16])).
% 1.91/0.98  
% 1.91/0.98  fof(f36,plain,(
% 1.91/0.98    m1_subset_1(sK4,u1_struct_0(sK1))),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f1,axiom,(
% 1.91/0.98    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 1.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.98  
% 1.91/0.98  fof(f7,plain,(
% 1.91/0.98    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.91/0.98    inference(ennf_transformation,[],[f1])).
% 1.91/0.98  
% 1.91/0.98  fof(f13,plain,(
% 1.91/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.91/0.98    inference(nnf_transformation,[],[f7])).
% 1.91/0.98  
% 1.91/0.98  fof(f14,plain,(
% 1.91/0.98    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.91/0.98    inference(flattening,[],[f13])).
% 1.91/0.98  
% 1.91/0.98  fof(f24,plain,(
% 1.91/0.98    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.91/0.98    inference(cnf_transformation,[],[f14])).
% 1.91/0.98  
% 1.91/0.98  fof(f44,plain,(
% 1.91/0.98    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.91/0.98    inference(equality_resolution,[],[f24])).
% 1.91/0.98  
% 1.91/0.98  fof(f32,plain,(
% 1.91/0.98    l1_orders_2(sK1)),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f37,plain,(
% 1.91/0.98    m1_subset_1(sK5,u1_struct_0(sK1))),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f31,plain,(
% 1.91/0.98    l1_orders_2(sK0)),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f33,plain,(
% 1.91/0.98    g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1))),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f4,axiom,(
% 1.91/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 1.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.98  
% 1.91/0.98  fof(f10,plain,(
% 1.91/0.98    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 1.91/0.98    inference(ennf_transformation,[],[f4])).
% 1.91/0.98  
% 1.91/0.98  fof(f29,plain,(
% 1.91/0.98    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.91/0.98    inference(cnf_transformation,[],[f10])).
% 1.91/0.98  
% 1.91/0.98  fof(f3,axiom,(
% 1.91/0.98    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 1.91/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.91/0.98  
% 1.91/0.98  fof(f9,plain,(
% 1.91/0.98    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.91/0.98    inference(ennf_transformation,[],[f3])).
% 1.91/0.98  
% 1.91/0.98  fof(f28,plain,(
% 1.91/0.98    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 1.91/0.98    inference(cnf_transformation,[],[f9])).
% 1.91/0.98  
% 1.91/0.98  fof(f23,plain,(
% 1.91/0.98    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.91/0.98    inference(cnf_transformation,[],[f14])).
% 1.91/0.98  
% 1.91/0.98  fof(f25,plain,(
% 1.91/0.98    ( ! [X2,X0,X1] : (r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.91/0.98    inference(cnf_transformation,[],[f14])).
% 1.91/0.98  
% 1.91/0.98  fof(f30,plain,(
% 1.91/0.98    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.91/0.98    inference(cnf_transformation,[],[f10])).
% 1.91/0.98  
% 1.91/0.98  fof(f41,plain,(
% 1.91/0.98    r2_orders_2(sK0,sK2,sK3) | ~r1_orders_2(sK1,sK4,sK5)),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f40,plain,(
% 1.91/0.98    r2_orders_2(sK0,sK2,sK3) | r1_orders_2(sK0,sK2,sK3)),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f38,plain,(
% 1.91/0.98    sK2 = sK4),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f39,plain,(
% 1.91/0.98    sK3 = sK5),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f34,plain,(
% 1.91/0.98    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f35,plain,(
% 1.91/0.98    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  fof(f43,plain,(
% 1.91/0.98    ~r2_orders_2(sK1,sK4,sK5) | ~r1_orders_2(sK1,sK4,sK5)),
% 1.91/0.98    inference(cnf_transformation,[],[f22])).
% 1.91/0.98  
% 1.91/0.98  cnf(c_175,plain,
% 1.91/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.91/0.98      theory(equality) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_173,plain,
% 1.91/0.98      ( ~ l1_orders_2(X0) | l1_orders_2(X1) | X1 != X0 ),
% 1.91/0.98      theory(equality) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_170,plain,
% 1.91/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.98      | r1_orders_2(X3,X4,X5)
% 1.91/0.98      | X3 != X0
% 1.91/0.98      | X4 != X1
% 1.91/0.98      | X5 != X2 ),
% 1.91/0.98      theory(equality) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_631,plain,( X0_2 = X0_2 ),theory(equality) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_15,negated_conjecture,
% 1.91/0.98      ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 1.91/0.98      inference(cnf_transformation,[],[f36]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_905,plain,
% 1.91/0.98      ( m1_subset_1(sK4,u1_struct_0(sK1)) = iProver_top ),
% 1.91/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1,plain,
% 1.91/0.98      ( ~ r2_orders_2(X0,X1,X1)
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.98      | ~ l1_orders_2(X0) ),
% 1.91/0.98      inference(cnf_transformation,[],[f44]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_19,negated_conjecture,
% 1.91/0.98      ( l1_orders_2(sK1) ),
% 1.91/0.98      inference(cnf_transformation,[],[f32]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_223,plain,
% 1.91/0.98      ( ~ r2_orders_2(X0,X1,X1)
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.98      | sK1 != X0 ),
% 1.91/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_19]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_224,plain,
% 1.91/0.98      ( ~ r2_orders_2(sK1,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.91/0.98      inference(unflattening,[status(thm)],[c_223]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_901,plain,
% 1.91/0.98      ( r2_orders_2(sK1,X0,X0) != iProver_top
% 1.91/0.98      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.98      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2136,plain,
% 1.91/0.98      ( r2_orders_2(sK1,sK4,sK4) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_905,c_901]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_14,negated_conjecture,
% 1.91/0.98      ( m1_subset_1(sK5,u1_struct_0(sK1)) ),
% 1.91/0.98      inference(cnf_transformation,[],[f37]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_906,plain,
% 1.91/0.98      ( m1_subset_1(sK5,u1_struct_0(sK1)) = iProver_top ),
% 1.91/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2135,plain,
% 1.91/0.98      ( r2_orders_2(sK1,sK5,sK5) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_906,c_901]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_20,negated_conjecture,
% 1.91/0.98      ( l1_orders_2(sK0) ),
% 1.91/0.98      inference(cnf_transformation,[],[f31]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_281,plain,
% 1.91/0.98      ( ~ r2_orders_2(X0,X1,X1)
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.98      | sK0 != X0 ),
% 1.91/0.98      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_282,plain,
% 1.91/0.98      ( ~ r2_orders_2(sK0,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK0)) ),
% 1.91/0.98      inference(unflattening,[status(thm)],[c_281]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_899,plain,
% 1.91/0.98      ( r2_orders_2(sK0,X0,X0) != iProver_top
% 1.91/0.98      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top ),
% 1.91/0.98      inference(predicate_to_equality,[status(thm)],[c_282]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_18,negated_conjecture,
% 1.91/0.98      ( g1_orders_2(u1_struct_0(sK0),u1_orders_2(sK0)) = g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) ),
% 1.91/0.98      inference(cnf_transformation,[],[f33]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_7,plain,
% 1.91/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.91/0.98      | X2 = X1
% 1.91/0.98      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 1.91/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_907,plain,
% 1.91/0.98      ( X0 = X1
% 1.91/0.98      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 1.91/0.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 1.91/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1494,plain,
% 1.91/0.98      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.98      | u1_struct_0(sK0) = X0
% 1.91/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_18,c_907]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_5,plain,
% 1.91/0.98      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.91/0.98      | ~ l1_orders_2(X0) ),
% 1.91/0.98      inference(cnf_transformation,[],[f28]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_36,plain,
% 1.91/0.98      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 1.91/0.98      | ~ l1_orders_2(sK0) ),
% 1.91/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1495,plain,
% 1.91/0.98      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.98      | u1_struct_0(sK0) = X0
% 1.91/0.98      | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_18,c_907]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1512,plain,
% 1.91/0.98      ( ~ m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
% 1.91/0.98      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.98      | u1_struct_0(sK0) = X0 ),
% 1.91/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1495]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1596,plain,
% 1.91/0.98      ( u1_struct_0(sK0) = X0
% 1.91/0.98      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
% 1.91/0.98      inference(global_propositional_subsumption,
% 1.91/0.98                [status(thm)],
% 1.91/0.98                [c_1494,c_20,c_36,c_1512]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1597,plain,
% 1.91/0.98      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.98      | u1_struct_0(sK0) = X0 ),
% 1.91/0.98      inference(renaming,[status(thm)],[c_1596]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_1602,plain,
% 1.91/0.98      ( u1_struct_0(sK0) = u1_struct_0(sK1) ),
% 1.91/0.98      inference(equality_resolution,[status(thm)],[c_1597]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2074,plain,
% 1.91/0.98      ( r2_orders_2(sK0,X0,X0) != iProver_top
% 1.91/0.98      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.98      inference(light_normalisation,[status(thm)],[c_899,c_1602]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2081,plain,
% 1.91/0.98      ( r2_orders_2(sK0,sK4,sK4) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_905,c_2074]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2080,plain,
% 1.91/0.98      ( r2_orders_2(sK0,sK5,sK5) != iProver_top ),
% 1.91/0.98      inference(superposition,[status(thm)],[c_906,c_2074]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_2,plain,
% 1.91/0.98      ( r1_orders_2(X0,X1,X2)
% 1.91/0.98      | ~ r2_orders_2(X0,X1,X2)
% 1.91/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.98      | ~ l1_orders_2(X0) ),
% 1.91/0.98      inference(cnf_transformation,[],[f23]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_205,plain,
% 1.91/0.98      ( r1_orders_2(X0,X1,X2)
% 1.91/0.98      | ~ r2_orders_2(X0,X1,X2)
% 1.91/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.98      | sK1 != X0 ),
% 1.91/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_19]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_206,plain,
% 1.91/0.98      ( r1_orders_2(sK1,X0,X1)
% 1.91/0.98      | ~ r2_orders_2(sK1,X0,X1)
% 1.91/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.91/0.98      inference(unflattening,[status(thm)],[c_205]) ).
% 1.91/0.98  
% 1.91/0.98  cnf(c_0,plain,
% 1.91/0.98      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.98      | r2_orders_2(X0,X1,X2)
% 1.91/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.99      | ~ l1_orders_2(X0)
% 1.91/0.99      | X2 = X1 ),
% 1.91/0.99      inference(cnf_transformation,[],[f25]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_293,plain,
% 1.91/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.99      | r2_orders_2(X0,X1,X2)
% 1.91/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.99      | X2 = X1
% 1.91/0.99      | sK0 != X0 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_294,plain,
% 1.91/0.99      ( ~ r1_orders_2(sK0,X0,X1)
% 1.91/0.99      | r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | X1 = X0 ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_293]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_445,plain,
% 1.91/0.99      ( r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | ~ r2_orders_2(sK1,X2,X3)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.91/0.99      | X0 != X2
% 1.91/0.99      | X1 != X3
% 1.91/0.99      | X1 = X0
% 1.91/0.99      | sK0 != sK1 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_206,c_294]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_446,plain,
% 1.91/0.99      ( r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | ~ r2_orders_2(sK1,X0,X1)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.91/0.99      | X1 = X0
% 1.91/0.99      | sK0 != sK1 ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_445]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_895,plain,
% 1.91/0.99      ( X0 = X1
% 1.91/0.99      | sK0 != sK1
% 1.91/0.99      | r2_orders_2(sK0,X1,X0) = iProver_top
% 1.91/0.99      | r2_orders_2(sK1,X1,X0) != iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1978,plain,
% 1.91/0.99      ( X0 = X1
% 1.91/0.99      | sK0 != sK1
% 1.91/0.99      | r2_orders_2(sK0,X0,X1) = iProver_top
% 1.91/0.99      | r2_orders_2(sK1,X0,X1) != iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.99      inference(light_normalisation,[status(thm)],[c_895,c_1602]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_235,plain,
% 1.91/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 1.91/0.99      | r2_orders_2(X0,X1,X2)
% 1.91/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.99      | X2 = X1
% 1.91/0.99      | sK1 != X0 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_19]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_236,plain,
% 1.91/0.99      ( ~ r1_orders_2(sK1,X0,X1)
% 1.91/0.99      | r2_orders_2(sK1,X0,X1)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.91/0.99      | X1 = X0 ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_235]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_263,plain,
% 1.91/0.99      ( r1_orders_2(X0,X1,X2)
% 1.91/0.99      | ~ r2_orders_2(X0,X1,X2)
% 1.91/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.91/0.99      | sK0 != X0 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_20]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_264,plain,
% 1.91/0.99      ( r1_orders_2(sK0,X0,X1)
% 1.91/0.99      | ~ r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_263]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_473,plain,
% 1.91/0.99      ( ~ r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | r2_orders_2(sK1,X2,X3)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.91/0.99      | X0 != X2
% 1.91/0.99      | X1 != X3
% 1.91/0.99      | X3 = X2
% 1.91/0.99      | sK0 != sK1 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_236,c_264]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_474,plain,
% 1.91/0.99      ( ~ r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | r2_orders_2(sK1,X0,X1)
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.91/0.99      | X1 = X0
% 1.91/0.99      | sK0 != sK1 ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_894,plain,
% 1.91/0.99      ( X0 = X1
% 1.91/0.99      | sK0 != sK1
% 1.91/0.99      | r2_orders_2(sK0,X1,X0) != iProver_top
% 1.91/0.99      | r2_orders_2(sK1,X1,X0) = iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK0)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK0)) != iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1731,plain,
% 1.91/0.99      ( X0 = X1
% 1.91/0.99      | sK0 != sK1
% 1.91/0.99      | r2_orders_2(sK0,X0,X1) != iProver_top
% 1.91/0.99      | r2_orders_2(sK1,X0,X1) = iProver_top
% 1.91/0.99      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 1.91/0.99      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top ),
% 1.91/0.99      inference(demodulation,[status(thm)],[c_1602,c_894]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_6,plain,
% 1.91/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 1.91/0.99      | X2 = X0
% 1.91/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 1.91/0.99      inference(cnf_transformation,[],[f30]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_908,plain,
% 1.91/0.99      ( X0 = X1
% 1.91/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 1.91/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1519,plain,
% 1.91/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.99      | u1_orders_2(sK0) = X1
% 1.91/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 1.91/0.99      inference(superposition,[status(thm)],[c_18,c_908]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_21,plain,
% 1.91/0.99      ( l1_orders_2(sK0) = iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_35,plain,
% 1.91/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) = iProver_top
% 1.91/0.99      | l1_orders_2(X0) != iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_37,plain,
% 1.91/0.99      ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) = iProver_top
% 1.91/0.99      | l1_orders_2(sK0) != iProver_top ),
% 1.91/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1520,plain,
% 1.91/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.99      | u1_orders_2(sK0) = X1
% 1.91/0.99      | m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) != iProver_top ),
% 1.91/0.99      inference(superposition,[status(thm)],[c_18,c_908]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1614,plain,
% 1.91/0.99      ( u1_orders_2(sK0) = X1
% 1.91/0.99      | g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1) ),
% 1.91/0.99      inference(global_propositional_subsumption,
% 1.91/0.99                [status(thm)],
% 1.91/0.99                [c_1519,c_21,c_37,c_1520]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1615,plain,
% 1.91/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.99      | u1_orders_2(sK0) = X1 ),
% 1.91/0.99      inference(renaming,[status(thm)],[c_1614]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1620,plain,
% 1.91/0.99      ( u1_orders_2(sK1) = u1_orders_2(sK0) ),
% 1.91/0.99      inference(equality_resolution,[status(thm)],[c_1615]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1622,plain,
% 1.91/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.99      | u1_orders_2(sK1) = X1 ),
% 1.91/0.99      inference(demodulation,[status(thm)],[c_1620,c_1615]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_1604,plain,
% 1.91/0.99      ( g1_orders_2(u1_struct_0(sK1),u1_orders_2(sK1)) != g1_orders_2(X0,X1)
% 1.91/0.99      | u1_struct_0(sK1) = X0 ),
% 1.91/0.99      inference(demodulation,[status(thm)],[c_1602,c_1597]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_10,negated_conjecture,
% 1.91/0.99      ( ~ r1_orders_2(sK1,sK4,sK5) | r2_orders_2(sK0,sK2,sK3) ),
% 1.91/0.99      inference(cnf_transformation,[],[f41]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_11,negated_conjecture,
% 1.91/0.99      ( r1_orders_2(sK0,sK2,sK3) | r2_orders_2(sK0,sK2,sK3) ),
% 1.91/0.99      inference(cnf_transformation,[],[f40]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_348,plain,
% 1.91/0.99      ( r2_orders_2(sK0,sK2,sK3) | sK3 != sK5 | sK2 != sK4 | sK0 != sK1 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_11]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_13,negated_conjecture,
% 1.91/0.99      ( sK2 = sK4 ),
% 1.91/0.99      inference(cnf_transformation,[],[f38]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_12,negated_conjecture,
% 1.91/0.99      ( sK3 = sK5 ),
% 1.91/0.99      inference(cnf_transformation,[],[f39]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_350,plain,
% 1.91/0.99      ( r2_orders_2(sK0,sK2,sK3) | sK0 != sK1 ),
% 1.91/0.99      inference(global_propositional_subsumption,
% 1.91/0.99                [status(thm)],
% 1.91/0.99                [c_348,c_13,c_12]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_898,plain,
% 1.91/0.99      ( sK0 != sK1 | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_930,plain,
% 1.91/0.99      ( sK0 != sK1 | r2_orders_2(sK0,sK4,sK5) = iProver_top ),
% 1.91/0.99      inference(light_normalisation,[status(thm)],[c_898,c_12,c_13]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_429,plain,
% 1.91/0.99      ( r2_orders_2(sK0,X0,X1)
% 1.91/0.99      | r2_orders_2(sK0,sK2,sK3)
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK0))
% 1.91/0.99      | X1 = X0
% 1.91/0.99      | sK3 != X1
% 1.91/0.99      | sK2 != X0
% 1.91/0.99      | sK0 != sK0 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_294]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_430,plain,
% 1.91/0.99      ( r2_orders_2(sK0,sK2,sK3)
% 1.91/0.99      | ~ m1_subset_1(sK3,u1_struct_0(sK0))
% 1.91/0.99      | ~ m1_subset_1(sK2,u1_struct_0(sK0))
% 1.91/0.99      | sK3 = sK2 ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_17,negated_conjecture,
% 1.91/0.99      ( m1_subset_1(sK2,u1_struct_0(sK0)) ),
% 1.91/0.99      inference(cnf_transformation,[],[f34]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_16,negated_conjecture,
% 1.91/0.99      ( m1_subset_1(sK3,u1_struct_0(sK0)) ),
% 1.91/0.99      inference(cnf_transformation,[],[f35]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_432,plain,
% 1.91/0.99      ( r2_orders_2(sK0,sK2,sK3) | sK3 = sK2 ),
% 1.91/0.99      inference(global_propositional_subsumption,
% 1.91/0.99                [status(thm)],
% 1.91/0.99                [c_430,c_17,c_16]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_896,plain,
% 1.91/0.99      ( sK3 = sK2 | r2_orders_2(sK0,sK2,sK3) = iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_925,plain,
% 1.91/0.99      ( sK5 = sK4 | r2_orders_2(sK0,sK4,sK5) = iProver_top ),
% 1.91/0.99      inference(light_normalisation,[status(thm)],[c_896,c_12,c_13]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_8,negated_conjecture,
% 1.91/0.99      ( ~ r1_orders_2(sK1,sK4,sK5) | ~ r2_orders_2(sK1,sK4,sK5) ),
% 1.91/0.99      inference(cnf_transformation,[],[f43]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_400,plain,
% 1.91/0.99      ( ~ r2_orders_2(sK1,X0,X1)
% 1.91/0.99      | ~ r2_orders_2(sK1,sK4,sK5)
% 1.91/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.91/0.99      | sK5 != X1
% 1.91/0.99      | sK4 != X0
% 1.91/0.99      | sK1 != sK1 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_206]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_401,plain,
% 1.91/0.99      ( ~ r2_orders_2(sK1,sK4,sK5)
% 1.91/0.99      | ~ m1_subset_1(sK5,u1_struct_0(sK1))
% 1.91/0.99      | ~ m1_subset_1(sK4,u1_struct_0(sK1)) ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_403,plain,
% 1.91/0.99      ( ~ r2_orders_2(sK1,sK4,sK5) ),
% 1.91/0.99      inference(global_propositional_subsumption,
% 1.91/0.99                [status(thm)],
% 1.91/0.99                [c_401,c_15,c_14]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_897,plain,
% 1.91/0.99      ( r2_orders_2(sK1,sK4,sK5) != iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_198,plain,
% 1.91/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 1.91/0.99      | sK1 != X0 ),
% 1.91/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_19]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_199,plain,
% 1.91/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
% 1.91/0.99      inference(unflattening,[status(thm)],[c_198]) ).
% 1.91/0.99  
% 1.91/0.99  cnf(c_902,plain,
% 1.91/0.99      ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) = iProver_top ),
% 1.91/0.99      inference(predicate_to_equality,[status(thm)],[c_199]) ).
% 1.91/0.99  
% 1.91/0.99  
% 1.91/0.99  % SZS output end Saturation for theBenchmark.p
% 1.91/0.99  
% 1.91/0.99  ------                               Statistics
% 1.91/0.99  
% 1.91/0.99  ------ General
% 1.91/0.99  
% 1.91/0.99  abstr_ref_over_cycles:                  0
% 1.91/0.99  abstr_ref_under_cycles:                 0
% 1.91/0.99  gc_basic_clause_elim:                   0
% 1.91/0.99  forced_gc_time:                         0
% 1.91/0.99  parsing_time:                           0.026
% 1.91/0.99  unif_index_cands_time:                  0.
% 1.91/0.99  unif_index_add_time:                    0.
% 1.91/0.99  orderings_time:                         0.
% 1.91/0.99  out_proof_time:                         0.
% 1.91/0.99  total_time:                             0.133
% 1.91/0.99  num_of_symbols:                         48
% 1.91/0.99  num_of_terms:                           2636
% 1.91/0.99  
% 1.91/0.99  ------ Preprocessing
% 1.91/0.99  
% 1.91/0.99  num_of_splits:                          0
% 1.91/0.99  num_of_split_atoms:                     0
% 1.91/0.99  num_of_reused_defs:                     0
% 1.91/0.99  num_eq_ax_congr_red:                    2
% 1.91/0.99  num_of_sem_filtered_clauses:            1
% 1.91/0.99  num_of_subtypes:                        0
% 1.91/0.99  monotx_restored_types:                  0
% 1.91/0.99  sat_num_of_epr_types:                   0
% 1.91/0.99  sat_num_of_non_cyclic_types:            0
% 1.91/0.99  sat_guarded_non_collapsed_types:        0
% 1.91/0.99  num_pure_diseq_elim:                    0
% 1.91/0.99  simp_replaced_by:                       0
% 1.91/0.99  res_preprocessed:                       94
% 1.91/0.99  prep_upred:                             0
% 1.91/0.99  prep_unflattend:                        28
% 1.91/0.99  smt_new_axioms:                         0
% 1.91/0.99  pred_elim_cands:                        2
% 1.91/0.99  pred_elim:                              3
% 1.91/0.99  pred_elim_cl:                           3
% 1.91/0.99  pred_elim_cycles:                       5
% 1.91/0.99  merged_defs:                            0
% 1.91/0.99  merged_defs_ncl:                        0
% 1.91/0.99  bin_hyper_res:                          0
% 1.91/0.99  prep_cycles:                            4
% 1.91/0.99  pred_elim_time:                         0.005
% 1.91/0.99  splitting_time:                         0.
% 1.91/0.99  sem_filter_time:                        0.
% 1.91/0.99  monotx_time:                            0.
% 1.91/0.99  subtype_inf_time:                       0.
% 1.91/0.99  
% 1.91/0.99  ------ Problem properties
% 1.91/0.99  
% 1.91/0.99  clauses:                                18
% 1.91/0.99  conjectures:                            7
% 1.91/0.99  epr:                                    5
% 1.91/0.99  horn:                                   15
% 1.91/0.99  ground:                                 12
% 1.91/0.99  unary:                                  10
% 1.91/0.99  binary:                                 4
% 1.91/0.99  lits:                                   40
% 1.91/0.99  lits_eq:                                13
% 1.91/0.99  fd_pure:                                0
% 1.91/0.99  fd_pseudo:                              0
% 1.91/0.99  fd_cond:                                0
% 1.91/0.99  fd_pseudo_cond:                         4
% 1.91/0.99  ac_symbols:                             0
% 1.91/0.99  
% 1.91/0.99  ------ Propositional Solver
% 1.91/0.99  
% 1.91/0.99  prop_solver_calls:                      28
% 1.91/0.99  prop_fast_solver_calls:                 617
% 1.91/0.99  smt_solver_calls:                       0
% 1.91/0.99  smt_fast_solver_calls:                  0
% 1.91/0.99  prop_num_of_clauses:                    1034
% 1.91/0.99  prop_preprocess_simplified:             3109
% 1.91/0.99  prop_fo_subsumed:                       26
% 1.91/0.99  prop_solver_time:                       0.
% 1.91/0.99  smt_solver_time:                        0.
% 1.91/0.99  smt_fast_solver_time:                   0.
% 1.91/0.99  prop_fast_solver_time:                  0.
% 1.91/0.99  prop_unsat_core_time:                   0.
% 1.91/0.99  
% 1.91/0.99  ------ QBF
% 1.91/0.99  
% 1.91/0.99  qbf_q_res:                              0
% 1.91/0.99  qbf_num_tautologies:                    0
% 1.91/0.99  qbf_prep_cycles:                        0
% 1.91/0.99  
% 1.91/0.99  ------ BMC1
% 1.91/0.99  
% 1.91/0.99  bmc1_current_bound:                     -1
% 1.91/0.99  bmc1_last_solved_bound:                 -1
% 1.91/0.99  bmc1_unsat_core_size:                   -1
% 1.91/0.99  bmc1_unsat_core_parents_size:           -1
% 1.91/0.99  bmc1_merge_next_fun:                    0
% 1.91/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.91/0.99  
% 1.91/0.99  ------ Instantiation
% 1.91/0.99  
% 1.91/0.99  inst_num_of_clauses:                    298
% 1.91/0.99  inst_num_in_passive:                    109
% 1.91/0.99  inst_num_in_active:                     143
% 1.91/0.99  inst_num_in_unprocessed:                46
% 1.91/0.99  inst_num_of_loops:                      150
% 1.91/0.99  inst_num_of_learning_restarts:          0
% 1.91/0.99  inst_num_moves_active_passive:          4
% 1.91/0.99  inst_lit_activity:                      0
% 1.91/0.99  inst_lit_activity_moves:                0
% 1.91/0.99  inst_num_tautologies:                   0
% 1.91/0.99  inst_num_prop_implied:                  0
% 1.91/0.99  inst_num_existing_simplified:           0
% 1.91/0.99  inst_num_eq_res_simplified:             0
% 1.91/0.99  inst_num_child_elim:                    0
% 1.91/0.99  inst_num_of_dismatching_blockings:      7
% 1.91/0.99  inst_num_of_non_proper_insts:           360
% 1.91/0.99  inst_num_of_duplicates:                 0
% 1.91/0.99  inst_inst_num_from_inst_to_res:         0
% 1.91/0.99  inst_dismatching_checking_time:         0.
% 1.91/0.99  
% 1.91/0.99  ------ Resolution
% 1.91/0.99  
% 1.91/0.99  res_num_of_clauses:                     0
% 1.91/0.99  res_num_in_passive:                     0
% 1.91/0.99  res_num_in_active:                      0
% 1.91/0.99  res_num_of_loops:                       98
% 1.91/0.99  res_forward_subset_subsumed:            23
% 1.91/0.99  res_backward_subset_subsumed:           1
% 1.91/0.99  res_forward_subsumed:                   4
% 1.91/0.99  res_backward_subsumed:                  1
% 1.91/0.99  res_forward_subsumption_resolution:     0
% 1.91/0.99  res_backward_subsumption_resolution:    0
% 1.91/0.99  res_clause_to_clause_subsumption:       118
% 1.91/0.99  res_orphan_elimination:                 0
% 1.91/0.99  res_tautology_del:                      61
% 1.91/0.99  res_num_eq_res_simplified:              0
% 1.91/0.99  res_num_sel_changes:                    0
% 1.91/0.99  res_moves_from_active_to_pass:          0
% 1.91/0.99  
% 1.91/0.99  ------ Superposition
% 1.91/0.99  
% 1.91/0.99  sup_time_total:                         0.
% 1.91/0.99  sup_time_generating:                    0.
% 1.91/0.99  sup_time_sim_full:                      0.
% 1.91/0.99  sup_time_sim_immed:                     0.
% 1.91/0.99  
% 1.91/0.99  sup_num_of_clauses:                     26
% 1.91/0.99  sup_num_in_active:                      22
% 1.91/0.99  sup_num_in_passive:                     4
% 1.91/0.99  sup_num_of_loops:                       29
% 1.91/0.99  sup_fw_superposition:                   10
% 1.91/0.99  sup_bw_superposition:                   4
% 1.91/0.99  sup_immediate_simplified:               2
% 1.91/0.99  sup_given_eliminated:                   2
% 1.91/0.99  comparisons_done:                       0
% 1.91/0.99  comparisons_avoided:                    0
% 1.91/0.99  
% 1.91/0.99  ------ Simplifications
% 1.91/0.99  
% 1.91/0.99  
% 1.91/0.99  sim_fw_subset_subsumed:                 2
% 1.91/0.99  sim_bw_subset_subsumed:                 2
% 1.91/0.99  sim_fw_subsumed:                        0
% 1.91/0.99  sim_bw_subsumed:                        0
% 1.91/0.99  sim_fw_subsumption_res:                 0
% 1.91/0.99  sim_bw_subsumption_res:                 0
% 1.91/0.99  sim_tautology_del:                      0
% 1.91/0.99  sim_eq_tautology_del:                   7
% 1.91/0.99  sim_eq_res_simp:                        0
% 1.91/0.99  sim_fw_demodulated:                     0
% 1.91/0.99  sim_bw_demodulated:                     7
% 1.91/0.99  sim_light_normalised:                   7
% 1.91/0.99  sim_joinable_taut:                      0
% 1.91/0.99  sim_joinable_simp:                      0
% 1.91/0.99  sim_ac_normalised:                      0
% 1.91/0.99  sim_smt_subsumption:                    0
% 1.91/0.99  
%------------------------------------------------------------------------------
