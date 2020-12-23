%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1584+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:57 EST 2020

% Result     : Theorem 2.26s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 636 expanded)
%              Number of clauses        :  118 ( 162 expanded)
%              Number of leaves         :   13 ( 208 expanded)
%              Depth                    :   18
%              Number of atoms          :  795 (5685 expanded)
%              Number of equality atoms :  154 ( 643 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X4,X5)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X0,X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_orders_2(X0,X2,X3)
                          | ~ r1_orders_2(X1,X4,X5)
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X1,X4,X5)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f56,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X0,X4,X5)
      | ~ r1_orders_2(X1,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f55])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r2_lattice3(X1,X2,X4)
                           => r2_lattice3(X0,X2,X3) )
                          & ( r1_lattice3(X1,X2,X4)
                           => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f8,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_yellow_0(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ( X3 = X4
                         => ( ( r2_lattice3(X1,X2,X4)
                             => r2_lattice3(X0,X2,X3) )
                            & ( r1_lattice3(X1,X2,X4)
                             => r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ( ~ r2_lattice3(X0,X2,X3)
              & r2_lattice3(X1,X2,X4) )
            | ( ~ r1_lattice3(X0,X2,X3)
              & r1_lattice3(X1,X2,X4) ) )
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ( ( ~ r2_lattice3(X0,X2,X3)
            & r2_lattice3(X1,X2,sK6) )
          | ( ~ r1_lattice3(X0,X2,X3)
            & r1_lattice3(X1,X2,sK6) ) )
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ( ~ r2_lattice3(X0,X2,X3)
                  & r2_lattice3(X1,X2,X4) )
                | ( ~ r1_lattice3(X0,X2,X3)
                  & r1_lattice3(X1,X2,X4) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ( ~ r2_lattice3(X0,X2,sK5)
                & r2_lattice3(X1,X2,X4) )
              | ( ~ r1_lattice3(X0,X2,sK5)
                & r1_lattice3(X1,X2,X4) ) )
            & sK5 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ( ~ r2_lattice3(X0,X2,X3)
                      & r2_lattice3(X1,X2,X4) )
                    | ( ~ r1_lattice3(X0,X2,X3)
                      & r1_lattice3(X1,X2,X4) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ( ~ r2_lattice3(X0,sK4,X3)
                    & r2_lattice3(X1,sK4,X4) )
                  | ( ~ r1_lattice3(X0,sK4,X3)
                    & r1_lattice3(X1,sK4,X4) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(X0,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(X0,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ( ~ r2_lattice3(X0,X2,X3)
                        & r2_lattice3(sK3,X2,X4) )
                      | ( ~ r1_lattice3(X0,X2,X3)
                        & r1_lattice3(sK3,X2,X4) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(sK3)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK3))) )
        & m1_yellow_0(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ( ~ r2_lattice3(X0,X2,X3)
                            & r2_lattice3(X1,X2,X4) )
                          | ( ~ r1_lattice3(X0,X2,X3)
                            & r1_lattice3(X1,X2,X4) ) )
                        & X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ( ~ r2_lattice3(sK2,X2,X3)
                          & r2_lattice3(X1,X2,X4) )
                        | ( ~ r1_lattice3(sK2,X2,X3)
                          & r1_lattice3(X1,X2,X4) ) )
                      & X3 = X4
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK2)) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_yellow_0(X1,sK2) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ( ( ~ r2_lattice3(sK2,sK4,sK5)
        & r2_lattice3(sK3,sK4,sK6) )
      | ( ~ r1_lattice3(sK2,sK4,sK5)
        & r1_lattice3(sK3,sK4,sK6) ) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & m1_yellow_0(sK3,sK2)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f19,f32,f31,f30,f29,f28])).

fof(f46,plain,(
    m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f45,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
                & r2_hidden(sK1(X0,X1,X2),X1)
                & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f42,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
                & r2_hidden(sK0(X0,X1,X2),X1)
                & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,
    ( r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,
    ( r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f53,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_10,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_yellow_0(X0,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( m1_yellow_0(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_226,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ l1_orders_2(X3)
    | sK3 != X0
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_227,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_226])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_231,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | r1_orders_2(sK2,X0,X1)
    | ~ r1_orders_2(sK3,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_227,c_20])).

cnf(c_232,plain,
    ( ~ r1_orders_2(sK3,X0,X1)
    | r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_2857,plain,
    ( ~ r1_orders_2(sK3,X0_45,X1_45)
    | r1_orders_2(sK2,X0_45,X1_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_232])).

cnf(c_5207,plain,
    ( ~ r1_orders_2(sK3,sK1(sK2,X0_45,sK5),X1_45)
    | r1_orders_2(sK2,sK1(sK2,X0_45,sK5),X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | ~ m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_6061,plain,
    ( ~ r1_orders_2(sK3,sK1(sK2,X0_45,sK5),sK5)
    | r1_orders_2(sK2,sK1(sK2,X0_45,sK5),sK5)
    | ~ m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_5207])).

cnf(c_6062,plain,
    ( r1_orders_2(sK3,sK1(sK2,X0_45,sK5),sK5) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_45,sK5),sK5) = iProver_top
    | m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6061])).

cnf(c_6064,plain,
    ( r1_orders_2(sK3,sK1(sK2,sK4,sK5),sK5) != iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK4,sK5),sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6062])).

cnf(c_3752,plain,
    ( ~ r1_orders_2(sK3,sK5,X0_45)
    | r1_orders_2(sK2,sK5,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_5652,plain,
    ( ~ r1_orders_2(sK3,sK5,sK0(sK2,sK4,sK5))
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3752])).

cnf(c_5653,plain,
    ( r1_orders_2(sK3,sK5,sK0(sK2,sK4,sK5)) != iProver_top
    | r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5652])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_8,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_215,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK3 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_216,plain,
    ( l1_orders_2(sK3)
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_215])).

cnf(c_218,plain,
    ( l1_orders_2(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_216,c_20])).

cnf(c_597,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_218])).

cnf(c_598,plain,
    ( ~ r2_lattice3(sK3,X0,X1)
    | r1_orders_2(sK3,X2,X1)
    | ~ r2_hidden(X2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X2,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_597])).

cnf(c_2848,plain,
    ( ~ r2_lattice3(sK3,X0_45,X1_45)
    | r1_orders_2(sK3,X2_45,X1_45)
    | ~ r2_hidden(X2_45,X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X2_45,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_598])).

cnf(c_3765,plain,
    ( ~ r2_lattice3(sK3,X0_45,sK5)
    | r1_orders_2(sK3,X1_45,sK5)
    | ~ r2_hidden(X1_45,X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2848])).

cnf(c_5144,plain,
    ( ~ r2_lattice3(sK3,X0_45,sK5)
    | r1_orders_2(sK3,sK1(sK2,sK4,sK5),sK5)
    | ~ r2_hidden(sK1(sK2,sK4,sK5),X0_45)
    | ~ m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3765])).

cnf(c_5180,plain,
    ( r2_lattice3(sK3,X0_45,sK5) != iProver_top
    | r1_orders_2(sK3,sK1(sK2,sK4,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK4,sK5),X0_45) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5144])).

cnf(c_5182,plain,
    ( r2_lattice3(sK3,sK4,sK5) != iProver_top
    | r1_orders_2(sK3,sK1(sK2,sK4,sK5),sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5180])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_663,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_218])).

cnf(c_664,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ r1_lattice3(sK3,X2,X0)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_663])).

cnf(c_2844,plain,
    ( r1_orders_2(sK3,X0_45,X1_45)
    | ~ r1_lattice3(sK3,X2_45,X0_45)
    | ~ r2_hidden(X1_45,X2_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_664])).

cnf(c_3750,plain,
    ( r1_orders_2(sK3,sK5,X0_45)
    | ~ r1_lattice3(sK3,X1_45,sK5)
    | ~ r2_hidden(X0_45,X1_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_4740,plain,
    ( r1_orders_2(sK3,sK5,sK0(sK2,sK4,sK5))
    | ~ r1_lattice3(sK3,X0_45,sK5)
    | ~ r2_hidden(sK0(sK2,sK4,sK5),X0_45)
    | ~ m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_3750])).

cnf(c_4761,plain,
    ( r1_orders_2(sK3,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | r1_lattice3(sK3,X0_45,sK5) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),X0_45) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4740])).

cnf(c_4763,plain,
    ( r1_orders_2(sK3,sK5,sK0(sK2,sK4,sK5)) = iProver_top
    | r1_lattice3(sK3,sK4,sK5) != iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4761])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_2866,plain,
    ( ~ r2_hidden(X0_45,X1_45)
    | m1_subset_1(X0_45,X0_46)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(X0_46)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_4099,plain,
    ( ~ r2_hidden(sK0(sK2,X0_45,sK5),X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | m1_subset_1(sK0(sK2,X0_45,sK5),X0_46) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_4387,plain,
    ( ~ r2_hidden(sK0(sK2,sK4,sK5),sK4)
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_4099])).

cnf(c_4388,plain,
    ( r2_hidden(sK0(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4387])).

cnf(c_3868,plain,
    ( ~ r2_hidden(sK1(sK2,X0_45,sK5),X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(X0_46))
    | m1_subset_1(sK1(sK2,X0_45,sK5),X0_46) ),
    inference(instantiation,[status(thm)],[c_2866])).

cnf(c_4246,plain,
    ( ~ r2_hidden(sK1(sK2,sK4,sK5),sK4)
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_3868])).

cnf(c_4247,plain,
    ( r2_hidden(sK1(sK2,sK4,sK5),sK4) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4246])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_501,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_20])).

cnf(c_502,plain,
    ( r2_lattice3(sK2,X0,X1)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_2854,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | r2_hidden(sK1(sK2,X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_3573,plain,
    ( r2_lattice3(sK2,X0_45,sK5)
    | r2_hidden(sK1(sK2,X0_45,sK5),X0_45)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2854])).

cnf(c_3574,plain,
    ( r2_lattice3(sK2,X0_45,sK5) = iProver_top
    | r2_hidden(sK1(sK2,X0_45,sK5),X0_45) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3573])).

cnf(c_3576,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK1(sK2,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3574])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_516,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_20])).

cnf(c_517,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_2853,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_45,X1_45),X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_517])).

cnf(c_3568,plain,
    ( r2_lattice3(sK2,X0_45,sK5)
    | ~ r1_orders_2(sK2,sK1(sK2,X0_45,sK5),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2853])).

cnf(c_3569,plain,
    ( r2_lattice3(sK2,X0_45,sK5) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,X0_45,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3568])).

cnf(c_3571,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_orders_2(sK2,sK1(sK2,sK4,sK5),sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_567,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_568,plain,
    ( r1_lattice3(sK2,X0,X1)
    | r2_hidden(sK0(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_2850,plain,
    ( r1_lattice3(sK2,X0_45,X1_45)
    | r2_hidden(sK0(sK2,X0_45,X1_45),X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_568])).

cnf(c_3563,plain,
    ( r1_lattice3(sK2,X0_45,sK5)
    | r2_hidden(sK0(sK2,X0_45,sK5),X0_45)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2850])).

cnf(c_3564,plain,
    ( r1_lattice3(sK2,X0_45,sK5) = iProver_top
    | r2_hidden(sK0(sK2,X0_45,sK5),X0_45) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3563])).

cnf(c_3566,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3564])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_582,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_583,plain,
    ( ~ r1_orders_2(sK2,X0,sK0(sK2,X1,X0))
    | r1_lattice3(sK2,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_582])).

cnf(c_2849,plain,
    ( ~ r1_orders_2(sK2,X0_45,sK0(sK2,X1_45,X0_45))
    | r1_lattice3(sK2,X1_45,X0_45)
    | ~ m1_subset_1(X0_45,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_583])).

cnf(c_3558,plain,
    ( ~ r1_orders_2(sK2,sK5,sK0(sK2,X0_45,sK5))
    | r1_lattice3(sK2,X0_45,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2849])).

cnf(c_3559,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,X0_45,sK5)) != iProver_top
    | r1_lattice3(sK2,X0_45,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3558])).

cnf(c_3561,plain,
    ( r1_orders_2(sK2,sK5,sK0(sK2,sK4,sK5)) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3559])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_486,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_20])).

cnf(c_487,plain,
    ( r2_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_2855,plain,
    ( r2_lattice3(sK2,X0_45,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X0_45,X1_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_487])).

cnf(c_3550,plain,
    ( r2_lattice3(sK2,X0_45,sK5)
    | m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2855])).

cnf(c_3551,plain,
    ( r2_lattice3(sK2,X0_45,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,X0_45,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3550])).

cnf(c_3553,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3551])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_552,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_20])).

cnf(c_553,plain,
    ( r1_lattice3(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_2851,plain,
    ( r1_lattice3(sK2,X0_45,X1_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK2))
    | m1_subset_1(sK0(sK2,X0_45,X1_45),u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_553])).

cnf(c_3545,plain,
    ( r1_lattice3(sK2,X0_45,sK5)
    | m1_subset_1(sK0(sK2,X0_45,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2851])).

cnf(c_3546,plain,
    ( r1_lattice3(sK2,X0_45,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,X0_45,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3545])).

cnf(c_3548,plain,
    ( r1_lattice3(sK2,sK4,sK5) = iProver_top
    | m1_subset_1(sK0(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3546])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2862,negated_conjecture,
    ( r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_3311,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2862])).

cnf(c_15,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2861,negated_conjecture,
    ( sK5 = sK6 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_3341,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3311,c_2861])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2860,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_3312,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2860])).

cnf(c_3334,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3312,c_2861])).

cnf(c_13,negated_conjecture,
    ( r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2863,negated_conjecture,
    ( r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_3310,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2863])).

cnf(c_3351,plain,
    ( r2_lattice3(sK3,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3310,c_2861])).

cnf(c_12,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2864,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK3,sK4,sK6) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_3309,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2864])).

cnf(c_3346,plain,
    ( r2_lattice3(sK2,sK4,sK5) != iProver_top
    | r1_lattice3(sK3,sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3309,c_2861])).

cnf(c_11,negated_conjecture,
    ( ~ r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2337,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | sK5 != X0
    | sK4 != X1
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_487])).

cnf(c_2338,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2337])).

cnf(c_2339,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(sK1(sK2,sK4,sK5),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2338])).

cnf(c_2323,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK1(sK2,X0,X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK5 != X1
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_502])).

cnf(c_2324,plain,
    ( ~ r1_lattice3(sK2,sK4,sK5)
    | r2_hidden(sK1(sK2,sK4,sK5),sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2323])).

cnf(c_2325,plain,
    ( r1_lattice3(sK2,sK4,sK5) != iProver_top
    | r2_hidden(sK1(sK2,sK4,sK5),sK4) = iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2324])).

cnf(c_2309,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,X0,X1),X1)
    | ~ r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | sK5 != X1
    | sK4 != X0
    | sK2 != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_517])).

cnf(c_2310,plain,
    ( ~ r1_orders_2(sK2,sK1(sK2,sK4,sK5),sK5)
    | ~ r1_lattice3(sK2,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_2309])).

cnf(c_2311,plain,
    ( r1_orders_2(sK2,sK1(sK2,sK4,sK5),sK5) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_23,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6064,c_5653,c_5182,c_4763,c_4388,c_4247,c_3576,c_3571,c_3566,c_3561,c_3553,c_3548,c_3341,c_3334,c_3351,c_3346,c_2339,c_2325,c_2311,c_24,c_23])).


%------------------------------------------------------------------------------
