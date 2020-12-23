%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:19:22 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  154 (1905 expanded)
%              Number of clauses        :  102 ( 510 expanded)
%              Number of leaves         :   12 ( 615 expanded)
%              Depth                    :   27
%              Number of atoms          :  644 (15239 expanded)
%              Number of equality atoms :  222 (3333 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( l1_orders_2(X1)
         => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
           => ! [X2,X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( X3 = X4
                     => ( ( r1_lattice3(X0,X2,X3)
                         => r1_lattice3(X1,X2,X4) )
                        & ( r2_lattice3(X0,X2,X3)
                         => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( l1_orders_2(X1)
           => ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
             => ! [X2,X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( X3 = X4
                       => ( ( r1_lattice3(X0,X2,X3)
                           => r1_lattice3(X1,X2,X4) )
                          & ( r2_lattice3(X0,X2,X3)
                           => r2_lattice3(X1,X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ( ~ r1_lattice3(X1,X2,X4)
              & r1_lattice3(X0,X2,X3) )
            | ( ~ r2_lattice3(X1,X2,X4)
              & r2_lattice3(X0,X2,X3) ) )
          & X3 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ( ( ~ r1_lattice3(X1,X2,sK6)
            & r1_lattice3(X0,X2,X3) )
          | ( ~ r2_lattice3(X1,X2,sK6)
            & r2_lattice3(X0,X2,X3) ) )
        & sK6 = X3
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( ? [X4] :
              ( ( ( ~ r1_lattice3(X1,X2,X4)
                  & r1_lattice3(X0,X2,X3) )
                | ( ~ r2_lattice3(X1,X2,X4)
                  & r2_lattice3(X0,X2,X3) ) )
              & X3 = X4
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ( ( ~ r1_lattice3(X1,sK4,X4)
                & r1_lattice3(X0,sK4,sK5) )
              | ( ~ r2_lattice3(X1,sK4,X4)
                & r2_lattice3(X0,sK4,sK5) ) )
            & sK5 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(X0,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(X0,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
     => ( ? [X3,X2] :
            ( ? [X4] :
                ( ( ( ~ r1_lattice3(sK3,X2,X4)
                    & r1_lattice3(X0,X2,X3) )
                  | ( ~ r2_lattice3(sK3,X2,X4)
                    & r2_lattice3(X0,X2,X3) ) )
                & X3 = X4
                & m1_subset_1(X4,u1_struct_0(sK3)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0))
        & l1_orders_2(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ( ( ~ r1_lattice3(X1,X2,X4)
                        & r1_lattice3(X0,X2,X3) )
                      | ( ~ r2_lattice3(X1,X2,X4)
                        & r2_lattice3(X0,X2,X3) ) )
                    & X3 = X4
                    & m1_subset_1(X4,u1_struct_0(X1)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
            & l1_orders_2(X1) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ( ( ~ r1_lattice3(X1,X2,X4)
                      & r1_lattice3(sK2,X2,X3) )
                    | ( ~ r2_lattice3(X1,X2,X4)
                      & r2_lattice3(sK2,X2,X3) ) )
                  & X3 = X4
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          & l1_orders_2(X1) )
      & l1_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ( ( ~ r1_lattice3(sK3,sK4,sK6)
        & r1_lattice3(sK2,sK4,sK5) )
      | ( ~ r2_lattice3(sK3,sK4,sK6)
        & r2_lattice3(sK2,sK4,sK5) ) )
    & sK5 = sK6
    & m1_subset_1(sK6,u1_struct_0(sK3))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    & l1_orders_2(sK3)
    & l1_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f16,f29,f28,f27,f26])).

fof(f50,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
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

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f13])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | ~ r2_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
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

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f19,plain,(
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
    inference(rectify,[],[f18])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,
    ( ~ r1_lattice3(sK3,sK4,sK6)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,
    ( ~ r1_lattice3(sK3,sK4,sK6)
    | ~ r2_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_16,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5885,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5904,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5885,c_17])).

cnf(c_10,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1391,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK1(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_1392,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK1(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1391])).

cnf(c_5880,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_11,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1376,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_21])).

cnf(c_1377,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1376])).

cnf(c_5881,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1377])).

cnf(c_12,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1530,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_1531,plain,
    ( ~ r2_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_1530])).

cnf(c_5871,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1531])).

cnf(c_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_5889,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6319,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_5889])).

cnf(c_2,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_60,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6320,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_5889])).

cnf(c_6337,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6320])).

cnf(c_6424,plain,
    ( u1_struct_0(sK2) = X0
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6319,c_22,c_60,c_6337])).

cnf(c_6425,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_6424])).

cnf(c_6430,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(equality_resolution,[status(thm)],[c_6425])).

cnf(c_7798,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5871,c_6430])).

cnf(c_7808,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK3,X2,X3) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X2,X3),X1) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X2,X3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5881,c_7798])).

cnf(c_10002,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r2_lattice3(sK3,X0,X2) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X2),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5880,c_7808])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_5884,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_1669,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_22])).

cnf(c_1670,plain,
    ( ~ r1_orders_2(sK2,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
    inference(unflattening,[status(thm)],[c_1669])).

cnf(c_5862,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1670])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_5890,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6402,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_5890])).

cnf(c_6403,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_5890])).

cnf(c_6420,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6403])).

cnf(c_6536,plain,
    ( u1_orders_2(sK2) = X1
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6402,c_22,c_60,c_6420])).

cnf(c_6537,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1 ),
    inference(renaming,[status(thm)],[c_6536])).

cnf(c_6542,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK2) ),
    inference(equality_resolution,[status(thm)],[c_6537])).

cnf(c_6734,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5862,c_6430,c_6542])).

cnf(c_0,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_1512,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_1513,plain,
    ( r1_orders_2(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
    inference(unflattening,[status(thm)],[c_1512])).

cnf(c_5872,plain,
    ( r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_7202,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6734,c_5872])).

cnf(c_8468,plain,
    ( r1_orders_2(sK2,X0,sK6) != iProver_top
    | r1_orders_2(sK3,X0,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5884,c_7202])).

cnf(c_8640,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5881,c_8468])).

cnf(c_10014,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10002,c_8640])).

cnf(c_26,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_10570,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK2,X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10014,c_26])).

cnf(c_10571,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_10570])).

cnf(c_9,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1406,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_1407,plain,
    ( r2_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,sK1(sK3,X0,X1),X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1406])).

cnf(c_5879,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1407])).

cnf(c_10580,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10571,c_5879])).

cnf(c_10603,plain,
    ( r2_lattice3(sK3,X0,sK6) = iProver_top
    | r2_lattice3(sK2,X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10580,c_26])).

cnf(c_10604,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,sK6) = iProver_top ),
    inference(renaming,[status(thm)],[c_10603])).

cnf(c_10611,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5904,c_10604])).

cnf(c_15,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5886,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5909,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5886,c_17])).

cnf(c_10653,plain,
    ( r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10611,c_5909])).

cnf(c_6,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1457,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | r2_hidden(sK0(X0,X1,X2),X1)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_21])).

cnf(c_1458,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | r2_hidden(sK0(sK3,X0,X1),X0) ),
    inference(unflattening,[status(thm)],[c_1457])).

cnf(c_5876,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1458])).

cnf(c_7,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1442,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_1443,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(sK3))
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1442])).

cnf(c_5877,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1443])).

cnf(c_8,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1596,plain,
    ( ~ r1_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ r2_hidden(X3,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_1597,plain,
    ( ~ r1_lattice3(sK2,X0,X1)
    | r1_orders_2(sK2,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,u1_struct_0(sK2))
    | ~ r2_hidden(X2,X0) ),
    inference(unflattening,[status(thm)],[c_1596])).

cnf(c_5867,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1597])).

cnf(c_7532,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5867,c_6430])).

cnf(c_7543,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X2,X3) = iProver_top
    | r1_orders_2(sK2,X1,sK0(sK3,X2,X3)) = iProver_top
    | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X2,X3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5877,c_7532])).

cnf(c_9280,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X2) = iProver_top
    | r1_orders_2(sK2,X1,sK0(sK3,X0,X2)) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5876,c_7543])).

cnf(c_8470,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,X2,sK0(sK3,X0,X1)) != iProver_top
    | r1_orders_2(sK3,X2,sK0(sK3,X0,X1)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5877,c_7202])).

cnf(c_9837,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X2) = iProver_top
    | r1_orders_2(sK3,X1,sK0(sK3,X0,X2)) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9280,c_8470])).

cnf(c_5,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1472,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_21])).

cnf(c_1473,plain,
    ( r1_lattice3(sK3,X0,X1)
    | ~ r1_orders_2(sK3,X1,sK0(sK3,X0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
    inference(unflattening,[status(thm)],[c_1472])).

cnf(c_5875,plain,
    ( r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,X1,sK0(sK3,X0,X1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1473])).

cnf(c_11267,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9837,c_5875])).

cnf(c_11430,plain,
    ( r1_lattice3(sK2,X0,sK6) != iProver_top
    | r1_lattice3(sK3,X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_5884,c_11267])).

cnf(c_11625,plain,
    ( r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_10653,c_11430])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_5887,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5914,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5887,c_17])).

cnf(c_11629,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_11625,c_5914])).

cnf(c_11746,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_11629,c_10604])).

cnf(c_13,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_30,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11746,c_11625,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:08:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.14/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.99  
% 3.14/0.99  ------  iProver source info
% 3.14/0.99  
% 3.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.99  git: non_committed_changes: false
% 3.14/0.99  git: last_make_outside_of_git: false
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     num_symb
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       true
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  ------ Parsing...
% 3.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.99  ------ Proving...
% 3.14/0.99  ------ Problem Properties 
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  clauses                                 32
% 3.14/0.99  conjectures                             8
% 3.14/0.99  EPR                                     5
% 3.14/0.99  Horn                                    23
% 3.14/0.99  unary                                   6
% 3.14/0.99  binary                                  4
% 3.14/0.99  lits                                    92
% 3.14/0.99  lits eq                                 6
% 3.14/0.99  fd_pure                                 0
% 3.14/0.99  fd_pseudo                               0
% 3.14/0.99  fd_cond                                 0
% 3.14/0.99  fd_pseudo_cond                          2
% 3.14/0.99  AC symbols                              0
% 3.14/0.99  
% 3.14/0.99  ------ Schedule dynamic 5 is on 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  Current options:
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     none
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       false
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ Proving...
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS status Theorem for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  fof(f6,conjecture,(
% 3.14/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4)) & (r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)))))))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f7,negated_conjecture,(
% 3.14/0.99    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (l1_orders_2(X1) => (g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) => ! [X2,X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (X3 = X4 => ((r1_lattice3(X0,X2,X3) => r1_lattice3(X1,X2,X4)) & (r2_lattice3(X0,X2,X3) => r2_lattice3(X1,X2,X4)))))))))),
% 3.14/0.99    inference(negated_conjecture,[],[f6])).
% 3.14/0.99  
% 3.14/0.99  fof(f15,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : ((? [X2,X3] : (? [X4] : ((((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4) & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f7])).
% 3.14/0.99  
% 3.14/0.99  fof(f16,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0))),
% 3.14/0.99    inference(flattening,[],[f15])).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (((~r1_lattice3(X1,X2,sK6) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,sK6) & r2_lattice3(X0,X2,X3))) & sK6 = X3 & m1_subset_1(sK6,u1_struct_0(X1)))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f28,plain,(
% 3.14/0.99    ( ! [X0,X1] : (? [X2,X3] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) => (? [X4] : (((~r1_lattice3(X1,sK4,X4) & r1_lattice3(X0,sK4,sK5)) | (~r2_lattice3(X1,sK4,X4) & r2_lattice3(X0,sK4,sK5))) & sK5 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f27,plain,(
% 3.14/0.99    ( ! [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) => (? [X3,X2] : (? [X4] : (((~r1_lattice3(sK3,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(sK3,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(sK3))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) = g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) & l1_orders_2(sK3))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f26,plain,(
% 3.14/0.99    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(X0,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(X0,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X0))) & g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (((~r1_lattice3(X1,X2,X4) & r1_lattice3(sK2,X2,X3)) | (~r2_lattice3(X1,X2,X4) & r2_lattice3(sK2,X2,X3))) & X3 = X4 & m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(sK2))) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(X1),u1_orders_2(X1)) & l1_orders_2(X1)) & l1_orders_2(sK2))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    (((((~r1_lattice3(sK3,sK4,sK6) & r1_lattice3(sK2,sK4,sK5)) | (~r2_lattice3(sK3,sK4,sK6) & r2_lattice3(sK2,sK4,sK5))) & sK5 = sK6 & m1_subset_1(sK6,u1_struct_0(sK3))) & m1_subset_1(sK5,u1_struct_0(sK2))) & g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) & l1_orders_2(sK3)) & l1_orders_2(sK2)),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f16,f29,f28,f27,f26])).
% 3.14/0.99  
% 3.14/0.99  fof(f50,plain,(
% 3.14/0.99    r1_lattice3(sK2,sK4,sK5) | r2_lattice3(sK2,sK4,sK5)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f49,plain,(
% 3.14/0.99    sK5 = sK6),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f13,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f14,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(flattening,[],[f13])).
% 3.14/0.99  
% 3.14/0.99  fof(f22,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f14])).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(rectify,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f25,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK1(X0,X1,X2),X2) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f23,f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f42,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | r2_hidden(sK1(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f45,plain,(
% 3.14/0.99    l1_orders_2(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f41,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f40,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f44,plain,(
% 3.14/0.99    l1_orders_2(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f46,plain,(
% 3.14/0.99    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2,X3] : (g1_orders_2(X0,X1) = g1_orders_2(X2,X3) => (X1 = X3 & X0 = X2)))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f10,plain,(
% 3.14/0.99    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 3.14/0.99    inference(ennf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f34,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f2,axiom,(
% 3.14/0.99    ! [X0] : (l1_orders_2(X0) => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f9,plain,(
% 3.14/0.99    ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f2])).
% 3.14/0.99  
% 3.14/0.99  fof(f33,plain,(
% 3.14/0.99    ( ! [X0] : (m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f48,plain,(
% 3.14/0.99    m1_subset_1(sK6,u1_struct_0(sK3))),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f8,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f17,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f31,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f35,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (X1 = X3 | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f32,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f43,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r2_lattice3(X0,X1,X2) | ~r1_orders_2(X0,sK1(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f51,plain,(
% 3.14/0.99    r1_lattice3(sK2,sK4,sK5) | ~r2_lattice3(sK3,sK4,sK6)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f4,axiom,(
% 3.14/0.99    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 3.14/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f11,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f4])).
% 3.14/0.99  
% 3.14/0.99  fof(f12,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(flattening,[],[f11])).
% 3.14/0.99  
% 3.14/0.99  fof(f18,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(nnf_transformation,[],[f12])).
% 3.14/0.99  
% 3.14/0.99  fof(f19,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(rectify,[],[f18])).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f21,plain,(
% 3.14/0.99    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK0(X0,X1,X2)) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f37,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f36,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X1] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f39,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (r1_lattice3(X0,X1,X2) | ~r1_orders_2(X0,X2,sK0(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f52,plain,(
% 3.14/0.99    ~r1_lattice3(sK3,sK4,sK6) | r2_lattice3(sK2,sK4,sK5)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f53,plain,(
% 3.14/0.99    ~r1_lattice3(sK3,sK4,sK6) | ~r2_lattice3(sK3,sK4,sK6)),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_16,negated_conjecture,
% 3.14/0.99      ( r2_lattice3(sK2,sK4,sK5) | r1_lattice3(sK2,sK4,sK5) ),
% 3.14/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5885,plain,
% 3.14/0.99      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 3.14/0.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,negated_conjecture,
% 3.14/0.99      ( sK5 = sK6 ),
% 3.14/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5904,plain,
% 3.14/0.99      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 3.14/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_5885,c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,negated_conjecture,
% 3.14/0.99      ( l1_orders_2(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1391,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(sK1(X0,X1,X2),X1)
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1392,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.14/0.99      | r2_hidden(sK1(sK3,X0,X1),X0) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1391]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5880,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(sK1(sK3,X0,X1),X0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_11,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1376,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1377,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.14/0.99      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1376]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5881,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(sK1(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1377]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_12,plain,
% 3.14/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.14/0.99      | r1_orders_2(X0,X3,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(X3,X1)
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_22,negated_conjecture,
% 3.14/0.99      ( l1_orders_2(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1530,plain,
% 3.14/0.99      ( ~ r2_lattice3(X0,X1,X2)
% 3.14/0.99      | r1_orders_2(X0,X3,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(X3,X1)
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1531,plain,
% 3.14/0.99      ( ~ r2_lattice3(sK2,X0,X1)
% 3.14/0.99      | r1_orders_2(sK2,X2,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.14/0.99      | ~ r2_hidden(X2,X0) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1530]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5871,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X2,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1531]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_20,negated_conjecture,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.14/0.99      | X2 = X1
% 3.14/0.99      | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5889,plain,
% 3.14/0.99      ( X0 = X1
% 3.14/0.99      | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
% 3.14/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6319,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_struct_0(sK2) = X0
% 3.14/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_20,c_5889]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2,plain,
% 3.14/0.99      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_60,plain,
% 3.14/0.99      ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.14/0.99      | ~ l1_orders_2(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6320,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_struct_0(sK2) = X0
% 3.14/0.99      | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_20,c_5889]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6337,plain,
% 3.14/0.99      ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.14/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_struct_0(sK2) = X0 ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6320]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6424,plain,
% 3.14/0.99      ( u1_struct_0(sK2) = X0
% 3.14/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_6319,c_22,c_60,c_6337]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6425,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_struct_0(sK2) = X0 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_6424]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6430,plain,
% 3.14/0.99      ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
% 3.14/0.99      inference(equality_resolution,[status(thm)],[c_6425]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7798,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X2,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_5871,c_6430]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7808,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X2,X3) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,sK1(sK3,X2,X3),X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(sK1(sK3,X2,X3),X0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5881,c_7798]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10002,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,X2) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,sK1(sK3,X0,X2),X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5880,c_7808]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_18,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5884,plain,
% 3.14/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1,plain,
% 3.14/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f31]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1669,plain,
% 3.14/0.99      ( ~ r1_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1670,plain,
% 3.14/0.99      ( ~ r1_orders_2(sK2,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.14/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 3.14/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1669]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5862,plain,
% 3.14/0.99      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 3.14/0.99      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1670]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 3.14/0.99      | X2 = X0
% 3.14/0.99      | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5890,plain,
% 3.14/0.99      ( X0 = X1
% 3.14/0.99      | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
% 3.14/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6402,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_orders_2(sK2) = X1
% 3.14/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_20,c_5890]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6403,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_orders_2(sK2) = X1
% 3.14/0.99      | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_20,c_5890]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6420,plain,
% 3.14/0.99      ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
% 3.14/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_orders_2(sK2) = X1 ),
% 3.14/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6403]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6536,plain,
% 3.14/0.99      ( u1_orders_2(sK2) = X1
% 3.14/0.99      | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_6402,c_22,c_60,c_6420]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6537,plain,
% 3.14/0.99      ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
% 3.14/0.99      | u1_orders_2(sK2) = X1 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_6536]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6542,plain,
% 3.14/0.99      ( u1_orders_2(sK3) = u1_orders_2(sK2) ),
% 3.14/0.99      inference(equality_resolution,[status(thm)],[c_6537]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6734,plain,
% 3.14/0.99      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) = iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_5862,c_6430,c_6542]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_0,plain,
% 3.14/0.99      ( r1_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f32]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1512,plain,
% 3.14/0.99      ( r1_orders_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1513,plain,
% 3.14/0.99      ( r1_orders_2(sK3,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.14/0.99      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 3.14/0.99      | ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1512]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5872,plain,
% 3.14/0.99      ( r1_orders_2(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK3)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7202,plain,
% 3.14/0.99      ( r1_orders_2(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_orders_2(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_6734,c_5872]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8468,plain,
% 3.14/0.99      ( r1_orders_2(sK2,X0,sK6) != iProver_top
% 3.14/0.99      | r1_orders_2(sK3,X0,sK6) = iProver_top
% 3.14/0.99      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5884,c_7202]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8640,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) != iProver_top
% 3.14/0.99      | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5881,c_8468]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10014,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,sK6) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_10002,c_8640]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_26,plain,
% 3.14/0.99      ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10570,plain,
% 3.14/0.99      ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r2_lattice3(sK2,X0,sK6) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_10014,c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10571,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,sK6) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_10570]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1406,plain,
% 3.14/0.99      ( r2_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1407,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1)
% 3.14/0.99      | ~ r1_orders_2(sK3,sK1(sK3,X0,X1),X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1406]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5879,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r1_orders_2(sK3,sK1(sK3,X0,X1),X1) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1407]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10580,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,sK6) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,sK6) = iProver_top
% 3.14/0.99      | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_10571,c_5879]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10603,plain,
% 3.14/0.99      ( r2_lattice3(sK3,X0,sK6) = iProver_top
% 3.14/0.99      | r2_lattice3(sK2,X0,sK6) != iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_10580,c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10604,plain,
% 3.14/0.99      ( r2_lattice3(sK2,X0,sK6) != iProver_top
% 3.14/0.99      | r2_lattice3(sK3,X0,sK6) = iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_10603]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10611,plain,
% 3.14/0.99      ( r2_lattice3(sK3,sK4,sK6) = iProver_top
% 3.14/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5904,c_10604]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_15,negated_conjecture,
% 3.14/0.99      ( ~ r2_lattice3(sK3,sK4,sK6) | r1_lattice3(sK2,sK4,sK5) ),
% 3.14/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5886,plain,
% 3.14/0.99      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 3.14/0.99      | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5909,plain,
% 3.14/0.99      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 3.14/0.99      | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_5886,c_17]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_10653,plain,
% 3.14/0.99      ( r1_lattice3(sK2,sK4,sK6) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_10611,c_5909]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6,plain,
% 3.14/0.99      ( r1_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1457,plain,
% 3.14/0.99      ( r1_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | r2_hidden(sK0(X0,X1,X2),X1)
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1458,plain,
% 3.14/0.99      ( r1_lattice3(sK3,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.14/0.99      | r2_hidden(sK0(sK3,X0,X1),X0) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1457]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5876,plain,
% 3.14/0.99      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(sK0(sK3,X0,X1),X0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1458]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7,plain,
% 3.14/0.99      ( r1_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1442,plain,
% 3.14/0.99      ( r1_lattice3(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
% 3.14/0.99      | sK3 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1443,plain,
% 3.14/0.99      ( r1_lattice3(sK3,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK3))
% 3.14/0.99      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1442]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5877,plain,
% 3.14/0.99      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(sK0(sK3,X0,X1),u1_struct_0(sK3)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1443]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8,plain,
% 3.14/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 3.14/0.99      | r1_orders_2(X0,X2,X3)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(X3,X1)
% 3.14/0.99      | ~ l1_orders_2(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1596,plain,
% 3.14/0.99      ( ~ r1_lattice3(X0,X1,X2)
% 3.14/0.99      | r1_orders_2(X0,X2,X3)
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/0.99      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 3.14/0.99      | ~ r2_hidden(X3,X1)
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1597,plain,
% 3.14/0.99      ( ~ r1_lattice3(sK2,X0,X1)
% 3.14/0.99      | r1_orders_2(sK2,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 3.14/0.99      | ~ m1_subset_1(X2,u1_struct_0(sK2))
% 3.14/0.99      | ~ r2_hidden(X2,X0) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_1596]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5867,plain,
% 3.14/0.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X1,X2) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
% 3.14/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1597]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7532,plain,
% 3.14/0.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X1,X2) = iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(X2,X0) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_5867,c_6430]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7543,plain,
% 3.14/0.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_lattice3(sK3,X2,X3) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X1,sK0(sK3,X2,X3)) = iProver_top
% 3.14/0.99      | m1_subset_1(X3,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | r2_hidden(sK0(sK3,X2,X3),X0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5877,c_7532]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_9280,plain,
% 3.14/0.99      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/0.99      | r1_lattice3(sK3,X0,X2) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X1,sK0(sK3,X0,X2)) = iProver_top
% 3.14/0.99      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_5876,c_7543]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_8470,plain,
% 3.14/0.99      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.14/0.99      | r1_orders_2(sK2,X2,sK0(sK3,X0,X1)) != iProver_top
% 3.14/0.99      | r1_orders_2(sK3,X2,sK0(sK3,X0,X1)) = iProver_top
% 3.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_5877,c_7202]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_9837,plain,
% 3.14/1.00      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/1.00      | r1_lattice3(sK3,X0,X2) = iProver_top
% 3.14/1.00      | r1_orders_2(sK3,X1,sK0(sK3,X0,X2)) = iProver_top
% 3.14/1.00      | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
% 3.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_9280,c_8470]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5,plain,
% 3.14/1.00      ( r1_lattice3(X0,X1,X2)
% 3.14/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 3.14/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/1.00      | ~ l1_orders_2(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1472,plain,
% 3.14/1.00      ( r1_lattice3(X0,X1,X2)
% 3.14/1.00      | ~ r1_orders_2(X0,X2,sK0(X0,X1,X2))
% 3.14/1.00      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 3.14/1.00      | sK3 != X0 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_5,c_21]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1473,plain,
% 3.14/1.00      ( r1_lattice3(sK3,X0,X1)
% 3.14/1.00      | ~ r1_orders_2(sK3,X1,sK0(sK3,X0,X1))
% 3.14/1.00      | ~ m1_subset_1(X1,u1_struct_0(sK3)) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_1472]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5875,plain,
% 3.14/1.00      ( r1_lattice3(sK3,X0,X1) = iProver_top
% 3.14/1.00      | r1_orders_2(sK3,X1,sK0(sK3,X0,X1)) != iProver_top
% 3.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_1473]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_11267,plain,
% 3.14/1.00      ( r1_lattice3(sK2,X0,X1) != iProver_top
% 3.14/1.00      | r1_lattice3(sK3,X0,X1) = iProver_top
% 3.14/1.00      | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_9837,c_5875]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_11430,plain,
% 3.14/1.00      ( r1_lattice3(sK2,X0,sK6) != iProver_top
% 3.14/1.00      | r1_lattice3(sK3,X0,sK6) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_5884,c_11267]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_11625,plain,
% 3.14/1.00      ( r1_lattice3(sK3,sK4,sK6) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_10653,c_11430]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_14,negated_conjecture,
% 3.14/1.00      ( r2_lattice3(sK2,sK4,sK5) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 3.14/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5887,plain,
% 3.14/1.00      ( r2_lattice3(sK2,sK4,sK5) = iProver_top
% 3.14/1.00      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_5914,plain,
% 3.14/1.00      ( r2_lattice3(sK2,sK4,sK6) = iProver_top
% 3.14/1.00      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 3.14/1.00      inference(light_normalisation,[status(thm)],[c_5887,c_17]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_11629,plain,
% 3.14/1.00      ( r2_lattice3(sK2,sK4,sK6) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_11625,c_5914]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_11746,plain,
% 3.14/1.00      ( r2_lattice3(sK3,sK4,sK6) = iProver_top ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_11629,c_10604]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_13,negated_conjecture,
% 3.14/1.00      ( ~ r2_lattice3(sK3,sK4,sK6) | ~ r1_lattice3(sK3,sK4,sK6) ),
% 3.14/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_30,plain,
% 3.14/1.00      ( r2_lattice3(sK3,sK4,sK6) != iProver_top
% 3.14/1.00      | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(contradiction,plain,
% 3.14/1.00      ( $false ),
% 3.14/1.00      inference(minisat,[status(thm)],[c_11746,c_11625,c_30]) ).
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  ------                               Statistics
% 3.14/1.00  
% 3.14/1.00  ------ General
% 3.14/1.00  
% 3.14/1.00  abstr_ref_over_cycles:                  0
% 3.14/1.00  abstr_ref_under_cycles:                 0
% 3.14/1.00  gc_basic_clause_elim:                   0
% 3.14/1.00  forced_gc_time:                         0
% 3.14/1.00  parsing_time:                           0.013
% 3.14/1.00  unif_index_cands_time:                  0.
% 3.14/1.00  unif_index_add_time:                    0.
% 3.14/1.00  orderings_time:                         0.
% 3.14/1.00  out_proof_time:                         0.029
% 3.14/1.00  total_time:                             0.299
% 3.14/1.00  num_of_symbols:                         50
% 3.14/1.00  num_of_terms:                           7070
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing
% 3.14/1.00  
% 3.14/1.00  num_of_splits:                          0
% 3.14/1.00  num_of_split_atoms:                     0
% 3.14/1.00  num_of_reused_defs:                     0
% 3.14/1.00  num_eq_ax_congr_red:                    15
% 3.14/1.00  num_of_sem_filtered_clauses:            1
% 3.14/1.00  num_of_subtypes:                        0
% 3.14/1.00  monotx_restored_types:                  0
% 3.14/1.00  sat_num_of_epr_types:                   0
% 3.14/1.00  sat_num_of_non_cyclic_types:            0
% 3.14/1.00  sat_guarded_non_collapsed_types:        0
% 3.14/1.00  num_pure_diseq_elim:                    0
% 3.14/1.00  simp_replaced_by:                       0
% 3.14/1.00  res_preprocessed:                       116
% 3.14/1.00  prep_upred:                             0
% 3.14/1.00  prep_unflattend:                        320
% 3.14/1.00  smt_new_axioms:                         0
% 3.14/1.00  pred_elim_cands:                        6
% 3.14/1.00  pred_elim:                              1
% 3.14/1.00  pred_elim_cl:                           -9
% 3.14/1.00  pred_elim_cycles:                       9
% 3.14/1.00  merged_defs:                            0
% 3.14/1.00  merged_defs_ncl:                        0
% 3.14/1.00  bin_hyper_res:                          0
% 3.14/1.00  prep_cycles:                            3
% 3.14/1.00  pred_elim_time:                         0.086
% 3.14/1.00  splitting_time:                         0.
% 3.14/1.00  sem_filter_time:                        0.
% 3.14/1.00  monotx_time:                            0.
% 3.14/1.00  subtype_inf_time:                       0.
% 3.14/1.00  
% 3.14/1.00  ------ Problem properties
% 3.14/1.00  
% 3.14/1.00  clauses:                                32
% 3.14/1.00  conjectures:                            8
% 3.14/1.00  epr:                                    5
% 3.14/1.00  horn:                                   23
% 3.14/1.00  ground:                                 10
% 3.14/1.00  unary:                                  6
% 3.14/1.00  binary:                                 4
% 3.14/1.00  lits:                                   92
% 3.14/1.00  lits_eq:                                6
% 3.14/1.00  fd_pure:                                0
% 3.14/1.00  fd_pseudo:                              0
% 3.14/1.00  fd_cond:                                0
% 3.14/1.00  fd_pseudo_cond:                         2
% 3.14/1.00  ac_symbols:                             0
% 3.14/1.00  
% 3.14/1.00  ------ Propositional Solver
% 3.14/1.00  
% 3.14/1.00  prop_solver_calls:                      25
% 3.14/1.00  prop_fast_solver_calls:                 2397
% 3.14/1.00  smt_solver_calls:                       0
% 3.14/1.00  smt_fast_solver_calls:                  0
% 3.14/1.00  prop_num_of_clauses:                    3067
% 3.14/1.00  prop_preprocess_simplified:             6981
% 3.14/1.00  prop_fo_subsumed:                       92
% 3.14/1.00  prop_solver_time:                       0.
% 3.14/1.00  smt_solver_time:                        0.
% 3.14/1.00  smt_fast_solver_time:                   0.
% 3.14/1.00  prop_fast_solver_time:                  0.
% 3.14/1.00  prop_unsat_core_time:                   0.
% 3.14/1.00  
% 3.14/1.00  ------ QBF
% 3.14/1.00  
% 3.14/1.00  qbf_q_res:                              0
% 3.14/1.00  qbf_num_tautologies:                    0
% 3.14/1.00  qbf_prep_cycles:                        0
% 3.14/1.00  
% 3.14/1.00  ------ BMC1
% 3.14/1.00  
% 3.14/1.00  bmc1_current_bound:                     -1
% 3.14/1.00  bmc1_last_solved_bound:                 -1
% 3.14/1.00  bmc1_unsat_core_size:                   -1
% 3.14/1.00  bmc1_unsat_core_parents_size:           -1
% 3.14/1.00  bmc1_merge_next_fun:                    0
% 3.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation
% 3.14/1.00  
% 3.14/1.00  inst_num_of_clauses:                    693
% 3.14/1.00  inst_num_in_passive:                    43
% 3.14/1.00  inst_num_in_active:                     495
% 3.14/1.00  inst_num_in_unprocessed:                157
% 3.14/1.00  inst_num_of_loops:                      550
% 3.14/1.00  inst_num_of_learning_restarts:          0
% 3.14/1.00  inst_num_moves_active_passive:          51
% 3.14/1.00  inst_lit_activity:                      0
% 3.14/1.00  inst_lit_activity_moves:                0
% 3.14/1.00  inst_num_tautologies:                   0
% 3.14/1.00  inst_num_prop_implied:                  0
% 3.14/1.00  inst_num_existing_simplified:           0
% 3.14/1.00  inst_num_eq_res_simplified:             0
% 3.14/1.00  inst_num_child_elim:                    0
% 3.14/1.00  inst_num_of_dismatching_blockings:      379
% 3.14/1.00  inst_num_of_non_proper_insts:           1194
% 3.14/1.00  inst_num_of_duplicates:                 0
% 3.14/1.00  inst_inst_num_from_inst_to_res:         0
% 3.14/1.00  inst_dismatching_checking_time:         0.
% 3.14/1.00  
% 3.14/1.00  ------ Resolution
% 3.14/1.00  
% 3.14/1.00  res_num_of_clauses:                     0
% 3.14/1.00  res_num_in_passive:                     0
% 3.14/1.00  res_num_in_active:                      0
% 3.14/1.00  res_num_of_loops:                       119
% 3.14/1.00  res_forward_subset_subsumed:            152
% 3.14/1.00  res_backward_subset_subsumed:           4
% 3.14/1.00  res_forward_subsumed:                   8
% 3.14/1.00  res_backward_subsumed:                  0
% 3.14/1.00  res_forward_subsumption_resolution:     15
% 3.14/1.00  res_backward_subsumption_resolution:    0
% 3.14/1.00  res_clause_to_clause_subsumption:       674
% 3.14/1.00  res_orphan_elimination:                 0
% 3.14/1.00  res_tautology_del:                      102
% 3.14/1.00  res_num_eq_res_simplified:              0
% 3.14/1.00  res_num_sel_changes:                    0
% 3.14/1.00  res_moves_from_active_to_pass:          0
% 3.14/1.00  
% 3.14/1.00  ------ Superposition
% 3.14/1.00  
% 3.14/1.00  sup_time_total:                         0.
% 3.14/1.00  sup_time_generating:                    0.
% 3.14/1.00  sup_time_sim_full:                      0.
% 3.14/1.00  sup_time_sim_immed:                     0.
% 3.14/1.00  
% 3.14/1.00  sup_num_of_clauses:                     132
% 3.14/1.00  sup_num_in_active:                      100
% 3.14/1.00  sup_num_in_passive:                     32
% 3.14/1.00  sup_num_of_loops:                       108
% 3.14/1.00  sup_fw_superposition:                   83
% 3.14/1.00  sup_bw_superposition:                   34
% 3.14/1.00  sup_immediate_simplified:               3
% 3.14/1.00  sup_given_eliminated:                   2
% 3.14/1.00  comparisons_done:                       0
% 3.14/1.00  comparisons_avoided:                    0
% 3.14/1.00  
% 3.14/1.00  ------ Simplifications
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  sim_fw_subset_subsumed:                 2
% 3.14/1.00  sim_bw_subset_subsumed:                 5
% 3.14/1.00  sim_fw_subsumed:                        1
% 3.14/1.00  sim_bw_subsumed:                        0
% 3.14/1.00  sim_fw_subsumption_res:                 3
% 3.14/1.00  sim_bw_subsumption_res:                 0
% 3.14/1.00  sim_tautology_del:                      3
% 3.14/1.00  sim_eq_tautology_del:                   7
% 3.14/1.00  sim_eq_res_simp:                        0
% 3.14/1.00  sim_fw_demodulated:                     0
% 3.14/1.00  sim_bw_demodulated:                     6
% 3.14/1.00  sim_light_normalised:                   15
% 3.14/1.00  sim_joinable_taut:                      0
% 3.14/1.00  sim_joinable_simp:                      0
% 3.14/1.00  sim_ac_normalised:                      0
% 3.14/1.00  sim_smt_subsumption:                    0
% 3.14/1.00  
%------------------------------------------------------------------------------
