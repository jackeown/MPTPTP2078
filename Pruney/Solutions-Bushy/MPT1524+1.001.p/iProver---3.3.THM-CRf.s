%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1524+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:46 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  158 (2188 expanded)
%              Number of clauses        :  105 ( 608 expanded)
%              Number of leaves         :   12 ( 700 expanded)
%              Depth                    :   31
%              Number of atoms          :  750 (17596 expanded)
%              Number of equality atoms :  375 (4415 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   20 (   4 average)
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f17,f29,f28,f27,f26])).

fof(f50,plain,
    ( r1_lattice3(sK2,sK4,sK5)
    | r2_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f30])).

fof(f49,plain,(
    sK5 = sK6 ),
    inference(cnf_transformation,[],[f30])).

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

fof(f10,plain,(
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
    inference(flattening,[],[f10])).

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
    inference(nnf_transformation,[],[f11])).

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

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,X2)
      | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f48,plain,(
    m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f46,plain,(
    g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2,X3] :
          ( g1_orders_2(X0,X1) = g1_orders_2(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_orders_2(X0,X1) != g1_orders_2(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f45,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X3
      | g1_orders_2(X0,X1) != g1_orders_2(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f5,axiom,(
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

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r2_orders_2(X1,X4,X5)
                              | ~ r2_orders_2(X0,X2,X3) )
                            & ( r1_orders_2(X1,X4,X5)
                              | ~ r1_orders_2(X0,X2,X3) ) )
                          | X3 != X5
                          | X2 != X4
                          | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
          | ~ l1_orders_2(X1) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X3)
      | X3 != X5
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | X2 != X4
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f57,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_orders_2(X1,X4,X5)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
      | ~ l1_orders_2(X1)
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f38,plain,(
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

fof(f8,plain,(
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
    inference(flattening,[],[f8])).

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
    inference(nnf_transformation,[],[f9])).

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

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,X2)
      | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_orders_2(X0,X2,X4)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
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

cnf(c_2193,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( sK5 = sK6 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2222,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2193,c_17])).

cnf(c_5,plain,
    ( r2_lattice3(X0,X1,X2)
    | r2_hidden(sK1(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2203,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | r2_hidden(sK1(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2202,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2192,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_20,negated_conjecture,
    ( g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK2)) = g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X1
    | g1_orders_2(X2,X3) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2198,plain,
    ( X0 = X1
    | g1_orders_2(X0,X2) != g1_orders_2(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2705,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2198])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_8,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_38,plain,
    ( m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2706,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2198])).

cnf(c_2723,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2706])).

cnf(c_2826,plain,
    ( u1_struct_0(sK2) = X0
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2705,c_22,c_38,c_2723])).

cnf(c_2827,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_struct_0(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_2826])).

cnf(c_2832,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK3) ),
    inference(equality_resolution,[status(thm)],[c_2827])).

cnf(c_7,plain,
    ( ~ r2_lattice3(X0,X1,X2)
    | r1_orders_2(X0,X3,X2)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2201,plain,
    ( r2_lattice3(X0,X1,X2) != iProver_top
    | r1_orders_2(X0,X3,X2) = iProver_top
    | r2_hidden(X3,X1) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3555,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_2201])).

cnf(c_3562,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3555,c_2832])).

cnf(c_23,plain,
    ( l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3854,plain,
    ( m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | r2_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3562,c_23])).

cnf(c_3855,plain,
    ( r2_lattice3(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK2,X2,X1) = iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3854])).

cnf(c_3867,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r1_orders_2(sK2,X1,sK6) = iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_3855])).

cnf(c_4016,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X1,X2),sK6) = iProver_top
    | r2_hidden(sK1(sK3,X1,X2),X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_3867])).

cnf(c_21,negated_conjecture,
    ( l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_24,plain,
    ( l1_orders_2(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4651,plain,
    ( m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK1(sK3,X1,X2),X0) != iProver_top
    | r1_orders_2(sK2,sK1(sK3,X1,X2),sK6) = iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | r2_lattice3(sK2,X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4016,c_24])).

cnf(c_4652,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X1,X2) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X1,X2),sK6) = iProver_top
    | r2_hidden(sK1(sK3,X1,X2),X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4651])).

cnf(c_4662,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2203,c_4652])).

cnf(c_4703,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) = iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r2_lattice3(sK2,X0,sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4662,c_24])).

cnf(c_4704,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4703])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | X2 = X0
    | g1_orders_2(X3,X2) != g1_orders_2(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2199,plain,
    ( X0 = X1
    | g1_orders_2(X2,X0) != g1_orders_2(X3,X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2804,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2199])).

cnf(c_2805,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1
    | m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2199])).

cnf(c_2822,plain,
    ( ~ m1_subset_1(u1_orders_2(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK2))))
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2805])).

cnf(c_2949,plain,
    ( u1_orders_2(sK2) = X1
    | g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2804,c_22,c_38,c_2822])).

cnf(c_2950,plain,
    ( g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) != g1_orders_2(X0,X1)
    | u1_orders_2(sK2) = X1 ),
    inference(renaming,[status(thm)],[c_2949])).

cnf(c_2955,plain,
    ( u1_orders_2(sK3) = u1_orders_2(sK2) ),
    inference(equality_resolution,[status(thm)],[c_2950])).

cnf(c_12,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r1_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0)
    | ~ l1_orders_2(X3)
    | g1_orders_2(u1_struct_0(X3),u1_orders_2(X3)) != g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2197,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(X1),u1_orders_2(X1))
    | r1_orders_2(X1,X2,X3) != iProver_top
    | r1_orders_2(X0,X2,X3) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X1)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X3,u1_struct_0(X1)) != iProver_top
    | l1_orders_2(X1) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3199,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK2),u1_orders_2(sK3))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2955,c_2197])).

cnf(c_3210,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3199,c_2832])).

cnf(c_3517,plain,
    ( l1_orders_2(X0) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | r1_orders_2(X0,X1,X2) = iProver_top
    | g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_23])).

cnf(c_3518,plain,
    ( g1_orders_2(u1_struct_0(X0),u1_orders_2(X0)) != g1_orders_2(u1_struct_0(sK3),u1_orders_2(sK3))
    | r1_orders_2(X0,X1,X2) = iProver_top
    | r1_orders_2(sK2,X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3517])).

cnf(c_3531,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3518])).

cnf(c_5259,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3531,c_24])).

cnf(c_5260,plain,
    ( r1_orders_2(sK2,X0,X1) != iProver_top
    | r1_orders_2(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5259])).

cnf(c_5271,plain,
    ( r1_orders_2(sK2,X0,sK6) != iProver_top
    | r1_orders_2(sK3,X0,sK6) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_5260])).

cnf(c_5419,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2202,c_5271])).

cnf(c_5577,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5419,c_24])).

cnf(c_5578,plain,
    ( r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK2,sK1(sK3,X0,X1),sK6) != iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5577])).

cnf(c_5587,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,X1) = iProver_top
    | r1_orders_2(sK3,sK1(sK3,X0,X1),sK6) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4704,c_5578])).

cnf(c_4,plain,
    ( r2_lattice3(X0,X1,X2)
    | ~ r1_orders_2(X0,sK1(X0,X1,X2),X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2204,plain,
    ( r2_lattice3(X0,X1,X2) = iProver_top
    | r1_orders_2(X0,sK1(X0,X1,X2),X2) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6493,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,sK6) = iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5587,c_2204])).

cnf(c_26,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_6725,plain,
    ( r2_lattice3(sK2,X0,sK6) != iProver_top
    | r2_lattice3(sK3,X0,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6493,c_24,c_26])).

cnf(c_6733,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2222,c_6725])).

cnf(c_15,negated_conjecture,
    ( ~ r2_lattice3(sK3,sK4,sK6)
    | r1_lattice3(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2194,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2227,plain,
    ( r2_lattice3(sK3,sK4,sK6) != iProver_top
    | r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2194,c_17])).

cnf(c_6736,plain,
    ( r1_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6733,c_2227])).

cnf(c_1,plain,
    ( r1_lattice3(X0,X1,X2)
    | r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_2207,plain,
    ( r1_lattice3(X0,X1,X2) = iProver_top
    | r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( r1_lattice3(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_2206,plain,
    ( r1_lattice3(X0,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) = iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r1_lattice3(X0,X3,X1)
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_2205,plain,
    ( r1_orders_2(X0,X1,X2) = iProver_top
    | r1_lattice3(X0,X3,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3717,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2832,c_2205])).

cnf(c_3724,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3717,c_2832])).

cnf(c_4175,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | r1_orders_2(sK2,X0,X1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3724,c_23])).

cnf(c_4176,plain,
    ( r1_orders_2(sK2,X0,X1) = iProver_top
    | r1_lattice3(sK2,X2,X0) != iProver_top
    | r2_hidden(X1,X2) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4175])).

cnf(c_4186,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK2,X3,X0) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | r2_hidden(sK0(sK3,X1,X2),X3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_4176])).

cnf(c_7636,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK0(sK3,X1,X2),X3) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | r1_lattice3(sK2,X3,X0) != iProver_top
    | r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4186,c_24])).

cnf(c_7637,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK2,X3,X0) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | r2_hidden(sK0(sK3,X1,X2),X3) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7636])).

cnf(c_7648,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2207,c_7637])).

cnf(c_8309,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7648,c_24])).

cnf(c_8310,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8309])).

cnf(c_5269,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) != iProver_top
    | r1_orders_2(sK3,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_5260])).

cnf(c_6285,plain,
    ( m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | r1_orders_2(sK3,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5269,c_24])).

cnf(c_6286,plain,
    ( r1_orders_2(sK2,X0,sK0(sK3,X1,X2)) != iProver_top
    | r1_orders_2(sK3,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_6285])).

cnf(c_8321,plain,
    ( r1_orders_2(sK3,X0,sK0(sK3,X1,X2)) = iProver_top
    | r1_lattice3(sK2,X1,X0) != iProver_top
    | r1_lattice3(sK3,X1,X2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8310,c_6286])).

cnf(c_0,plain,
    ( ~ r1_orders_2(X0,X1,sK0(X0,X2,X1))
    | r1_lattice3(X0,X2,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_2208,plain,
    ( r1_orders_2(X0,X1,sK0(X0,X2,X1)) != iProver_top
    | r1_lattice3(X0,X2,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(X0)) != iProver_top
    | l1_orders_2(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8772,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | l1_orders_2(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8321,c_2208])).

cnf(c_8875,plain,
    ( m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | r1_lattice3(sK2,X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8772,c_24])).

cnf(c_8876,plain,
    ( r1_lattice3(sK2,X0,X1) != iProver_top
    | r1_lattice3(sK3,X0,X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8875])).

cnf(c_8886,plain,
    ( r1_lattice3(sK2,X0,sK6) != iProver_top
    | r1_lattice3(sK3,X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2192,c_8876])).

cnf(c_8947,plain,
    ( r1_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_6736,c_8886])).

cnf(c_14,negated_conjecture,
    ( r2_lattice3(sK2,sK4,sK5)
    | ~ r1_lattice3(sK3,sK4,sK6) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2195,plain,
    ( r2_lattice3(sK2,sK4,sK5) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2232,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top
    | r1_lattice3(sK3,sK4,sK6) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2195,c_17])).

cnf(c_9295,plain,
    ( r2_lattice3(sK2,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_8947,c_2232])).

cnf(c_9311,plain,
    ( r2_lattice3(sK3,sK4,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_9295,c_6725])).

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
    inference(minisat,[status(thm)],[c_9311,c_8947,c_30])).


%------------------------------------------------------------------------------
