%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1582+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:57 EST 2020

% Result     : Theorem 11.52s
% Output     : CNFRefutation 11.52s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 420 expanded)
%              Number of clauses        :   71 ( 104 expanded)
%              Number of leaves         :   20 ( 168 expanded)
%              Depth                    :   20
%              Number of atoms          :  529 (3965 expanded)
%              Number of equality atoms :  133 ( 833 expanded)
%              Maximal formula depth    :   18 (   5 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r2_hidden(X4,u1_struct_0(X1))
                              & r1_orders_2(X0,X2,X3)
                              & X3 = X5
                              & X2 = X4 )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_yellow_0(X1,X0)
              & v4_yellow_0(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X1))
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ( ( r2_hidden(X4,u1_struct_0(X1))
                                & r1_orders_2(X0,X2,X3)
                                & X3 = X5
                                & X2 = X4 )
                             => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(X0,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(X0,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ? [X5] :
          ( ~ r1_orders_2(X1,X4,X5)
          & r2_hidden(X4,u1_struct_0(X1))
          & r1_orders_2(X0,X2,X3)
          & X3 = X5
          & X2 = X4
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,X4,sK6)
        & r2_hidden(X4,u1_struct_0(X1))
        & r1_orders_2(X0,X2,X3)
        & sK6 = X3
        & X2 = X4
        & m1_subset_1(sK6,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r1_orders_2(X1,X4,X5)
              & r2_hidden(X4,u1_struct_0(X1))
              & r1_orders_2(X0,X2,X3)
              & X3 = X5
              & X2 = X4
              & m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ? [X5] :
            ( ~ r1_orders_2(X1,sK5,X5)
            & r2_hidden(sK5,u1_struct_0(X1))
            & r1_orders_2(X0,X2,X3)
            & X3 = X5
            & sK5 = X2
            & m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK5,u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r1_orders_2(X1,X4,X5)
                  & r2_hidden(X4,u1_struct_0(X1))
                  & r1_orders_2(X0,X2,X3)
                  & X3 = X5
                  & X2 = X4
                  & m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r1_orders_2(X1,X4,X5)
                & r2_hidden(X4,u1_struct_0(X1))
                & r1_orders_2(X0,X2,sK4)
                & sK4 = X5
                & X2 = X4
                & m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ~ r1_orders_2(X1,X4,X5)
                      & r2_hidden(X4,u1_struct_0(X1))
                      & r1_orders_2(X0,X2,X3)
                      & X3 = X5
                      & X2 = X4
                      & m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r1_orders_2(X1,X4,X5)
                    & r2_hidden(X4,u1_struct_0(X1))
                    & r1_orders_2(X0,sK3,X3)
                    & X3 = X5
                    & sK3 = X4
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK3,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(X0,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_yellow_0(X1,X0)
          & v4_yellow_0(X1,X0) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ~ r1_orders_2(sK2,X4,X5)
                        & r2_hidden(X4,u1_struct_0(sK2))
                        & r1_orders_2(X0,X2,X3)
                        & X3 = X5
                        & X2 = X4
                        & m1_subset_1(X5,u1_struct_0(sK2)) )
                    & m1_subset_1(X4,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_yellow_0(sK2,X0)
        & v4_yellow_0(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ~ r1_orders_2(X1,X4,X5)
                            & r2_hidden(X4,u1_struct_0(X1))
                            & r1_orders_2(X0,X2,X3)
                            & X3 = X5
                            & X2 = X4
                            & m1_subset_1(X5,u1_struct_0(X1)) )
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_yellow_0(X1,X0)
            & v4_yellow_0(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ~ r1_orders_2(X1,X4,X5)
                          & r2_hidden(X4,u1_struct_0(X1))
                          & r1_orders_2(sK1,X2,X3)
                          & X3 = X5
                          & X2 = X4
                          & m1_subset_1(X5,u1_struct_0(X1)) )
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(sK1)) )
              & m1_subset_1(X2,u1_struct_0(sK1)) )
          & m1_yellow_0(X1,sK1)
          & v4_yellow_0(X1,sK1) )
      & l1_orders_2(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ~ r1_orders_2(sK2,sK5,sK6)
    & r2_hidden(sK5,u1_struct_0(sK2))
    & r1_orders_2(sK1,sK3,sK4)
    & sK4 = sK6
    & sK3 = sK5
    & m1_subset_1(sK6,u1_struct_0(sK2))
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK1))
    & m1_subset_1(sK3,u1_struct_0(sK1))
    & m1_yellow_0(sK2,sK1)
    & v4_yellow_0(sK2,sK1)
    & l1_orders_2(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5,sK6])],[f25,f40,f39,f38,f37,f36,f35])).

fof(f71,plain,(
    r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f41])).

fof(f62,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f70,plain,(
    sK4 = sK6 ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    sK3 = sK5 ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_yellow_0(X1,X0)
          <=> u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_yellow_0(X1,X0)
              | u1_orders_2(X1) != k1_toler_1(u1_orders_2(X0),u1_struct_0(X1)) )
            & ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
              | ~ v4_yellow_0(X1,X0) ) )
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( u1_orders_2(X1) = k1_toler_1(u1_orders_2(X0),u1_struct_0(X1))
      | ~ v4_yellow_0(X1,X0)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f64,plain,(
    m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f63,plain,(
    v4_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f33])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => k1_toler_1(X0,X1) = k2_wellord1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_toler_1(X0,X1) = k2_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
          | ~ r2_hidden(sK0(X0,X1,X2),X0)
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(sK0(X0,X1,X2),X0) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            | ~ r2_hidden(sK0(X0,X1,X2),X0)
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK0(X0,X1,X2),X1)
              & r2_hidden(sK0(X0,X1,X2),X0) )
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f29,f30])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f72,plain,(
    r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f68,plain,(
    m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f41])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_yellow_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ m1_yellow_0(X1,X0) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f54,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ m1_yellow_0(X1,X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_22,negated_conjecture,
    ( r1_orders_2(sK1,sK3,sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_404,plain,
    ( r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK4 != X1
    | sK3 != X0
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_405,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK1))
    | ~ m1_subset_1(sK4,u1_struct_0(sK1))
    | ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_31,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_407,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_31,c_28,c_27])).

cnf(c_1538,plain,
    ( r2_hidden(k4_tarski(sK3,sK4),u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_23,negated_conjecture,
    ( sK4 = sK6 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( sK3 = sK5 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1552,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1538,c_23,c_24])).

cnf(c_2,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ v4_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) = u1_orders_2(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_29,negated_conjecture,
    ( m1_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_379,plain,
    ( ~ v4_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | k1_toler_1(u1_orders_2(X1),u1_struct_0(X0)) = u1_orders_2(X0)
    | sK1 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_29])).

cnf(c_380,plain,
    ( ~ v4_yellow_0(sK2,sK1)
    | ~ l1_orders_2(sK1)
    | k1_toler_1(u1_orders_2(sK1),u1_struct_0(sK2)) = u1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_379])).

cnf(c_30,negated_conjecture,
    ( v4_yellow_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_382,plain,
    ( k1_toler_1(u1_orders_2(sK1),u1_struct_0(sK2)) = u1_orders_2(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_380,c_31,c_30])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X2,X3)
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1543,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X3) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_13,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_426,plain,
    ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_31])).

cnf(c_427,plain,
    ( m1_subset_1(u1_orders_2(sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_492,plain,
    ( v1_relat_1(X0)
    | u1_orders_2(sK1) != X0
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution_lifted,[status(thm)],[c_0,c_427])).

cnf(c_493,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_492])).

cnf(c_1533,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_493])).

cnf(c_1667,plain,
    ( v1_relat_1(u1_orders_2(sK1))
    | k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_493])).

cnf(c_1668,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) != k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)))
    | v1_relat_1(u1_orders_2(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1667])).

cnf(c_1108,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1808,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) = k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_1108])).

cnf(c_2867,plain,
    ( v1_relat_1(u1_orders_2(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1533,c_1668,c_1808])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1545,plain,
    ( k3_xboole_0(X0,k2_zfmisc_1(X1,X1)) = k2_wellord1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2972,plain,
    ( k3_xboole_0(u1_orders_2(sK1),k2_zfmisc_1(X0,X0)) = k2_wellord1(u1_orders_2(sK1),X0) ),
    inference(superposition,[status(thm)],[c_2867,c_1545])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k2_wellord1(X0,X1) = k1_toler_1(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1544,plain,
    ( k2_wellord1(X0,X1) = k1_toler_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2871,plain,
    ( k2_wellord1(u1_orders_2(sK1),X0) = k1_toler_1(u1_orders_2(sK1),X0) ),
    inference(superposition,[status(thm)],[c_2867,c_1544])).

cnf(c_2973,plain,
    ( k3_xboole_0(u1_orders_2(sK1),k2_zfmisc_1(X0,X0)) = k1_toler_1(u1_orders_2(sK1),X0) ),
    inference(light_normalisation,[status(thm)],[c_2972,c_2871])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,X2)
    | r2_hidden(X0,k3_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1548,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k3_xboole_0(X2,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3151,plain,
    ( r2_hidden(X0,k1_toler_1(u1_orders_2(sK1),X1)) = iProver_top
    | r2_hidden(X0,k2_zfmisc_1(X1,X1)) != iProver_top
    | r2_hidden(X0,u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2973,c_1548])).

cnf(c_4569,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,X1) != iProver_top
    | r2_hidden(k4_tarski(X2,X0),k1_toler_1(u1_orders_2(sK1),X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),u1_orders_2(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_3151])).

cnf(c_46254,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X1,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK1)) != iProver_top
    | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_382,c_4569])).

cnf(c_46584,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK2)) = iProver_top
    | r2_hidden(sK6,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1552,c_46254])).

cnf(c_21,negated_conjecture,
    ( r2_hidden(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1540,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_18,plain,
    ( r2_hidden(X0,X1)
    | ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_516,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK2) != X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_517,plain,
    ( r2_hidden(sK6,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_601,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(sK6,u1_struct_0(sK2))
    | u1_struct_0(sK2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_517])).

cnf(c_602,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK2))
    | r2_hidden(sK6,u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_1531,plain,
    ( r2_hidden(X0,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2823,plain,
    ( r2_hidden(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1540,c_1531])).

cnf(c_10,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( ~ r1_orders_2(sK2,sK5,sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_393,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),u1_orders_2(X2))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | sK6 != X1
    | sK5 != X0
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_394,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK2))
    | ~ m1_subset_1(sK6,u1_struct_0(sK2))
    | ~ m1_subset_1(sK5,u1_struct_0(sK2))
    | ~ l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( r2_hidden(k4_tarski(sK5,sK6),u1_orders_2(sK2)) != iProver_top
    | m1_subset_1(sK6,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,u1_struct_0(sK2)) != iProver_top
    | l1_orders_2(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_12,plain,
    ( ~ m1_yellow_0(X0,X1)
    | ~ l1_orders_2(X1)
    | l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_368,plain,
    ( ~ l1_orders_2(X0)
    | l1_orders_2(X1)
    | sK1 != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_369,plain,
    ( ~ l1_orders_2(sK1)
    | l1_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_370,plain,
    ( l1_orders_2(sK1) != iProver_top
    | l1_orders_2(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_40,plain,
    ( r2_hidden(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_38,plain,
    ( m1_subset_1(sK6,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_46584,c_2823,c_395,c_370,c_40,c_38,c_37,c_32])).


%------------------------------------------------------------------------------
