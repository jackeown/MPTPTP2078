%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1164+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:04 EST 2020

% Result     : Theorem 3.83s
% Output     : CNFRefutation 3.83s
% Verified   : 
% Statistics : Number of formulae       :  170 (1038 expanded)
%              Number of clauses        :  120 ( 340 expanded)
%              Number of leaves         :   18 ( 310 expanded)
%              Depth                    :   21
%              Number of atoms          :  721 (5823 expanded)
%              Number of equality atoms :  235 ( 605 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   21 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_orders_2(X2,X0,X1)
               => r1_tarski(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & m1_orders_2(X2,X0,X1) )
     => ( ~ r1_tarski(sK4,X1)
        & m1_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r1_tarski(X2,sK3)
            & m1_orders_2(X2,X0,sK3) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(X2,X1)
                & m1_orders_2(X2,X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X2,X1)
              & m1_orders_2(X2,sK2,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ~ r1_tarski(sK4,sK3)
    & m1_orders_2(sK4,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f22,f32,f31,f30])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
                        & r2_hidden(sK0(X0,X1,X2),X1)
                        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_orders_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f53,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f49,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f50,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f51,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f56,plain,(
    ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_12,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_13,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_185,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_13])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_185])).

cnf(c_367,plain,
    ( X0 != X1
    | k9_subset_1(X0,X2,X2) = X2
    | k3_xboole_0(X1,X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_236])).

cnf(c_368,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1387,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_14,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1390,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1754,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1390])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_237,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_11,c_185])).

cnf(c_1385,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_2283,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k3_xboole_0(X0,sK3) ),
    inference(superposition,[status(thm)],[c_1754,c_1385])).

cnf(c_2334,plain,
    ( k3_xboole_0(sK3,sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_368,c_2283])).

cnf(c_16,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1388,plain,
    ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_137,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_8])).

cnf(c_138,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_137])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_621,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_138,c_18])).

cnf(c_622,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X1,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_621])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_21,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_626,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X1,X0),u1_struct_0(sK2))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_622,c_22,c_21,c_20,c_19])).

cnf(c_1382,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_235,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_185])).

cnf(c_1386,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_235])).

cnf(c_2710,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2283,c_1386])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1503,plain,
    ( r1_tarski(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1627,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1503])).

cnf(c_1628,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_8634,plain,
    ( m1_subset_1(k3_xboole_0(X0,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2710,c_28,c_1628])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X0) = k3_orders_2(X1,X0,X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_685,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X0) = k3_orders_2(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_686,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X0) = k3_orders_2(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_685])).

cnf(c_690,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X0) = k3_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_686,c_22,c_21,c_20,c_19])).

cnf(c_1379,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1) = k3_orders_2(sK2,X1,X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_690])).

cnf(c_8645,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),k3_xboole_0(X1,sK3)) = k3_orders_2(sK2,k3_xboole_0(X1,sK3),X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8634,c_1379])).

cnf(c_8644,plain,
    ( r1_tarski(k3_xboole_0(X0,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_8634,c_1390])).

cnf(c_8843,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k3_xboole_0(X1,sK3)) = k3_xboole_0(X0,k3_xboole_0(X1,sK3)) ),
    inference(superposition,[status(thm)],[c_8644,c_1385])).

cnf(c_9124,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),k3_xboole_0(X1,sK3)) = k3_orders_2(sK2,k3_xboole_0(X1,sK3),X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8645,c_8843])).

cnf(c_9129,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),k3_xboole_0(X2,sK3)) = k3_orders_2(sK2,k3_xboole_0(X2,sK3),sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1382,c_9124])).

cnf(c_9481,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK3,X0))),k3_xboole_0(X1,sK3)) = k3_orders_2(sK2,k3_xboole_0(X1,sK3),sK0(sK2,sK3,X0))
    | sK3 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_9129])).

cnf(c_10203,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK3,sK4))),k3_xboole_0(X0,sK3)) = k3_orders_2(sK2,k3_xboole_0(X0,sK3),sK0(sK2,sK3,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1388,c_9481])).

cnf(c_1392,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2282,plain,
    ( k9_subset_1(X0,X1,k3_xboole_0(X0,X2)) = k3_xboole_0(X1,k3_xboole_0(X0,X2)) ),
    inference(superposition,[status(thm)],[c_1392,c_1385])).

cnf(c_2734,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) != iProver_top
    | m1_subset_1(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2282,c_1386])).

cnf(c_37,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10978,plain,
    ( m1_subset_1(k3_xboole_0(X2,k3_xboole_0(X0,X1)),k1_zfmisc_1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_37])).

cnf(c_10979,plain,
    ( m1_subset_1(k3_xboole_0(X0,k3_xboole_0(X1,X2)),k1_zfmisc_1(X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_10978])).

cnf(c_11003,plain,
    ( r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,X2)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_10979,c_1390])).

cnf(c_11245,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k3_orders_2(sK2,k3_xboole_0(X0,sK3),sK0(sK2,sK3,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10203,c_11003])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_30,plain,
    ( r1_tarski(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_979,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1002,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1569,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1644,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1647,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_980,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1532,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1684,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_1685,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_1787,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1788,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_986,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != X1
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_1518,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1800,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1518])).

cnf(c_2,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_662,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_18])).

cnf(c_663,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_667,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_22,c_21,c_20,c_19])).

cnf(c_645,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_646,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_645])).

cnf(c_648,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_646,c_22,c_21,c_20,c_19])).

cnf(c_677,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_667,c_648])).

cnf(c_1890,plain,
    ( ~ m1_orders_2(sK4,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_677])).

cnf(c_2010,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_1489,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_2304,plain,
    ( sK3 != X0
    | sK3 = sK4
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1489])).

cnf(c_2307,plain,
    ( sK3 = sK4
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2304])).

cnf(c_2305,plain,
    ( sK3 != sK4
    | sK4 = sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_990,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1423,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_990])).

cnf(c_1484,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_2483,plain,
    ( ~ r1_tarski(sK3,sK3)
    | r1_tarski(sK4,sK3)
    | sK3 != sK3
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_2490,plain,
    ( sK3 != sK3
    | sK4 != sK3
    | r1_tarski(sK3,sK3) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_4802,plain,
    ( r1_tarski(sK3,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_1392])).

cnf(c_988,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_2325,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(sK4,sK2,k1_xboole_0)
    | sK2 != X1
    | sK4 != X0
    | k1_xboole_0 != X2 ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_3079,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | m1_orders_2(sK4,sK2,k1_xboole_0)
    | sK2 != sK2
    | sK4 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_2325])).

cnf(c_5057,plain,
    ( ~ m1_orders_2(sK4,sK2,X0)
    | m1_orders_2(sK4,sK2,k1_xboole_0)
    | sK2 != sK2
    | sK4 != sK4
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_3079])).

cnf(c_10751,plain,
    ( ~ m1_orders_2(sK4,sK2,sK3)
    | m1_orders_2(sK4,sK2,k1_xboole_0)
    | sK2 != sK2
    | sK4 != sK4
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_5057])).

cnf(c_11929,plain,
    ( r1_tarski(k3_orders_2(sK2,k3_xboole_0(X0,sK3),sK0(sK2,sK3,sK4)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11245,c_17,c_16,c_30,c_1002,c_1569,c_1644,c_1647,c_1685,c_1788,c_1800,c_1890,c_2010,c_2307,c_2305,c_2490,c_4802,c_10751])).

cnf(c_11935,plain,
    ( r1_tarski(k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2334,c_11929])).

cnf(c_6021,plain,
    ( ~ r1_tarski(k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)),sK3)
    | r1_tarski(sK4,sK3)
    | sK3 != sK3
    | sK4 != k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1484])).

cnf(c_6027,plain,
    ( sK3 != sK3
    | sK4 != k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4))
    | r1_tarski(k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)),sK3) != iProver_top
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6021])).

cnf(c_4421,plain,
    ( k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)) != sK4
    | sK4 = k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4))
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_4,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_147,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_8])).

cnf(c_148,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_573,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_148,c_18])).

cnf(c_574,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k3_orders_2(sK2,X1,sK0(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_573])).

cnf(c_578,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,X1,sK0(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_22,c_21,c_20,c_19])).

cnf(c_1850,plain,
    ( ~ m1_orders_2(X0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,sK3,sK0(sK2,sK3,X0)) = X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_578])).

cnf(c_3451,plain,
    ( ~ m1_orders_2(sK4,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)) = sK4
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_1383,plain,
    ( k3_orders_2(sK2,X0,sK0(sK2,X0,X1)) = X1
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_1977,plain,
    ( k3_orders_2(sK2,sK3,sK0(sK2,sK3,X0)) = X0
    | sK3 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1387,c_1383])).

cnf(c_2094,plain,
    ( k3_orders_2(sK2,sK3,sK0(sK2,sK3,sK4)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1388,c_1977])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11935,c_10751,c_6027,c_4802,c_4421,c_3451,c_2490,c_2305,c_2307,c_2094,c_2010,c_1890,c_1800,c_1685,c_1647,c_1644,c_1569,c_30,c_16,c_17])).


%------------------------------------------------------------------------------
