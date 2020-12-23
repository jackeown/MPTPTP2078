%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:37 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  160 (3626 expanded)
%              Number of clauses        :  107 ( 833 expanded)
%              Number of leaves         :   16 (1228 expanded)
%              Depth                    :   28
%              Number of atoms          :  823 (24987 expanded)
%              Number of equality atoms :  234 (1868 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f32,f31,f30])).

fof(f55,plain,(
    m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(nnf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
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
                    & ( ( k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2
                        & r2_hidden(sK1(X0,X1,X2),X1)
                        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k3_orders_2(X0,X1,X3) != X2
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( m1_orders_2(k3_orders_2(X0,X1,X3),X0,X1)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(k3_orders_2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
    inference(equality_resolution,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1458,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_16,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1453,plain,
    ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1452,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_11,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_137,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_11])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_436,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_18])).

cnf(c_437,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_436])).

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

cnf(c_441,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_437,c_22,c_21,c_20,c_19])).

cnf(c_1448,plain,
    ( k3_orders_2(sK2,X0,sK1(sK2,X0,X1)) = X1
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_2196,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,X0)) = X0
    | sK3 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1448])).

cnf(c_2252,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1453,c_2196])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1455,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2550,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1455])).

cnf(c_535,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_18])).

cnf(c_536,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_538,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_22,c_21,c_20,c_19])).

cnf(c_1444,plain,
    ( m1_orders_2(X0,sK2,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_538])).

cnf(c_1650,plain,
    ( m1_orders_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1452,c_1444])).

cnf(c_7,plain,
    ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_364,plain,
    ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X1)
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_365,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_369,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_365,c_22,c_21,c_20,c_19])).

cnf(c_387,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_369,c_4])).

cnf(c_1451,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_2437,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_1451])).

cnf(c_3517,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
    | m1_orders_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_2437])).

cnf(c_29,plain,
    ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_15,negated_conjecture,
    ( ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_308,plain,
    ( sK3 != X0
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_15])).

cnf(c_309,plain,
    ( sK4 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_6,plain,
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

cnf(c_552,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_553,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_552])).

cnf(c_557,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_553,c_22,c_21,c_20,c_19])).

cnf(c_567,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_557,c_538])).

cnf(c_670,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_567])).

cnf(c_671,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_1127,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1146,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1677,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1131,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1621,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != k1_zfmisc_1(u1_struct_0(sK2))
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1693,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_1696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1693])).

cnf(c_1694,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1721,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1886,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1127])).

cnf(c_1128,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2324,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_2325,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2324])).

cnf(c_1133,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1626,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X1 != sK2
    | X2 != sK3
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1133])).

cnf(c_1720,plain,
    ( m1_orders_2(X0,sK2,X1)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X1 != sK3
    | X0 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_1932,plain,
    ( m1_orders_2(X0,sK2,sK3)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X0 != sK4
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1720])).

cnf(c_2801,plain,
    ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1932])).

cnf(c_2809,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
    | sK2 != sK2
    | sK3 != sK3
    | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
    | m1_orders_2(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2801])).

cnf(c_2222,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_3424,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2222])).

cnf(c_3425,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3424])).

cnf(c_3584,plain,
    ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3517,c_17,c_29,c_309,c_671,c_1146,c_1677,c_1696,c_1694,c_1721,c_1886,c_2252,c_2325,c_2809,c_3425])).

cnf(c_3595,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3584,c_2196])).

cnf(c_3618,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3595,c_17,c_309,c_671,c_1146,c_1696,c_1694,c_1886,c_2325,c_3425])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_508,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X2,X3)
    | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_18])).

cnf(c_509,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_508])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_509,c_22,c_21,c_20,c_19])).

cnf(c_514,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
    inference(renaming,[status(thm)],[c_513])).

cnf(c_1445,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3626,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3618,c_1445])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2551,plain,
    ( m1_orders_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_1455])).

cnf(c_3594,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_2551])).

cnf(c_3822,plain,
    ( m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3626,c_28,c_3594])).

cnf(c_3832,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2550,c_3822])).

cnf(c_10,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_127,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10,c_11])).

cnf(c_484,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_18])).

cnf(c_485,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_489,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_485,c_22,c_21,c_20,c_19])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
    | sK2 != sK2
    | sK3 != X0
    | sK4 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_489])).

cnf(c_632,plain,
    ( m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_631])).

cnf(c_633,plain,
    ( k1_xboole_0 = sK3
    | m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1680,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1128])).

cnf(c_1895,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1680])).

cnf(c_1896,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_3834,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_3822])).

cnf(c_3878,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3832,c_17,c_28,c_309,c_633,c_671,c_1146,c_1677,c_1696,c_1694,c_1886,c_1896,c_2325,c_3425,c_3834])).

cnf(c_3879,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_3878])).

cnf(c_3891,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2252,c_3879])).

cnf(c_4076,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3891,c_17,c_309,c_671,c_1146,c_1696,c_1694,c_1886,c_2325,c_3425])).

cnf(c_4084,plain,
    ( r2_hidden(sK0(sK4,X0),sK3) = iProver_top
    | r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1458,c_4076])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1459,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4307,plain,
    ( r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4084,c_1459])).

cnf(c_30,plain,
    ( r1_tarski(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4307,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n014.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 10:04:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.98/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/0.96  
% 1.98/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/0.96  
% 1.98/0.96  ------  iProver source info
% 1.98/0.96  
% 1.98/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.98/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/0.96  git: non_committed_changes: false
% 1.98/0.96  git: last_make_outside_of_git: false
% 1.98/0.96  
% 1.98/0.96  ------ 
% 1.98/0.96  
% 1.98/0.96  ------ Input Options
% 1.98/0.96  
% 1.98/0.96  --out_options                           all
% 1.98/0.96  --tptp_safe_out                         true
% 1.98/0.96  --problem_path                          ""
% 1.98/0.96  --include_path                          ""
% 1.98/0.96  --clausifier                            res/vclausify_rel
% 1.98/0.96  --clausifier_options                    --mode clausify
% 1.98/0.96  --stdin                                 false
% 1.98/0.96  --stats_out                             all
% 1.98/0.96  
% 1.98/0.96  ------ General Options
% 1.98/0.96  
% 1.98/0.96  --fof                                   false
% 1.98/0.96  --time_out_real                         305.
% 1.98/0.96  --time_out_virtual                      -1.
% 1.98/0.96  --symbol_type_check                     false
% 1.98/0.96  --clausify_out                          false
% 1.98/0.96  --sig_cnt_out                           false
% 1.98/0.96  --trig_cnt_out                          false
% 1.98/0.96  --trig_cnt_out_tolerance                1.
% 1.98/0.96  --trig_cnt_out_sk_spl                   false
% 1.98/0.96  --abstr_cl_out                          false
% 1.98/0.96  
% 1.98/0.96  ------ Global Options
% 1.98/0.96  
% 1.98/0.96  --schedule                              default
% 1.98/0.96  --add_important_lit                     false
% 1.98/0.96  --prop_solver_per_cl                    1000
% 1.98/0.96  --min_unsat_core                        false
% 1.98/0.96  --soft_assumptions                      false
% 1.98/0.96  --soft_lemma_size                       3
% 1.98/0.96  --prop_impl_unit_size                   0
% 1.98/0.96  --prop_impl_unit                        []
% 1.98/0.96  --share_sel_clauses                     true
% 1.98/0.96  --reset_solvers                         false
% 1.98/0.96  --bc_imp_inh                            [conj_cone]
% 1.98/0.96  --conj_cone_tolerance                   3.
% 1.98/0.96  --extra_neg_conj                        none
% 1.98/0.96  --large_theory_mode                     true
% 1.98/0.96  --prolific_symb_bound                   200
% 1.98/0.96  --lt_threshold                          2000
% 1.98/0.96  --clause_weak_htbl                      true
% 1.98/0.96  --gc_record_bc_elim                     false
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing Options
% 1.98/0.96  
% 1.98/0.96  --preprocessing_flag                    true
% 1.98/0.96  --time_out_prep_mult                    0.1
% 1.98/0.96  --splitting_mode                        input
% 1.98/0.96  --splitting_grd                         true
% 1.98/0.96  --splitting_cvd                         false
% 1.98/0.96  --splitting_cvd_svl                     false
% 1.98/0.96  --splitting_nvd                         32
% 1.98/0.96  --sub_typing                            true
% 1.98/0.96  --prep_gs_sim                           true
% 1.98/0.96  --prep_unflatten                        true
% 1.98/0.96  --prep_res_sim                          true
% 1.98/0.96  --prep_upred                            true
% 1.98/0.96  --prep_sem_filter                       exhaustive
% 1.98/0.96  --prep_sem_filter_out                   false
% 1.98/0.96  --pred_elim                             true
% 1.98/0.96  --res_sim_input                         true
% 1.98/0.96  --eq_ax_congr_red                       true
% 1.98/0.96  --pure_diseq_elim                       true
% 1.98/0.96  --brand_transform                       false
% 1.98/0.96  --non_eq_to_eq                          false
% 1.98/0.96  --prep_def_merge                        true
% 1.98/0.96  --prep_def_merge_prop_impl              false
% 1.98/0.96  --prep_def_merge_mbd                    true
% 1.98/0.96  --prep_def_merge_tr_red                 false
% 1.98/0.96  --prep_def_merge_tr_cl                  false
% 1.98/0.96  --smt_preprocessing                     true
% 1.98/0.96  --smt_ac_axioms                         fast
% 1.98/0.96  --preprocessed_out                      false
% 1.98/0.96  --preprocessed_stats                    false
% 1.98/0.96  
% 1.98/0.96  ------ Abstraction refinement Options
% 1.98/0.96  
% 1.98/0.96  --abstr_ref                             []
% 1.98/0.96  --abstr_ref_prep                        false
% 1.98/0.96  --abstr_ref_until_sat                   false
% 1.98/0.96  --abstr_ref_sig_restrict                funpre
% 1.98/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.96  --abstr_ref_under                       []
% 1.98/0.96  
% 1.98/0.96  ------ SAT Options
% 1.98/0.96  
% 1.98/0.96  --sat_mode                              false
% 1.98/0.96  --sat_fm_restart_options                ""
% 1.98/0.96  --sat_gr_def                            false
% 1.98/0.96  --sat_epr_types                         true
% 1.98/0.96  --sat_non_cyclic_types                  false
% 1.98/0.96  --sat_finite_models                     false
% 1.98/0.96  --sat_fm_lemmas                         false
% 1.98/0.96  --sat_fm_prep                           false
% 1.98/0.96  --sat_fm_uc_incr                        true
% 1.98/0.96  --sat_out_model                         small
% 1.98/0.96  --sat_out_clauses                       false
% 1.98/0.96  
% 1.98/0.96  ------ QBF Options
% 1.98/0.96  
% 1.98/0.96  --qbf_mode                              false
% 1.98/0.96  --qbf_elim_univ                         false
% 1.98/0.96  --qbf_dom_inst                          none
% 1.98/0.96  --qbf_dom_pre_inst                      false
% 1.98/0.96  --qbf_sk_in                             false
% 1.98/0.96  --qbf_pred_elim                         true
% 1.98/0.96  --qbf_split                             512
% 1.98/0.96  
% 1.98/0.96  ------ BMC1 Options
% 1.98/0.96  
% 1.98/0.96  --bmc1_incremental                      false
% 1.98/0.96  --bmc1_axioms                           reachable_all
% 1.98/0.96  --bmc1_min_bound                        0
% 1.98/0.96  --bmc1_max_bound                        -1
% 1.98/0.96  --bmc1_max_bound_default                -1
% 1.98/0.96  --bmc1_symbol_reachability              true
% 1.98/0.96  --bmc1_property_lemmas                  false
% 1.98/0.96  --bmc1_k_induction                      false
% 1.98/0.96  --bmc1_non_equiv_states                 false
% 1.98/0.96  --bmc1_deadlock                         false
% 1.98/0.96  --bmc1_ucm                              false
% 1.98/0.96  --bmc1_add_unsat_core                   none
% 1.98/0.96  --bmc1_unsat_core_children              false
% 1.98/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.96  --bmc1_out_stat                         full
% 1.98/0.96  --bmc1_ground_init                      false
% 1.98/0.96  --bmc1_pre_inst_next_state              false
% 1.98/0.96  --bmc1_pre_inst_state                   false
% 1.98/0.96  --bmc1_pre_inst_reach_state             false
% 1.98/0.96  --bmc1_out_unsat_core                   false
% 1.98/0.96  --bmc1_aig_witness_out                  false
% 1.98/0.96  --bmc1_verbose                          false
% 1.98/0.96  --bmc1_dump_clauses_tptp                false
% 1.98/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.96  --bmc1_dump_file                        -
% 1.98/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.96  --bmc1_ucm_extend_mode                  1
% 1.98/0.96  --bmc1_ucm_init_mode                    2
% 1.98/0.96  --bmc1_ucm_cone_mode                    none
% 1.98/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.96  --bmc1_ucm_relax_model                  4
% 1.98/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.96  --bmc1_ucm_layered_model                none
% 1.98/0.96  --bmc1_ucm_max_lemma_size               10
% 1.98/0.96  
% 1.98/0.96  ------ AIG Options
% 1.98/0.96  
% 1.98/0.96  --aig_mode                              false
% 1.98/0.96  
% 1.98/0.96  ------ Instantiation Options
% 1.98/0.96  
% 1.98/0.96  --instantiation_flag                    true
% 1.98/0.96  --inst_sos_flag                         false
% 1.98/0.96  --inst_sos_phase                        true
% 1.98/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel_side                     num_symb
% 1.98/0.96  --inst_solver_per_active                1400
% 1.98/0.96  --inst_solver_calls_frac                1.
% 1.98/0.96  --inst_passive_queue_type               priority_queues
% 1.98/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.96  --inst_passive_queues_freq              [25;2]
% 1.98/0.96  --inst_dismatching                      true
% 1.98/0.96  --inst_eager_unprocessed_to_passive     true
% 1.98/0.96  --inst_prop_sim_given                   true
% 1.98/0.96  --inst_prop_sim_new                     false
% 1.98/0.96  --inst_subs_new                         false
% 1.98/0.96  --inst_eq_res_simp                      false
% 1.98/0.96  --inst_subs_given                       false
% 1.98/0.96  --inst_orphan_elimination               true
% 1.98/0.96  --inst_learning_loop_flag               true
% 1.98/0.96  --inst_learning_start                   3000
% 1.98/0.96  --inst_learning_factor                  2
% 1.98/0.96  --inst_start_prop_sim_after_learn       3
% 1.98/0.96  --inst_sel_renew                        solver
% 1.98/0.96  --inst_lit_activity_flag                true
% 1.98/0.96  --inst_restr_to_given                   false
% 1.98/0.96  --inst_activity_threshold               500
% 1.98/0.96  --inst_out_proof                        true
% 1.98/0.96  
% 1.98/0.96  ------ Resolution Options
% 1.98/0.96  
% 1.98/0.96  --resolution_flag                       true
% 1.98/0.96  --res_lit_sel                           adaptive
% 1.98/0.96  --res_lit_sel_side                      none
% 1.98/0.96  --res_ordering                          kbo
% 1.98/0.96  --res_to_prop_solver                    active
% 1.98/0.96  --res_prop_simpl_new                    false
% 1.98/0.96  --res_prop_simpl_given                  true
% 1.98/0.96  --res_passive_queue_type                priority_queues
% 1.98/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.96  --res_passive_queues_freq               [15;5]
% 1.98/0.96  --res_forward_subs                      full
% 1.98/0.96  --res_backward_subs                     full
% 1.98/0.96  --res_forward_subs_resolution           true
% 1.98/0.96  --res_backward_subs_resolution          true
% 1.98/0.96  --res_orphan_elimination                true
% 1.98/0.96  --res_time_limit                        2.
% 1.98/0.96  --res_out_proof                         true
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Options
% 1.98/0.96  
% 1.98/0.96  --superposition_flag                    true
% 1.98/0.96  --sup_passive_queue_type                priority_queues
% 1.98/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.96  --demod_completeness_check              fast
% 1.98/0.96  --demod_use_ground                      true
% 1.98/0.96  --sup_to_prop_solver                    passive
% 1.98/0.96  --sup_prop_simpl_new                    true
% 1.98/0.96  --sup_prop_simpl_given                  true
% 1.98/0.96  --sup_fun_splitting                     false
% 1.98/0.96  --sup_smt_interval                      50000
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Simplification Setup
% 1.98/0.96  
% 1.98/0.96  --sup_indices_passive                   []
% 1.98/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_full_bw                           [BwDemod]
% 1.98/0.96  --sup_immed_triv                        [TrivRules]
% 1.98/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_immed_bw_main                     []
% 1.98/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  
% 1.98/0.96  ------ Combination Options
% 1.98/0.96  
% 1.98/0.96  --comb_res_mult                         3
% 1.98/0.96  --comb_sup_mult                         2
% 1.98/0.96  --comb_inst_mult                        10
% 1.98/0.96  
% 1.98/0.96  ------ Debug Options
% 1.98/0.96  
% 1.98/0.96  --dbg_backtrace                         false
% 1.98/0.96  --dbg_dump_prop_clauses                 false
% 1.98/0.96  --dbg_dump_prop_clauses_file            -
% 1.98/0.96  --dbg_out_stat                          false
% 1.98/0.96  ------ Parsing...
% 1.98/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.98/0.96  ------ Proving...
% 1.98/0.96  ------ Problem Properties 
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  clauses                                 17
% 1.98/0.96  conjectures                             3
% 1.98/0.97  EPR                                     4
% 1.98/0.97  Horn                                    12
% 1.98/0.97  unary                                   4
% 1.98/0.97  binary                                  3
% 1.98/0.97  lits                                    50
% 1.98/0.97  lits eq                                 6
% 1.98/0.97  fd_pure                                 0
% 1.98/0.97  fd_pseudo                               0
% 1.98/0.97  fd_cond                                 4
% 1.98/0.97  fd_pseudo_cond                          0
% 1.98/0.97  AC symbols                              0
% 1.98/0.97  
% 1.98/0.97  ------ Schedule dynamic 5 is on 
% 1.98/0.97  
% 1.98/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  ------ 
% 1.98/0.97  Current options:
% 1.98/0.97  ------ 
% 1.98/0.97  
% 1.98/0.97  ------ Input Options
% 1.98/0.97  
% 1.98/0.97  --out_options                           all
% 1.98/0.97  --tptp_safe_out                         true
% 1.98/0.97  --problem_path                          ""
% 1.98/0.97  --include_path                          ""
% 1.98/0.97  --clausifier                            res/vclausify_rel
% 1.98/0.97  --clausifier_options                    --mode clausify
% 1.98/0.97  --stdin                                 false
% 1.98/0.97  --stats_out                             all
% 1.98/0.97  
% 1.98/0.97  ------ General Options
% 1.98/0.97  
% 1.98/0.97  --fof                                   false
% 1.98/0.97  --time_out_real                         305.
% 1.98/0.97  --time_out_virtual                      -1.
% 1.98/0.97  --symbol_type_check                     false
% 1.98/0.97  --clausify_out                          false
% 1.98/0.97  --sig_cnt_out                           false
% 1.98/0.97  --trig_cnt_out                          false
% 1.98/0.97  --trig_cnt_out_tolerance                1.
% 1.98/0.97  --trig_cnt_out_sk_spl                   false
% 1.98/0.97  --abstr_cl_out                          false
% 1.98/0.97  
% 1.98/0.97  ------ Global Options
% 1.98/0.97  
% 1.98/0.97  --schedule                              default
% 1.98/0.97  --add_important_lit                     false
% 1.98/0.97  --prop_solver_per_cl                    1000
% 1.98/0.97  --min_unsat_core                        false
% 1.98/0.97  --soft_assumptions                      false
% 1.98/0.97  --soft_lemma_size                       3
% 1.98/0.97  --prop_impl_unit_size                   0
% 1.98/0.97  --prop_impl_unit                        []
% 1.98/0.97  --share_sel_clauses                     true
% 1.98/0.97  --reset_solvers                         false
% 1.98/0.97  --bc_imp_inh                            [conj_cone]
% 1.98/0.97  --conj_cone_tolerance                   3.
% 1.98/0.97  --extra_neg_conj                        none
% 1.98/0.97  --large_theory_mode                     true
% 1.98/0.97  --prolific_symb_bound                   200
% 1.98/0.97  --lt_threshold                          2000
% 1.98/0.97  --clause_weak_htbl                      true
% 1.98/0.97  --gc_record_bc_elim                     false
% 1.98/0.97  
% 1.98/0.97  ------ Preprocessing Options
% 1.98/0.97  
% 1.98/0.97  --preprocessing_flag                    true
% 1.98/0.97  --time_out_prep_mult                    0.1
% 1.98/0.97  --splitting_mode                        input
% 1.98/0.97  --splitting_grd                         true
% 1.98/0.97  --splitting_cvd                         false
% 1.98/0.97  --splitting_cvd_svl                     false
% 1.98/0.97  --splitting_nvd                         32
% 1.98/0.97  --sub_typing                            true
% 1.98/0.97  --prep_gs_sim                           true
% 1.98/0.97  --prep_unflatten                        true
% 1.98/0.97  --prep_res_sim                          true
% 1.98/0.97  --prep_upred                            true
% 1.98/0.97  --prep_sem_filter                       exhaustive
% 1.98/0.97  --prep_sem_filter_out                   false
% 1.98/0.97  --pred_elim                             true
% 1.98/0.97  --res_sim_input                         true
% 1.98/0.97  --eq_ax_congr_red                       true
% 1.98/0.97  --pure_diseq_elim                       true
% 1.98/0.97  --brand_transform                       false
% 1.98/0.97  --non_eq_to_eq                          false
% 1.98/0.97  --prep_def_merge                        true
% 1.98/0.97  --prep_def_merge_prop_impl              false
% 1.98/0.97  --prep_def_merge_mbd                    true
% 1.98/0.97  --prep_def_merge_tr_red                 false
% 1.98/0.97  --prep_def_merge_tr_cl                  false
% 1.98/0.97  --smt_preprocessing                     true
% 1.98/0.97  --smt_ac_axioms                         fast
% 1.98/0.97  --preprocessed_out                      false
% 1.98/0.97  --preprocessed_stats                    false
% 1.98/0.97  
% 1.98/0.97  ------ Abstraction refinement Options
% 1.98/0.97  
% 1.98/0.97  --abstr_ref                             []
% 1.98/0.97  --abstr_ref_prep                        false
% 1.98/0.97  --abstr_ref_until_sat                   false
% 1.98/0.97  --abstr_ref_sig_restrict                funpre
% 1.98/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.97  --abstr_ref_under                       []
% 1.98/0.97  
% 1.98/0.97  ------ SAT Options
% 1.98/0.97  
% 1.98/0.97  --sat_mode                              false
% 1.98/0.97  --sat_fm_restart_options                ""
% 1.98/0.97  --sat_gr_def                            false
% 1.98/0.97  --sat_epr_types                         true
% 1.98/0.97  --sat_non_cyclic_types                  false
% 1.98/0.97  --sat_finite_models                     false
% 1.98/0.97  --sat_fm_lemmas                         false
% 1.98/0.97  --sat_fm_prep                           false
% 1.98/0.97  --sat_fm_uc_incr                        true
% 1.98/0.97  --sat_out_model                         small
% 1.98/0.97  --sat_out_clauses                       false
% 1.98/0.97  
% 1.98/0.97  ------ QBF Options
% 1.98/0.97  
% 1.98/0.97  --qbf_mode                              false
% 1.98/0.97  --qbf_elim_univ                         false
% 1.98/0.97  --qbf_dom_inst                          none
% 1.98/0.97  --qbf_dom_pre_inst                      false
% 1.98/0.97  --qbf_sk_in                             false
% 1.98/0.97  --qbf_pred_elim                         true
% 1.98/0.97  --qbf_split                             512
% 1.98/0.97  
% 1.98/0.97  ------ BMC1 Options
% 1.98/0.97  
% 1.98/0.97  --bmc1_incremental                      false
% 1.98/0.97  --bmc1_axioms                           reachable_all
% 1.98/0.97  --bmc1_min_bound                        0
% 1.98/0.97  --bmc1_max_bound                        -1
% 1.98/0.97  --bmc1_max_bound_default                -1
% 1.98/0.97  --bmc1_symbol_reachability              true
% 1.98/0.97  --bmc1_property_lemmas                  false
% 1.98/0.97  --bmc1_k_induction                      false
% 1.98/0.97  --bmc1_non_equiv_states                 false
% 1.98/0.97  --bmc1_deadlock                         false
% 1.98/0.97  --bmc1_ucm                              false
% 1.98/0.97  --bmc1_add_unsat_core                   none
% 1.98/0.97  --bmc1_unsat_core_children              false
% 1.98/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.97  --bmc1_out_stat                         full
% 1.98/0.97  --bmc1_ground_init                      false
% 1.98/0.97  --bmc1_pre_inst_next_state              false
% 1.98/0.97  --bmc1_pre_inst_state                   false
% 1.98/0.97  --bmc1_pre_inst_reach_state             false
% 1.98/0.97  --bmc1_out_unsat_core                   false
% 1.98/0.97  --bmc1_aig_witness_out                  false
% 1.98/0.97  --bmc1_verbose                          false
% 1.98/0.97  --bmc1_dump_clauses_tptp                false
% 1.98/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.97  --bmc1_dump_file                        -
% 1.98/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.97  --bmc1_ucm_extend_mode                  1
% 1.98/0.97  --bmc1_ucm_init_mode                    2
% 1.98/0.97  --bmc1_ucm_cone_mode                    none
% 1.98/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.97  --bmc1_ucm_relax_model                  4
% 1.98/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.97  --bmc1_ucm_layered_model                none
% 1.98/0.97  --bmc1_ucm_max_lemma_size               10
% 1.98/0.97  
% 1.98/0.97  ------ AIG Options
% 1.98/0.97  
% 1.98/0.97  --aig_mode                              false
% 1.98/0.97  
% 1.98/0.97  ------ Instantiation Options
% 1.98/0.97  
% 1.98/0.97  --instantiation_flag                    true
% 1.98/0.97  --inst_sos_flag                         false
% 1.98/0.97  --inst_sos_phase                        true
% 1.98/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.97  --inst_lit_sel_side                     none
% 1.98/0.97  --inst_solver_per_active                1400
% 1.98/0.97  --inst_solver_calls_frac                1.
% 1.98/0.97  --inst_passive_queue_type               priority_queues
% 1.98/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.97  --inst_passive_queues_freq              [25;2]
% 1.98/0.97  --inst_dismatching                      true
% 1.98/0.97  --inst_eager_unprocessed_to_passive     true
% 1.98/0.97  --inst_prop_sim_given                   true
% 1.98/0.97  --inst_prop_sim_new                     false
% 1.98/0.97  --inst_subs_new                         false
% 1.98/0.97  --inst_eq_res_simp                      false
% 1.98/0.97  --inst_subs_given                       false
% 1.98/0.97  --inst_orphan_elimination               true
% 1.98/0.97  --inst_learning_loop_flag               true
% 1.98/0.97  --inst_learning_start                   3000
% 1.98/0.97  --inst_learning_factor                  2
% 1.98/0.97  --inst_start_prop_sim_after_learn       3
% 1.98/0.97  --inst_sel_renew                        solver
% 1.98/0.97  --inst_lit_activity_flag                true
% 1.98/0.97  --inst_restr_to_given                   false
% 1.98/0.97  --inst_activity_threshold               500
% 1.98/0.97  --inst_out_proof                        true
% 1.98/0.97  
% 1.98/0.97  ------ Resolution Options
% 1.98/0.97  
% 1.98/0.97  --resolution_flag                       false
% 1.98/0.97  --res_lit_sel                           adaptive
% 1.98/0.97  --res_lit_sel_side                      none
% 1.98/0.97  --res_ordering                          kbo
% 1.98/0.97  --res_to_prop_solver                    active
% 1.98/0.97  --res_prop_simpl_new                    false
% 1.98/0.97  --res_prop_simpl_given                  true
% 1.98/0.97  --res_passive_queue_type                priority_queues
% 1.98/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.97  --res_passive_queues_freq               [15;5]
% 1.98/0.97  --res_forward_subs                      full
% 1.98/0.97  --res_backward_subs                     full
% 1.98/0.97  --res_forward_subs_resolution           true
% 1.98/0.97  --res_backward_subs_resolution          true
% 1.98/0.97  --res_orphan_elimination                true
% 1.98/0.97  --res_time_limit                        2.
% 1.98/0.97  --res_out_proof                         true
% 1.98/0.97  
% 1.98/0.97  ------ Superposition Options
% 1.98/0.97  
% 1.98/0.97  --superposition_flag                    true
% 1.98/0.97  --sup_passive_queue_type                priority_queues
% 1.98/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.97  --demod_completeness_check              fast
% 1.98/0.97  --demod_use_ground                      true
% 1.98/0.97  --sup_to_prop_solver                    passive
% 1.98/0.97  --sup_prop_simpl_new                    true
% 1.98/0.97  --sup_prop_simpl_given                  true
% 1.98/0.97  --sup_fun_splitting                     false
% 1.98/0.97  --sup_smt_interval                      50000
% 1.98/0.97  
% 1.98/0.97  ------ Superposition Simplification Setup
% 1.98/0.97  
% 1.98/0.97  --sup_indices_passive                   []
% 1.98/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.97  --sup_full_bw                           [BwDemod]
% 1.98/0.97  --sup_immed_triv                        [TrivRules]
% 1.98/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.97  --sup_immed_bw_main                     []
% 1.98/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.97  
% 1.98/0.97  ------ Combination Options
% 1.98/0.97  
% 1.98/0.97  --comb_res_mult                         3
% 1.98/0.97  --comb_sup_mult                         2
% 1.98/0.97  --comb_inst_mult                        10
% 1.98/0.97  
% 1.98/0.97  ------ Debug Options
% 1.98/0.97  
% 1.98/0.97  --dbg_backtrace                         false
% 1.98/0.97  --dbg_dump_prop_clauses                 false
% 1.98/0.97  --dbg_dump_prop_clauses_file            -
% 1.98/0.97  --dbg_out_stat                          false
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  ------ Proving...
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  % SZS status Theorem for theBenchmark.p
% 1.98/0.97  
% 1.98/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.98/0.97  
% 1.98/0.97  fof(f1,axiom,(
% 1.98/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f9,plain,(
% 1.98/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.98/0.97    inference(ennf_transformation,[],[f1])).
% 1.98/0.97  
% 1.98/0.97  fof(f20,plain,(
% 1.98/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.97    inference(nnf_transformation,[],[f9])).
% 1.98/0.97  
% 1.98/0.97  fof(f21,plain,(
% 1.98/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.97    inference(rectify,[],[f20])).
% 1.98/0.97  
% 1.98/0.97  fof(f22,plain,(
% 1.98/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f23,plain,(
% 1.98/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.98/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 1.98/0.97  
% 1.98/0.97  fof(f35,plain,(
% 1.98/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f23])).
% 1.98/0.97  
% 1.98/0.97  fof(f7,conjecture,(
% 1.98/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f8,negated_conjecture,(
% 1.98/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.98/0.97    inference(negated_conjecture,[],[f7])).
% 1.98/0.97  
% 1.98/0.97  fof(f18,plain,(
% 1.98/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.98/0.97    inference(ennf_transformation,[],[f8])).
% 1.98/0.97  
% 1.98/0.97  fof(f19,plain,(
% 1.98/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.98/0.97    inference(flattening,[],[f18])).
% 1.98/0.97  
% 1.98/0.97  fof(f32,plain,(
% 1.98/0.97    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) => (~r1_tarski(sK4,X1) & m1_orders_2(sK4,X0,X1))) )),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f31,plain,(
% 1.98/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(X2,sK3) & m1_orders_2(X2,X0,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f30,plain,(
% 1.98/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,sK2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f33,plain,(
% 1.98/0.97    ((~r1_tarski(sK4,sK3) & m1_orders_2(sK4,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.98/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f32,f31,f30])).
% 1.98/0.97  
% 1.98/0.97  fof(f55,plain,(
% 1.98/0.97    m1_orders_2(sK4,sK2,sK3)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f54,plain,(
% 1.98/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f4,axiom,(
% 1.98/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f12,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.98/0.97    inference(ennf_transformation,[],[f4])).
% 1.98/0.97  
% 1.98/0.97  fof(f13,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(flattening,[],[f12])).
% 1.98/0.97  
% 1.98/0.97  fof(f24,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(nnf_transformation,[],[f13])).
% 1.98/0.97  
% 1.98/0.97  fof(f25,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(rectify,[],[f24])).
% 1.98/0.97  
% 1.98/0.97  fof(f26,plain,(
% 1.98/0.97    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f27,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 1.98/0.97  
% 1.98/0.97  fof(f41,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f27])).
% 1.98/0.97  
% 1.98/0.97  fof(f5,axiom,(
% 1.98/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f14,plain,(
% 1.98/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.98/0.97    inference(ennf_transformation,[],[f5])).
% 1.98/0.97  
% 1.98/0.97  fof(f15,plain,(
% 1.98/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(flattening,[],[f14])).
% 1.98/0.97  
% 1.98/0.97  fof(f45,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f15])).
% 1.98/0.97  
% 1.98/0.97  fof(f53,plain,(
% 1.98/0.97    l1_orders_2(sK2)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f49,plain,(
% 1.98/0.97    ~v2_struct_0(sK2)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f50,plain,(
% 1.98/0.97    v3_orders_2(sK2)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f51,plain,(
% 1.98/0.97    v4_orders_2(sK2)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f52,plain,(
% 1.98/0.97    v5_orders_2(sK2)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f3,axiom,(
% 1.98/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f10,plain,(
% 1.98/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.98/0.97    inference(ennf_transformation,[],[f3])).
% 1.98/0.97  
% 1.98/0.97  fof(f11,plain,(
% 1.98/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.98/0.97    inference(flattening,[],[f10])).
% 1.98/0.97  
% 1.98/0.97  fof(f38,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f11])).
% 1.98/0.97  
% 1.98/0.97  fof(f42,plain,(
% 1.98/0.97    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X1) | k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f27])).
% 1.98/0.97  
% 1.98/0.97  fof(f60,plain,(
% 1.98/0.97    ( ! [X0,X3,X1] : (m1_orders_2(k3_orders_2(X0,X1,X3),X0,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(k3_orders_2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(equality_resolution,[],[f42])).
% 1.98/0.97  
% 1.98/0.97  fof(f2,axiom,(
% 1.98/0.97    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f37,plain,(
% 1.98/0.97    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f2])).
% 1.98/0.97  
% 1.98/0.97  fof(f56,plain,(
% 1.98/0.97    ~r1_tarski(sK4,sK3)),
% 1.98/0.97    inference(cnf_transformation,[],[f33])).
% 1.98/0.97  
% 1.98/0.97  fof(f43,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f27])).
% 1.98/0.97  
% 1.98/0.97  fof(f59,plain,(
% 1.98/0.97    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(equality_resolution,[],[f43])).
% 1.98/0.97  
% 1.98/0.97  fof(f6,axiom,(
% 1.98/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.98/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f16,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.98/0.97    inference(ennf_transformation,[],[f6])).
% 1.98/0.97  
% 1.98/0.97  fof(f17,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(flattening,[],[f16])).
% 1.98/0.97  
% 1.98/0.97  fof(f28,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(nnf_transformation,[],[f17])).
% 1.98/0.97  
% 1.98/0.97  fof(f29,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.98/0.97    inference(flattening,[],[f28])).
% 1.98/0.97  
% 1.98/0.97  fof(f47,plain,(
% 1.98/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f29])).
% 1.98/0.97  
% 1.98/0.97  fof(f39,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f27])).
% 1.98/0.97  
% 1.98/0.97  fof(f36,plain,(
% 1.98/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f23])).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1,plain,
% 1.98/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1458,plain,
% 1.98/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 1.98/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_16,negated_conjecture,
% 1.98/0.97      ( m1_orders_2(sK4,sK2,sK3) ),
% 1.98/0.97      inference(cnf_transformation,[],[f55]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1453,plain,
% 1.98/0.97      ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_17,negated_conjecture,
% 1.98/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.98/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1452,plain,
% 1.98/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_8,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1)
% 1.98/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(cnf_transformation,[],[f41]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_11,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f45]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_137,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1)
% 1.98/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_8,c_11]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_18,negated_conjecture,
% 1.98/0.97      ( l1_orders_2(sK2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_436,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 1.98/0.97      | sK2 != X1
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_137,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_437,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2)
% 1.98/0.97      | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_436]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_22,negated_conjecture,
% 1.98/0.97      ( ~ v2_struct_0(sK2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_21,negated_conjecture,
% 1.98/0.97      ( v3_orders_2(sK2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f50]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_20,negated_conjecture,
% 1.98/0.97      ( v4_orders_2(sK2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_19,negated_conjecture,
% 1.98/0.97      ( v5_orders_2(sK2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_441,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_437,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1448,plain,
% 1.98/0.97      ( k3_orders_2(sK2,X0,sK1(sK2,X0,X1)) = X1
% 1.98/0.97      | k1_xboole_0 = X0
% 1.98/0.97      | m1_orders_2(X1,sK2,X0) != iProver_top
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2196,plain,
% 1.98/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,X0)) = X0
% 1.98/0.97      | sK3 = k1_xboole_0
% 1.98/0.97      | m1_orders_2(X0,sK2,sK3) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1452,c_1448]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2252,plain,
% 1.98/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) = sK4 | sK3 = k1_xboole_0 ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1453,c_2196]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 1.98/0.97      | ~ r2_hidden(X0,X2) ),
% 1.98/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1455,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 1.98/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 1.98/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2550,plain,
% 1.98/0.97      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1452,c_1455]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_535,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | sK2 != X1 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_11,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_536,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2) ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_535]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_538,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_536,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1444,plain,
% 1.98/0.97      ( m1_orders_2(X0,sK2,X1) != iProver_top
% 1.98/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_538]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1650,plain,
% 1.98/0.97      ( m1_orders_2(X0,sK2,sK3) != iProver_top
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1452,c_1444]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_7,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 1.98/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.98/0.97      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 1.98/0.97      | ~ r2_hidden(X2,X1)
% 1.98/0.97      | v2_struct_0(X0)
% 1.98/0.97      | ~ v3_orders_2(X0)
% 1.98/0.97      | ~ v4_orders_2(X0)
% 1.98/0.97      | ~ v5_orders_2(X0)
% 1.98/0.97      | ~ l1_orders_2(X0)
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(cnf_transformation,[],[f60]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_364,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 1.98/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.98/0.97      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 1.98/0.97      | ~ r2_hidden(X2,X1)
% 1.98/0.97      | v2_struct_0(X0)
% 1.98/0.97      | ~ v3_orders_2(X0)
% 1.98/0.97      | ~ v4_orders_2(X0)
% 1.98/0.97      | ~ v5_orders_2(X0)
% 1.98/0.97      | sK2 != X0
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_365,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 1.98/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ r2_hidden(X1,X0)
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2)
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_364]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_369,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 1.98/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ r2_hidden(X1,X0)
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_365,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_387,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ r2_hidden(X1,X0)
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_369,c_4]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1451,plain,
% 1.98/0.97      ( k1_xboole_0 = X0
% 1.98/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2437,plain,
% 1.98/0.97      ( k1_xboole_0 = X0
% 1.98/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
% 1.98/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,sK3) != iProver_top
% 1.98/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1650,c_1451]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3517,plain,
% 1.98/0.97      ( sK3 = k1_xboole_0
% 1.98/0.97      | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
% 1.98/0.97      | m1_orders_2(sK4,sK2,sK3) != iProver_top
% 1.98/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | r2_hidden(sK1(sK2,sK3,sK4),sK3) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_2252,c_2437]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_29,plain,
% 1.98/0.97      ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3,plain,
% 1.98/0.97      ( r1_tarski(k1_xboole_0,X0) ),
% 1.98/0.97      inference(cnf_transformation,[],[f37]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_15,negated_conjecture,
% 1.98/0.97      ( ~ r1_tarski(sK4,sK3) ),
% 1.98/0.97      inference(cnf_transformation,[],[f56]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_308,plain,
% 1.98/0.97      ( sK3 != X0 | sK4 != k1_xboole_0 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_15]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_309,plain,
% 1.98/0.97      ( sK4 != k1_xboole_0 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_308]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_6,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1)
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(cnf_transformation,[],[f59]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_552,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | sK2 != X1
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_553,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2)
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_552]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_557,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_553,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_567,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 1.98/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(forward_subsumption_resolution,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_557,c_538]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_670,plain,
% 1.98/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | sK2 != sK2
% 1.98/0.97      | sK3 != k1_xboole_0
% 1.98/0.97      | sK4 != X0
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_567]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_671,plain,
% 1.98/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | sK3 != k1_xboole_0
% 1.98/0.97      | k1_xboole_0 = sK4 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_670]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1127,plain,( X0 = X0 ),theory(equality) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1146,plain,
% 1.98/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1677,plain,
% 1.98/0.97      ( sK3 = sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1131,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 1.98/0.97      theory(equality) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1621,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1)
% 1.98/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | X1 != k1_zfmisc_1(u1_struct_0(sK2))
% 1.98/0.97      | X0 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1131]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1693,plain,
% 1.98/0.97      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | X0 != sK3
% 1.98/0.97      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1621]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1696,plain,
% 1.98/0.97      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 1.98/0.97      | k1_xboole_0 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1693]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1694,plain,
% 1.98/0.97      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1721,plain,
% 1.98/0.97      ( sK2 = sK2 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1886,plain,
% 1.98/0.97      ( sK4 = sK4 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1127]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1128,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2324,plain,
% 1.98/0.97      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2325,plain,
% 1.98/0.97      ( sK3 != k1_xboole_0
% 1.98/0.97      | k1_xboole_0 = sK3
% 1.98/0.97      | k1_xboole_0 != k1_xboole_0 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_2324]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1133,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | m1_orders_2(X3,X4,X5)
% 1.98/0.97      | X3 != X0
% 1.98/0.97      | X4 != X1
% 1.98/0.97      | X5 != X2 ),
% 1.98/0.97      theory(equality) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1626,plain,
% 1.98/0.97      ( m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_orders_2(sK4,sK2,sK3)
% 1.98/0.97      | X1 != sK2
% 1.98/0.97      | X2 != sK3
% 1.98/0.97      | X0 != sK4 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1133]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1720,plain,
% 1.98/0.97      ( m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_orders_2(sK4,sK2,sK3)
% 1.98/0.97      | X1 != sK3
% 1.98/0.97      | X0 != sK4
% 1.98/0.97      | sK2 != sK2 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1626]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1932,plain,
% 1.98/0.97      ( m1_orders_2(X0,sK2,sK3)
% 1.98/0.97      | ~ m1_orders_2(sK4,sK2,sK3)
% 1.98/0.97      | X0 != sK4
% 1.98/0.97      | sK2 != sK2
% 1.98/0.97      | sK3 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1720]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2801,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3)
% 1.98/0.97      | ~ m1_orders_2(sK4,sK2,sK3)
% 1.98/0.97      | k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
% 1.98/0.97      | sK2 != sK2
% 1.98/0.97      | sK3 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1932]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2809,plain,
% 1.98/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
% 1.98/0.97      | sK2 != sK2
% 1.98/0.97      | sK3 != sK3
% 1.98/0.97      | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
% 1.98/0.97      | m1_orders_2(sK4,sK2,sK3) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_2801]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2222,plain,
% 1.98/0.97      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3424,plain,
% 1.98/0.97      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_2222]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3425,plain,
% 1.98/0.97      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_3424]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3584,plain,
% 1.98/0.97      ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3517,c_17,c_29,c_309,c_671,c_1146,c_1677,c_1696,
% 1.98/0.97                 c_1694,c_1721,c_1886,c_2252,c_2325,c_2809,c_3425]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3595,plain,
% 1.98/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))
% 1.98/0.97      | sK3 = k1_xboole_0 ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3584,c_2196]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3618,plain,
% 1.98/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3595,c_17,c_309,c_671,c_1146,c_1696,c_1694,c_1886,
% 1.98/0.97                 c_2325,c_3425]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_13,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.98/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.98/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | r2_hidden(X2,X3)
% 1.98/0.97      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f47]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_508,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.98/0.97      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 1.98/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | r2_hidden(X2,X3)
% 1.98/0.97      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | sK2 != X1 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_509,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | r2_hidden(X0,X2)
% 1.98/0.97      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2) ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_508]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_513,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | r2_hidden(X0,X2)
% 1.98/0.97      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_509,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_514,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | r2_hidden(X1,X2)
% 1.98/0.97      | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
% 1.98/0.97      inference(renaming,[status(thm)],[c_513]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1445,plain,
% 1.98/0.97      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,X2) = iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,X2,X1)) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3626,plain,
% 1.98/0.97      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3618,c_1445]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_28,plain,
% 1.98/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2551,plain,
% 1.98/0.97      ( m1_orders_2(X0,sK2,sK3) != iProver_top
% 1.98/0.97      | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
% 1.98/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1650,c_1455]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3594,plain,
% 1.98/0.97      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3584,c_2551]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3822,plain,
% 1.98/0.97      ( m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3626,c_28,c_3594]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3832,plain,
% 1.98/0.97      ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top
% 1.98/0.97      | r2_hidden(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),sK3) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_2550,c_3822]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_10,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1)
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_127,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | ~ l1_orders_2(X1)
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_10,c_11]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_484,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.98/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.98/0.97      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 1.98/0.97      | v2_struct_0(X1)
% 1.98/0.97      | ~ v3_orders_2(X1)
% 1.98/0.97      | ~ v4_orders_2(X1)
% 1.98/0.97      | ~ v5_orders_2(X1)
% 1.98/0.97      | sK2 != X1
% 1.98/0.97      | k1_xboole_0 = X2 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_127,c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_485,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.98/0.97      | v2_struct_0(sK2)
% 1.98/0.97      | ~ v3_orders_2(sK2)
% 1.98/0.97      | ~ v4_orders_2(sK2)
% 1.98/0.97      | ~ v5_orders_2(sK2)
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_484]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_489,plain,
% 1.98/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 1.98/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 1.98/0.97      | k1_xboole_0 = X1 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_485,c_22,c_21,c_20,c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_631,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2))
% 1.98/0.97      | sK2 != sK2
% 1.98/0.97      | sK3 != X0
% 1.98/0.97      | sK4 != X1
% 1.98/0.97      | k1_xboole_0 = X0 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_489]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_632,plain,
% 1.98/0.97      ( m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2))
% 1.98/0.97      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 1.98/0.97      | k1_xboole_0 = sK3 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_631]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_633,plain,
% 1.98/0.97      ( k1_xboole_0 = sK3
% 1.98/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) = iProver_top
% 1.98/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1680,plain,
% 1.98/0.97      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1128]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1895,plain,
% 1.98/0.97      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1680]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1896,plain,
% 1.98/0.97      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1895]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3834,plain,
% 1.98/0.97      ( sK3 = k1_xboole_0
% 1.98/0.97      | m1_subset_1(sK1(sK2,sK3,sK4),u1_struct_0(sK2)) != iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_2252,c_3822]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3878,plain,
% 1.98/0.97      ( r2_hidden(X0,sK3) = iProver_top
% 1.98/0.97      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3832,c_17,c_28,c_309,c_633,c_671,c_1146,c_1677,c_1696,
% 1.98/0.97                 c_1694,c_1886,c_1896,c_2325,c_3425,c_3834]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3879,plain,
% 1.98/0.97      ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top ),
% 1.98/0.97      inference(renaming,[status(thm)],[c_3878]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3891,plain,
% 1.98/0.97      ( sK3 = k1_xboole_0
% 1.98/0.97      | r2_hidden(X0,sK3) = iProver_top
% 1.98/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_2252,c_3879]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4076,plain,
% 1.98/0.97      ( r2_hidden(X0,sK3) = iProver_top
% 1.98/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3891,c_17,c_309,c_671,c_1146,c_1696,c_1694,c_1886,
% 1.98/0.97                 c_2325,c_3425]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4084,plain,
% 1.98/0.97      ( r2_hidden(sK0(sK4,X0),sK3) = iProver_top
% 1.98/0.97      | r1_tarski(sK4,X0) = iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1458,c_4076]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_0,plain,
% 1.98/0.97      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1459,plain,
% 1.98/0.97      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 1.98/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4307,plain,
% 1.98/0.97      ( r1_tarski(sK4,sK3) = iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_4084,c_1459]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_30,plain,
% 1.98/0.97      ( r1_tarski(sK4,sK3) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(contradiction,plain,
% 1.98/0.97      ( $false ),
% 1.98/0.97      inference(minisat,[status(thm)],[c_4307,c_30]) ).
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.98/0.97  
% 1.98/0.97  ------                               Statistics
% 1.98/0.97  
% 1.98/0.97  ------ General
% 1.98/0.97  
% 1.98/0.97  abstr_ref_over_cycles:                  0
% 1.98/0.97  abstr_ref_under_cycles:                 0
% 1.98/0.97  gc_basic_clause_elim:                   0
% 1.98/0.97  forced_gc_time:                         0
% 1.98/0.97  parsing_time:                           0.009
% 1.98/0.97  unif_index_cands_time:                  0.
% 1.98/0.97  unif_index_add_time:                    0.
% 1.98/0.97  orderings_time:                         0.
% 1.98/0.97  out_proof_time:                         0.01
% 1.98/0.97  total_time:                             0.161
% 1.98/0.97  num_of_symbols:                         50
% 1.98/0.97  num_of_terms:                           3205
% 1.98/0.97  
% 1.98/0.97  ------ Preprocessing
% 1.98/0.97  
% 1.98/0.97  num_of_splits:                          0
% 1.98/0.97  num_of_split_atoms:                     0
% 1.98/0.97  num_of_reused_defs:                     0
% 1.98/0.97  num_eq_ax_congr_red:                    20
% 1.98/0.97  num_of_sem_filtered_clauses:            1
% 1.98/0.97  num_of_subtypes:                        0
% 1.98/0.97  monotx_restored_types:                  0
% 1.98/0.97  sat_num_of_epr_types:                   0
% 1.98/0.97  sat_num_of_non_cyclic_types:            0
% 1.98/0.97  sat_guarded_non_collapsed_types:        0
% 1.98/0.97  num_pure_diseq_elim:                    0
% 1.98/0.97  simp_replaced_by:                       0
% 1.98/0.97  res_preprocessed:                       95
% 1.98/0.97  prep_upred:                             0
% 1.98/0.97  prep_unflattend:                        87
% 1.98/0.97  smt_new_axioms:                         0
% 1.98/0.97  pred_elim_cands:                        4
% 1.98/0.97  pred_elim:                              6
% 1.98/0.97  pred_elim_cl:                           6
% 1.98/0.97  pred_elim_cycles:                       10
% 1.98/0.97  merged_defs:                            0
% 1.98/0.97  merged_defs_ncl:                        0
% 1.98/0.97  bin_hyper_res:                          0
% 1.98/0.97  prep_cycles:                            4
% 1.98/0.97  pred_elim_time:                         0.016
% 1.98/0.97  splitting_time:                         0.
% 1.98/0.97  sem_filter_time:                        0.
% 1.98/0.97  monotx_time:                            0.001
% 1.98/0.97  subtype_inf_time:                       0.
% 1.98/0.97  
% 1.98/0.97  ------ Problem properties
% 1.98/0.97  
% 1.98/0.97  clauses:                                17
% 1.98/0.97  conjectures:                            3
% 1.98/0.97  epr:                                    4
% 1.98/0.97  horn:                                   12
% 1.98/0.97  ground:                                 4
% 1.98/0.97  unary:                                  4
% 1.98/0.97  binary:                                 3
% 1.98/0.97  lits:                                   50
% 1.98/0.97  lits_eq:                                6
% 1.98/0.97  fd_pure:                                0
% 1.98/0.97  fd_pseudo:                              0
% 1.98/0.97  fd_cond:                                4
% 1.98/0.97  fd_pseudo_cond:                         0
% 1.98/0.97  ac_symbols:                             0
% 1.98/0.97  
% 1.98/0.97  ------ Propositional Solver
% 1.98/0.97  
% 1.98/0.97  prop_solver_calls:                      27
% 1.98/0.97  prop_fast_solver_calls:                 1067
% 1.98/0.97  smt_solver_calls:                       0
% 1.98/0.97  smt_fast_solver_calls:                  0
% 1.98/0.97  prop_num_of_clauses:                    1232
% 1.98/0.97  prop_preprocess_simplified:             4078
% 1.98/0.97  prop_fo_subsumed:                       61
% 1.98/0.97  prop_solver_time:                       0.
% 1.98/0.97  smt_solver_time:                        0.
% 1.98/0.97  smt_fast_solver_time:                   0.
% 1.98/0.97  prop_fast_solver_time:                  0.
% 1.98/0.97  prop_unsat_core_time:                   0.
% 1.98/0.97  
% 1.98/0.97  ------ QBF
% 1.98/0.97  
% 1.98/0.97  qbf_q_res:                              0
% 1.98/0.97  qbf_num_tautologies:                    0
% 1.98/0.97  qbf_prep_cycles:                        0
% 1.98/0.97  
% 1.98/0.97  ------ BMC1
% 1.98/0.97  
% 1.98/0.97  bmc1_current_bound:                     -1
% 1.98/0.97  bmc1_last_solved_bound:                 -1
% 1.98/0.97  bmc1_unsat_core_size:                   -1
% 1.98/0.97  bmc1_unsat_core_parents_size:           -1
% 1.98/0.97  bmc1_merge_next_fun:                    0
% 1.98/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.98/0.97  
% 1.98/0.97  ------ Instantiation
% 1.98/0.97  
% 1.98/0.97  inst_num_of_clauses:                    314
% 1.98/0.97  inst_num_in_passive:                    14
% 1.98/0.97  inst_num_in_active:                     217
% 1.98/0.97  inst_num_in_unprocessed:                83
% 1.98/0.97  inst_num_of_loops:                      250
% 1.98/0.97  inst_num_of_learning_restarts:          0
% 1.98/0.97  inst_num_moves_active_passive:          29
% 1.98/0.97  inst_lit_activity:                      0
% 1.98/0.97  inst_lit_activity_moves:                0
% 1.98/0.97  inst_num_tautologies:                   0
% 1.98/0.97  inst_num_prop_implied:                  0
% 1.98/0.97  inst_num_existing_simplified:           0
% 1.98/0.97  inst_num_eq_res_simplified:             0
% 1.98/0.97  inst_num_child_elim:                    0
% 1.98/0.97  inst_num_of_dismatching_blockings:      73
% 1.98/0.97  inst_num_of_non_proper_insts:           295
% 1.98/0.97  inst_num_of_duplicates:                 0
% 1.98/0.97  inst_inst_num_from_inst_to_res:         0
% 1.98/0.97  inst_dismatching_checking_time:         0.
% 1.98/0.97  
% 1.98/0.97  ------ Resolution
% 1.98/0.97  
% 1.98/0.97  res_num_of_clauses:                     0
% 1.98/0.97  res_num_in_passive:                     0
% 1.98/0.97  res_num_in_active:                      0
% 1.98/0.97  res_num_of_loops:                       99
% 1.98/0.97  res_forward_subset_subsumed:            19
% 1.98/0.97  res_backward_subset_subsumed:           2
% 1.98/0.97  res_forward_subsumed:                   0
% 1.98/0.97  res_backward_subsumed:                  0
% 1.98/0.97  res_forward_subsumption_resolution:     3
% 1.98/0.97  res_backward_subsumption_resolution:    0
% 1.98/0.97  res_clause_to_clause_subsumption:       344
% 1.98/0.97  res_orphan_elimination:                 0
% 1.98/0.97  res_tautology_del:                      30
% 1.98/0.97  res_num_eq_res_simplified:              0
% 1.98/0.97  res_num_sel_changes:                    0
% 1.98/0.97  res_moves_from_active_to_pass:          0
% 1.98/0.97  
% 1.98/0.97  ------ Superposition
% 1.98/0.97  
% 1.98/0.97  sup_time_total:                         0.
% 1.98/0.97  sup_time_generating:                    0.
% 1.98/0.97  sup_time_sim_full:                      0.
% 1.98/0.97  sup_time_sim_immed:                     0.
% 1.98/0.97  
% 1.98/0.97  sup_num_of_clauses:                     85
% 1.98/0.97  sup_num_in_active:                      49
% 1.98/0.97  sup_num_in_passive:                     36
% 1.98/0.97  sup_num_of_loops:                       48
% 1.98/0.97  sup_fw_superposition:                   42
% 1.98/0.97  sup_bw_superposition:                   49
% 1.98/0.97  sup_immediate_simplified:               16
% 1.98/0.97  sup_given_eliminated:                   0
% 1.98/0.97  comparisons_done:                       0
% 1.98/0.97  comparisons_avoided:                    9
% 1.98/0.97  
% 1.98/0.97  ------ Simplifications
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  sim_fw_subset_subsumed:                 10
% 1.98/0.97  sim_bw_subset_subsumed:                 1
% 1.98/0.97  sim_fw_subsumed:                        3
% 1.98/0.97  sim_bw_subsumed:                        0
% 1.98/0.97  sim_fw_subsumption_res:                 0
% 1.98/0.97  sim_bw_subsumption_res:                 0
% 1.98/0.97  sim_tautology_del:                      6
% 1.98/0.97  sim_eq_tautology_del:                   0
% 1.98/0.97  sim_eq_res_simp:                        0
% 1.98/0.97  sim_fw_demodulated:                     0
% 1.98/0.97  sim_bw_demodulated:                     0
% 1.98/0.97  sim_light_normalised:                   4
% 1.98/0.97  sim_joinable_taut:                      0
% 1.98/0.97  sim_joinable_simp:                      0
% 1.98/0.97  sim_ac_normalised:                      0
% 1.98/0.97  sim_smt_subsumption:                    0
% 1.98/0.97  
%------------------------------------------------------------------------------
