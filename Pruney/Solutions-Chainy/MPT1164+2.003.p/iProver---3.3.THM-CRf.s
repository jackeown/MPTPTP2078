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
% DateTime   : Thu Dec  3 12:12:38 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  158 (3906 expanded)
%              Number of clauses        :  107 ( 959 expanded)
%              Number of leaves         :   16 (1297 expanded)
%              Depth                    :   27
%              Number of atoms          :  822 (26287 expanded)
%              Number of equality atoms :  226 (2049 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & m1_orders_2(X2,X0,X1) )
     => ( ~ r1_tarski(sK4,X1)
        & m1_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( ~ r1_tarski(sK4,sK3)
    & m1_orders_2(sK4,sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f33,f32,f31])).

fof(f57,plain,(
    m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f56,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f28])).

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

fof(f47,plain,(
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

fof(f55,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f53,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

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

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f44])).

fof(f58,plain,(
    ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
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
    inference(equality_resolution,[],[f45])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(nnf_transformation,[],[f17])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f49,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f28])).

cnf(c_17,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1798,plain,
    ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1797,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9,plain,
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
    inference(cnf_transformation,[],[f43])).

cnf(c_12,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_147,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9,c_12])).

cnf(c_19,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_553,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_147,c_19])).

cnf(c_554,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_22,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_558,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_23,c_22,c_21,c_20])).

cnf(c_1793,plain,
    ( k3_orders_2(sK2,X0,sK1(sK2,X0,X1)) = X1
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_558])).

cnf(c_2707,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,X0)) = X0
    | sK3 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1793])).

cnf(c_2740,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) = sK4
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1798,c_2707])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1804,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_652,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_19])).

cnf(c_653,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_652])).

cnf(c_655,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_653,c_23,c_22,c_21,c_20])).

cnf(c_1789,plain,
    ( m1_orders_2(X0,sK2,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_655])).

cnf(c_2002,plain,
    ( m1_orders_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1789])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1800,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3037,plain,
    ( m1_orders_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1800])).

cnf(c_3510,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1798,c_3037])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_481,plain,
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
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_482,plain,
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
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_486,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_23,c_22,c_21,c_20])).

cnf(c_504,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r2_hidden(X1,X0)
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_486,c_5])).

cnf(c_1796,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_2878,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2002,c_1796])).

cnf(c_5299,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
    | m1_orders_2(sK4,sK2,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(sK1(sK2,sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2740,c_2878])).

cnf(c_30,plain,
    ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( ~ r1_tarski(sK4,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1325,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1344,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_1327,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1981,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1327])).

cnf(c_1983,plain,
    ( r1_tarski(sK4,sK3)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_2044,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2063,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_7,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_669,plain,
    ( ~ m1_orders_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_670,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_674,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_670,c_23,c_22,c_21,c_20])).

cnf(c_684,plain,
    ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_674,c_655])).

cnf(c_2214,plain,
    ( ~ m1_orders_2(sK4,sK2,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_2225,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1805,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2497,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_1805])).

cnf(c_2498,plain,
    ( r1_tarski(X0,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2497])).

cnf(c_2500,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2498])).

cnf(c_1331,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1992,plain,
    ( m1_orders_2(X0,X1,X2)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X1 != sK2
    | X2 != sK3
    | X0 != sK4 ),
    inference(instantiation,[status(thm)],[c_1331])).

cnf(c_2062,plain,
    ( m1_orders_2(X0,sK2,X1)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X1 != sK3
    | X0 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_2769,plain,
    ( ~ m1_orders_2(sK4,sK2,sK3)
    | m1_orders_2(sK4,sK2,k1_xboole_0)
    | sK2 != sK2
    | sK4 != sK4
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_1326,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2945,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_2946,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2945])).

cnf(c_2105,plain,
    ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1325])).

cnf(c_2993,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_2527,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1326])).

cnf(c_3162,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2527])).

cnf(c_3163,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_3162])).

cnf(c_2279,plain,
    ( m1_orders_2(X0,sK2,sK3)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | X0 != sK4
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2062])).

cnf(c_3366,plain,
    ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3)
    | ~ m1_orders_2(sK4,sK2,sK3)
    | k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
    | sK2 != sK2
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_3369,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
    | sK2 != sK2
    | sK3 != sK3
    | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
    | m1_orders_2(sK4,sK2,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3366])).

cnf(c_1330,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1986,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_2104,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1986])).

cnf(c_3542,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2104])).

cnf(c_3861,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != sK3
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3542])).

cnf(c_3863,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3861])).

cnf(c_5382,plain,
    ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5299,c_18,c_17,c_30,c_16,c_1344,c_1983,c_2044,c_2063,c_2214,c_2225,c_2500,c_2740,c_2769,c_2946,c_2993,c_3163,c_3369,c_3863])).

cnf(c_5396,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5382,c_2707])).

cnf(c_5427,plain,
    ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5396,c_18,c_17,c_16,c_1344,c_1983,c_2063,c_2214,c_2225,c_2500,c_2769,c_2946,c_2993,c_3163,c_3863])).

cnf(c_14,plain,
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
    inference(cnf_transformation,[],[f49])).

cnf(c_625,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_626,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_630,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_626,c_23,c_22,c_21,c_20])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK2))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
    | r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
    inference(renaming,[status(thm)],[c_630])).

cnf(c_1790,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_5435,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5427,c_1790])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5394,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5382,c_3037])).

cnf(c_5606,plain,
    ( m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5435,c_29,c_5394])).

cnf(c_5615,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3510,c_5606])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f41])).

cnf(c_137,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11,c_12])).

cnf(c_601,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_137,c_19])).

cnf(c_602,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_601])).

cnf(c_606,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_602,c_23,c_22,c_21,c_20])).

cnf(c_1791,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_5617,plain,
    ( sK3 = k1_xboole_0
    | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_5606])).

cnf(c_5675,plain,
    ( r2_hidden(X0,sK3) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5615,c_18,c_29,c_17,c_30,c_16,c_1344,c_1983,c_2044,c_2063,c_2214,c_2225,c_2500,c_2740,c_2769,c_2946,c_2993,c_3163,c_3369,c_3863,c_5617])).

cnf(c_5676,plain,
    ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
    | r2_hidden(X0,sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_5675])).

cnf(c_5683,plain,
    ( r2_hidden(sK0(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),X0),sK3) = iProver_top
    | r1_tarski(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1804,c_5676])).

cnf(c_5886,plain,
    ( r1_tarski(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5683,c_1805])).

cnf(c_6025,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2740,c_5886])).

cnf(c_31,plain,
    ( r1_tarski(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6025,c_3863,c_3163,c_2993,c_2946,c_2769,c_2500,c_2225,c_2214,c_2063,c_1983,c_1344,c_31,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.40/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/0.97  
% 2.40/0.97  ------  iProver source info
% 2.40/0.97  
% 2.40/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.40/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/0.97  git: non_committed_changes: false
% 2.40/0.97  git: last_make_outside_of_git: false
% 2.40/0.97  
% 2.40/0.97  ------ 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options
% 2.40/0.97  
% 2.40/0.97  --out_options                           all
% 2.40/0.97  --tptp_safe_out                         true
% 2.40/0.97  --problem_path                          ""
% 2.40/0.97  --include_path                          ""
% 2.40/0.97  --clausifier                            res/vclausify_rel
% 2.40/0.97  --clausifier_options                    --mode clausify
% 2.40/0.97  --stdin                                 false
% 2.40/0.97  --stats_out                             all
% 2.40/0.97  
% 2.40/0.97  ------ General Options
% 2.40/0.97  
% 2.40/0.97  --fof                                   false
% 2.40/0.97  --time_out_real                         305.
% 2.40/0.97  --time_out_virtual                      -1.
% 2.40/0.97  --symbol_type_check                     false
% 2.40/0.97  --clausify_out                          false
% 2.40/0.97  --sig_cnt_out                           false
% 2.40/0.97  --trig_cnt_out                          false
% 2.40/0.97  --trig_cnt_out_tolerance                1.
% 2.40/0.97  --trig_cnt_out_sk_spl                   false
% 2.40/0.97  --abstr_cl_out                          false
% 2.40/0.97  
% 2.40/0.97  ------ Global Options
% 2.40/0.97  
% 2.40/0.97  --schedule                              default
% 2.40/0.97  --add_important_lit                     false
% 2.40/0.97  --prop_solver_per_cl                    1000
% 2.40/0.97  --min_unsat_core                        false
% 2.40/0.97  --soft_assumptions                      false
% 2.40/0.97  --soft_lemma_size                       3
% 2.40/0.97  --prop_impl_unit_size                   0
% 2.40/0.97  --prop_impl_unit                        []
% 2.40/0.97  --share_sel_clauses                     true
% 2.40/0.97  --reset_solvers                         false
% 2.40/0.97  --bc_imp_inh                            [conj_cone]
% 2.40/0.97  --conj_cone_tolerance                   3.
% 2.40/0.97  --extra_neg_conj                        none
% 2.40/0.97  --large_theory_mode                     true
% 2.40/0.97  --prolific_symb_bound                   200
% 2.40/0.97  --lt_threshold                          2000
% 2.40/0.97  --clause_weak_htbl                      true
% 2.40/0.97  --gc_record_bc_elim                     false
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing Options
% 2.40/0.97  
% 2.40/0.97  --preprocessing_flag                    true
% 2.40/0.97  --time_out_prep_mult                    0.1
% 2.40/0.97  --splitting_mode                        input
% 2.40/0.97  --splitting_grd                         true
% 2.40/0.97  --splitting_cvd                         false
% 2.40/0.97  --splitting_cvd_svl                     false
% 2.40/0.97  --splitting_nvd                         32
% 2.40/0.97  --sub_typing                            true
% 2.40/0.97  --prep_gs_sim                           true
% 2.40/0.97  --prep_unflatten                        true
% 2.40/0.97  --prep_res_sim                          true
% 2.40/0.97  --prep_upred                            true
% 2.40/0.97  --prep_sem_filter                       exhaustive
% 2.40/0.97  --prep_sem_filter_out                   false
% 2.40/0.97  --pred_elim                             true
% 2.40/0.97  --res_sim_input                         true
% 2.40/0.97  --eq_ax_congr_red                       true
% 2.40/0.97  --pure_diseq_elim                       true
% 2.40/0.97  --brand_transform                       false
% 2.40/0.97  --non_eq_to_eq                          false
% 2.40/0.97  --prep_def_merge                        true
% 2.40/0.97  --prep_def_merge_prop_impl              false
% 2.40/0.97  --prep_def_merge_mbd                    true
% 2.40/0.97  --prep_def_merge_tr_red                 false
% 2.40/0.97  --prep_def_merge_tr_cl                  false
% 2.40/0.97  --smt_preprocessing                     true
% 2.40/0.97  --smt_ac_axioms                         fast
% 2.40/0.97  --preprocessed_out                      false
% 2.40/0.97  --preprocessed_stats                    false
% 2.40/0.97  
% 2.40/0.97  ------ Abstraction refinement Options
% 2.40/0.97  
% 2.40/0.97  --abstr_ref                             []
% 2.40/0.97  --abstr_ref_prep                        false
% 2.40/0.97  --abstr_ref_until_sat                   false
% 2.40/0.97  --abstr_ref_sig_restrict                funpre
% 2.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.97  --abstr_ref_under                       []
% 2.40/0.97  
% 2.40/0.97  ------ SAT Options
% 2.40/0.97  
% 2.40/0.97  --sat_mode                              false
% 2.40/0.97  --sat_fm_restart_options                ""
% 2.40/0.97  --sat_gr_def                            false
% 2.40/0.97  --sat_epr_types                         true
% 2.40/0.97  --sat_non_cyclic_types                  false
% 2.40/0.97  --sat_finite_models                     false
% 2.40/0.97  --sat_fm_lemmas                         false
% 2.40/0.97  --sat_fm_prep                           false
% 2.40/0.97  --sat_fm_uc_incr                        true
% 2.40/0.97  --sat_out_model                         small
% 2.40/0.97  --sat_out_clauses                       false
% 2.40/0.97  
% 2.40/0.97  ------ QBF Options
% 2.40/0.97  
% 2.40/0.97  --qbf_mode                              false
% 2.40/0.97  --qbf_elim_univ                         false
% 2.40/0.97  --qbf_dom_inst                          none
% 2.40/0.97  --qbf_dom_pre_inst                      false
% 2.40/0.97  --qbf_sk_in                             false
% 2.40/0.97  --qbf_pred_elim                         true
% 2.40/0.97  --qbf_split                             512
% 2.40/0.97  
% 2.40/0.97  ------ BMC1 Options
% 2.40/0.97  
% 2.40/0.97  --bmc1_incremental                      false
% 2.40/0.97  --bmc1_axioms                           reachable_all
% 2.40/0.97  --bmc1_min_bound                        0
% 2.40/0.97  --bmc1_max_bound                        -1
% 2.40/0.97  --bmc1_max_bound_default                -1
% 2.40/0.97  --bmc1_symbol_reachability              true
% 2.40/0.97  --bmc1_property_lemmas                  false
% 2.40/0.97  --bmc1_k_induction                      false
% 2.40/0.97  --bmc1_non_equiv_states                 false
% 2.40/0.97  --bmc1_deadlock                         false
% 2.40/0.97  --bmc1_ucm                              false
% 2.40/0.97  --bmc1_add_unsat_core                   none
% 2.40/0.97  --bmc1_unsat_core_children              false
% 2.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.97  --bmc1_out_stat                         full
% 2.40/0.97  --bmc1_ground_init                      false
% 2.40/0.97  --bmc1_pre_inst_next_state              false
% 2.40/0.97  --bmc1_pre_inst_state                   false
% 2.40/0.97  --bmc1_pre_inst_reach_state             false
% 2.40/0.97  --bmc1_out_unsat_core                   false
% 2.40/0.97  --bmc1_aig_witness_out                  false
% 2.40/0.97  --bmc1_verbose                          false
% 2.40/0.97  --bmc1_dump_clauses_tptp                false
% 2.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.97  --bmc1_dump_file                        -
% 2.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.97  --bmc1_ucm_extend_mode                  1
% 2.40/0.97  --bmc1_ucm_init_mode                    2
% 2.40/0.97  --bmc1_ucm_cone_mode                    none
% 2.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.97  --bmc1_ucm_relax_model                  4
% 2.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.97  --bmc1_ucm_layered_model                none
% 2.40/0.97  --bmc1_ucm_max_lemma_size               10
% 2.40/0.97  
% 2.40/0.97  ------ AIG Options
% 2.40/0.97  
% 2.40/0.97  --aig_mode                              false
% 2.40/0.97  
% 2.40/0.97  ------ Instantiation Options
% 2.40/0.97  
% 2.40/0.97  --instantiation_flag                    true
% 2.40/0.97  --inst_sos_flag                         false
% 2.40/0.97  --inst_sos_phase                        true
% 2.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel_side                     num_symb
% 2.40/0.97  --inst_solver_per_active                1400
% 2.40/0.97  --inst_solver_calls_frac                1.
% 2.40/0.97  --inst_passive_queue_type               priority_queues
% 2.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.97  --inst_passive_queues_freq              [25;2]
% 2.40/0.97  --inst_dismatching                      true
% 2.40/0.97  --inst_eager_unprocessed_to_passive     true
% 2.40/0.97  --inst_prop_sim_given                   true
% 2.40/0.97  --inst_prop_sim_new                     false
% 2.40/0.97  --inst_subs_new                         false
% 2.40/0.97  --inst_eq_res_simp                      false
% 2.40/0.97  --inst_subs_given                       false
% 2.40/0.97  --inst_orphan_elimination               true
% 2.40/0.97  --inst_learning_loop_flag               true
% 2.40/0.97  --inst_learning_start                   3000
% 2.40/0.97  --inst_learning_factor                  2
% 2.40/0.97  --inst_start_prop_sim_after_learn       3
% 2.40/0.97  --inst_sel_renew                        solver
% 2.40/0.97  --inst_lit_activity_flag                true
% 2.40/0.97  --inst_restr_to_given                   false
% 2.40/0.97  --inst_activity_threshold               500
% 2.40/0.97  --inst_out_proof                        true
% 2.40/0.97  
% 2.40/0.97  ------ Resolution Options
% 2.40/0.97  
% 2.40/0.97  --resolution_flag                       true
% 2.40/0.97  --res_lit_sel                           adaptive
% 2.40/0.97  --res_lit_sel_side                      none
% 2.40/0.97  --res_ordering                          kbo
% 2.40/0.97  --res_to_prop_solver                    active
% 2.40/0.97  --res_prop_simpl_new                    false
% 2.40/0.97  --res_prop_simpl_given                  true
% 2.40/0.97  --res_passive_queue_type                priority_queues
% 2.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.97  --res_passive_queues_freq               [15;5]
% 2.40/0.97  --res_forward_subs                      full
% 2.40/0.97  --res_backward_subs                     full
% 2.40/0.97  --res_forward_subs_resolution           true
% 2.40/0.97  --res_backward_subs_resolution          true
% 2.40/0.97  --res_orphan_elimination                true
% 2.40/0.97  --res_time_limit                        2.
% 2.40/0.97  --res_out_proof                         true
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Options
% 2.40/0.97  
% 2.40/0.97  --superposition_flag                    true
% 2.40/0.97  --sup_passive_queue_type                priority_queues
% 2.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.97  --demod_completeness_check              fast
% 2.40/0.97  --demod_use_ground                      true
% 2.40/0.97  --sup_to_prop_solver                    passive
% 2.40/0.97  --sup_prop_simpl_new                    true
% 2.40/0.97  --sup_prop_simpl_given                  true
% 2.40/0.97  --sup_fun_splitting                     false
% 2.40/0.97  --sup_smt_interval                      50000
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Simplification Setup
% 2.40/0.97  
% 2.40/0.97  --sup_indices_passive                   []
% 2.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_full_bw                           [BwDemod]
% 2.40/0.97  --sup_immed_triv                        [TrivRules]
% 2.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_immed_bw_main                     []
% 2.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  
% 2.40/0.97  ------ Combination Options
% 2.40/0.97  
% 2.40/0.97  --comb_res_mult                         3
% 2.40/0.97  --comb_sup_mult                         2
% 2.40/0.97  --comb_inst_mult                        10
% 2.40/0.97  
% 2.40/0.97  ------ Debug Options
% 2.40/0.97  
% 2.40/0.97  --dbg_backtrace                         false
% 2.40/0.97  --dbg_dump_prop_clauses                 false
% 2.40/0.97  --dbg_dump_prop_clauses_file            -
% 2.40/0.97  --dbg_out_stat                          false
% 2.40/0.97  ------ Parsing...
% 2.40/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/0.97  ------ Proving...
% 2.40/0.97  ------ Problem Properties 
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  clauses                                 18
% 2.40/0.97  conjectures                             3
% 2.40/0.97  EPR                                     3
% 2.40/0.97  Horn                                    13
% 2.40/0.97  unary                                   3
% 2.40/0.97  binary                                  5
% 2.40/0.97  lits                                    53
% 2.40/0.97  lits eq                                 6
% 2.40/0.97  fd_pure                                 0
% 2.40/0.97  fd_pseudo                               0
% 2.40/0.97  fd_cond                                 4
% 2.40/0.97  fd_pseudo_cond                          0
% 2.40/0.97  AC symbols                              0
% 2.40/0.97  
% 2.40/0.97  ------ Schedule dynamic 5 is on 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  ------ 
% 2.40/0.97  Current options:
% 2.40/0.97  ------ 
% 2.40/0.97  
% 2.40/0.97  ------ Input Options
% 2.40/0.97  
% 2.40/0.97  --out_options                           all
% 2.40/0.97  --tptp_safe_out                         true
% 2.40/0.97  --problem_path                          ""
% 2.40/0.97  --include_path                          ""
% 2.40/0.97  --clausifier                            res/vclausify_rel
% 2.40/0.97  --clausifier_options                    --mode clausify
% 2.40/0.97  --stdin                                 false
% 2.40/0.97  --stats_out                             all
% 2.40/0.97  
% 2.40/0.97  ------ General Options
% 2.40/0.97  
% 2.40/0.97  --fof                                   false
% 2.40/0.97  --time_out_real                         305.
% 2.40/0.97  --time_out_virtual                      -1.
% 2.40/0.97  --symbol_type_check                     false
% 2.40/0.97  --clausify_out                          false
% 2.40/0.97  --sig_cnt_out                           false
% 2.40/0.97  --trig_cnt_out                          false
% 2.40/0.97  --trig_cnt_out_tolerance                1.
% 2.40/0.97  --trig_cnt_out_sk_spl                   false
% 2.40/0.97  --abstr_cl_out                          false
% 2.40/0.97  
% 2.40/0.97  ------ Global Options
% 2.40/0.97  
% 2.40/0.97  --schedule                              default
% 2.40/0.97  --add_important_lit                     false
% 2.40/0.97  --prop_solver_per_cl                    1000
% 2.40/0.97  --min_unsat_core                        false
% 2.40/0.97  --soft_assumptions                      false
% 2.40/0.97  --soft_lemma_size                       3
% 2.40/0.97  --prop_impl_unit_size                   0
% 2.40/0.97  --prop_impl_unit                        []
% 2.40/0.97  --share_sel_clauses                     true
% 2.40/0.97  --reset_solvers                         false
% 2.40/0.97  --bc_imp_inh                            [conj_cone]
% 2.40/0.97  --conj_cone_tolerance                   3.
% 2.40/0.97  --extra_neg_conj                        none
% 2.40/0.97  --large_theory_mode                     true
% 2.40/0.97  --prolific_symb_bound                   200
% 2.40/0.97  --lt_threshold                          2000
% 2.40/0.97  --clause_weak_htbl                      true
% 2.40/0.97  --gc_record_bc_elim                     false
% 2.40/0.97  
% 2.40/0.97  ------ Preprocessing Options
% 2.40/0.97  
% 2.40/0.97  --preprocessing_flag                    true
% 2.40/0.97  --time_out_prep_mult                    0.1
% 2.40/0.97  --splitting_mode                        input
% 2.40/0.97  --splitting_grd                         true
% 2.40/0.97  --splitting_cvd                         false
% 2.40/0.97  --splitting_cvd_svl                     false
% 2.40/0.97  --splitting_nvd                         32
% 2.40/0.97  --sub_typing                            true
% 2.40/0.97  --prep_gs_sim                           true
% 2.40/0.97  --prep_unflatten                        true
% 2.40/0.97  --prep_res_sim                          true
% 2.40/0.97  --prep_upred                            true
% 2.40/0.97  --prep_sem_filter                       exhaustive
% 2.40/0.97  --prep_sem_filter_out                   false
% 2.40/0.97  --pred_elim                             true
% 2.40/0.97  --res_sim_input                         true
% 2.40/0.97  --eq_ax_congr_red                       true
% 2.40/0.97  --pure_diseq_elim                       true
% 2.40/0.97  --brand_transform                       false
% 2.40/0.97  --non_eq_to_eq                          false
% 2.40/0.97  --prep_def_merge                        true
% 2.40/0.97  --prep_def_merge_prop_impl              false
% 2.40/0.97  --prep_def_merge_mbd                    true
% 2.40/0.97  --prep_def_merge_tr_red                 false
% 2.40/0.97  --prep_def_merge_tr_cl                  false
% 2.40/0.97  --smt_preprocessing                     true
% 2.40/0.97  --smt_ac_axioms                         fast
% 2.40/0.97  --preprocessed_out                      false
% 2.40/0.97  --preprocessed_stats                    false
% 2.40/0.97  
% 2.40/0.97  ------ Abstraction refinement Options
% 2.40/0.97  
% 2.40/0.97  --abstr_ref                             []
% 2.40/0.97  --abstr_ref_prep                        false
% 2.40/0.97  --abstr_ref_until_sat                   false
% 2.40/0.97  --abstr_ref_sig_restrict                funpre
% 2.40/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/0.97  --abstr_ref_under                       []
% 2.40/0.97  
% 2.40/0.97  ------ SAT Options
% 2.40/0.97  
% 2.40/0.97  --sat_mode                              false
% 2.40/0.97  --sat_fm_restart_options                ""
% 2.40/0.97  --sat_gr_def                            false
% 2.40/0.97  --sat_epr_types                         true
% 2.40/0.97  --sat_non_cyclic_types                  false
% 2.40/0.97  --sat_finite_models                     false
% 2.40/0.97  --sat_fm_lemmas                         false
% 2.40/0.97  --sat_fm_prep                           false
% 2.40/0.97  --sat_fm_uc_incr                        true
% 2.40/0.97  --sat_out_model                         small
% 2.40/0.97  --sat_out_clauses                       false
% 2.40/0.97  
% 2.40/0.97  ------ QBF Options
% 2.40/0.97  
% 2.40/0.97  --qbf_mode                              false
% 2.40/0.97  --qbf_elim_univ                         false
% 2.40/0.97  --qbf_dom_inst                          none
% 2.40/0.97  --qbf_dom_pre_inst                      false
% 2.40/0.97  --qbf_sk_in                             false
% 2.40/0.97  --qbf_pred_elim                         true
% 2.40/0.97  --qbf_split                             512
% 2.40/0.97  
% 2.40/0.97  ------ BMC1 Options
% 2.40/0.97  
% 2.40/0.97  --bmc1_incremental                      false
% 2.40/0.97  --bmc1_axioms                           reachable_all
% 2.40/0.97  --bmc1_min_bound                        0
% 2.40/0.97  --bmc1_max_bound                        -1
% 2.40/0.97  --bmc1_max_bound_default                -1
% 2.40/0.97  --bmc1_symbol_reachability              true
% 2.40/0.97  --bmc1_property_lemmas                  false
% 2.40/0.97  --bmc1_k_induction                      false
% 2.40/0.97  --bmc1_non_equiv_states                 false
% 2.40/0.97  --bmc1_deadlock                         false
% 2.40/0.97  --bmc1_ucm                              false
% 2.40/0.97  --bmc1_add_unsat_core                   none
% 2.40/0.97  --bmc1_unsat_core_children              false
% 2.40/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/0.97  --bmc1_out_stat                         full
% 2.40/0.97  --bmc1_ground_init                      false
% 2.40/0.97  --bmc1_pre_inst_next_state              false
% 2.40/0.97  --bmc1_pre_inst_state                   false
% 2.40/0.97  --bmc1_pre_inst_reach_state             false
% 2.40/0.97  --bmc1_out_unsat_core                   false
% 2.40/0.97  --bmc1_aig_witness_out                  false
% 2.40/0.97  --bmc1_verbose                          false
% 2.40/0.97  --bmc1_dump_clauses_tptp                false
% 2.40/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.40/0.97  --bmc1_dump_file                        -
% 2.40/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.40/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.40/0.97  --bmc1_ucm_extend_mode                  1
% 2.40/0.97  --bmc1_ucm_init_mode                    2
% 2.40/0.97  --bmc1_ucm_cone_mode                    none
% 2.40/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.40/0.97  --bmc1_ucm_relax_model                  4
% 2.40/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.40/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/0.97  --bmc1_ucm_layered_model                none
% 2.40/0.97  --bmc1_ucm_max_lemma_size               10
% 2.40/0.97  
% 2.40/0.97  ------ AIG Options
% 2.40/0.97  
% 2.40/0.97  --aig_mode                              false
% 2.40/0.97  
% 2.40/0.97  ------ Instantiation Options
% 2.40/0.97  
% 2.40/0.97  --instantiation_flag                    true
% 2.40/0.97  --inst_sos_flag                         false
% 2.40/0.97  --inst_sos_phase                        true
% 2.40/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/0.97  --inst_lit_sel_side                     none
% 2.40/0.97  --inst_solver_per_active                1400
% 2.40/0.97  --inst_solver_calls_frac                1.
% 2.40/0.97  --inst_passive_queue_type               priority_queues
% 2.40/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/0.97  --inst_passive_queues_freq              [25;2]
% 2.40/0.97  --inst_dismatching                      true
% 2.40/0.97  --inst_eager_unprocessed_to_passive     true
% 2.40/0.97  --inst_prop_sim_given                   true
% 2.40/0.97  --inst_prop_sim_new                     false
% 2.40/0.97  --inst_subs_new                         false
% 2.40/0.97  --inst_eq_res_simp                      false
% 2.40/0.97  --inst_subs_given                       false
% 2.40/0.97  --inst_orphan_elimination               true
% 2.40/0.97  --inst_learning_loop_flag               true
% 2.40/0.97  --inst_learning_start                   3000
% 2.40/0.97  --inst_learning_factor                  2
% 2.40/0.97  --inst_start_prop_sim_after_learn       3
% 2.40/0.97  --inst_sel_renew                        solver
% 2.40/0.97  --inst_lit_activity_flag                true
% 2.40/0.97  --inst_restr_to_given                   false
% 2.40/0.97  --inst_activity_threshold               500
% 2.40/0.97  --inst_out_proof                        true
% 2.40/0.97  
% 2.40/0.97  ------ Resolution Options
% 2.40/0.97  
% 2.40/0.97  --resolution_flag                       false
% 2.40/0.97  --res_lit_sel                           adaptive
% 2.40/0.97  --res_lit_sel_side                      none
% 2.40/0.97  --res_ordering                          kbo
% 2.40/0.97  --res_to_prop_solver                    active
% 2.40/0.97  --res_prop_simpl_new                    false
% 2.40/0.97  --res_prop_simpl_given                  true
% 2.40/0.97  --res_passive_queue_type                priority_queues
% 2.40/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/0.97  --res_passive_queues_freq               [15;5]
% 2.40/0.97  --res_forward_subs                      full
% 2.40/0.97  --res_backward_subs                     full
% 2.40/0.97  --res_forward_subs_resolution           true
% 2.40/0.97  --res_backward_subs_resolution          true
% 2.40/0.97  --res_orphan_elimination                true
% 2.40/0.97  --res_time_limit                        2.
% 2.40/0.97  --res_out_proof                         true
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Options
% 2.40/0.97  
% 2.40/0.97  --superposition_flag                    true
% 2.40/0.97  --sup_passive_queue_type                priority_queues
% 2.40/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.40/0.97  --demod_completeness_check              fast
% 2.40/0.97  --demod_use_ground                      true
% 2.40/0.97  --sup_to_prop_solver                    passive
% 2.40/0.97  --sup_prop_simpl_new                    true
% 2.40/0.97  --sup_prop_simpl_given                  true
% 2.40/0.97  --sup_fun_splitting                     false
% 2.40/0.97  --sup_smt_interval                      50000
% 2.40/0.97  
% 2.40/0.97  ------ Superposition Simplification Setup
% 2.40/0.97  
% 2.40/0.97  --sup_indices_passive                   []
% 2.40/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_full_bw                           [BwDemod]
% 2.40/0.97  --sup_immed_triv                        [TrivRules]
% 2.40/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_immed_bw_main                     []
% 2.40/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/0.97  
% 2.40/0.97  ------ Combination Options
% 2.40/0.97  
% 2.40/0.97  --comb_res_mult                         3
% 2.40/0.97  --comb_sup_mult                         2
% 2.40/0.97  --comb_inst_mult                        10
% 2.40/0.97  
% 2.40/0.97  ------ Debug Options
% 2.40/0.97  
% 2.40/0.97  --dbg_backtrace                         false
% 2.40/0.97  --dbg_dump_prop_clauses                 false
% 2.40/0.97  --dbg_dump_prop_clauses_file            -
% 2.40/0.97  --dbg_out_stat                          false
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  ------ Proving...
% 2.40/0.97  
% 2.40/0.97  
% 2.40/0.97  % SZS status Theorem for theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/0.97  
% 2.40/0.97  fof(f7,conjecture,(
% 2.40/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f8,negated_conjecture,(
% 2.40/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 2.40/0.97    inference(negated_conjecture,[],[f7])).
% 2.40/0.97  
% 2.40/0.97  fof(f18,plain,(
% 2.40/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f8])).
% 2.40/0.97  
% 2.40/0.97  fof(f19,plain,(
% 2.40/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.40/0.97    inference(flattening,[],[f18])).
% 2.40/0.97  
% 2.40/0.97  fof(f33,plain,(
% 2.40/0.97    ( ! [X0,X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) => (~r1_tarski(sK4,X1) & m1_orders_2(sK4,X0,X1))) )),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f32,plain,(
% 2.40/0.97    ( ! [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (~r1_tarski(X2,sK3) & m1_orders_2(X2,X0,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f31,plain,(
% 2.40/0.97    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (~r1_tarski(X2,X1) & m1_orders_2(X2,sK2,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f34,plain,(
% 2.40/0.97    ((~r1_tarski(sK4,sK3) & m1_orders_2(sK4,sK2,sK3)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f33,f32,f31])).
% 2.40/0.97  
% 2.40/0.97  fof(f57,plain,(
% 2.40/0.97    m1_orders_2(sK4,sK2,sK3)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f56,plain,(
% 2.40/0.97    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f4,axiom,(
% 2.40/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f12,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f4])).
% 2.40/0.97  
% 2.40/0.97  fof(f13,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(flattening,[],[f12])).
% 2.40/0.97  
% 2.40/0.97  fof(f25,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(nnf_transformation,[],[f13])).
% 2.40/0.97  
% 2.40/0.97  fof(f26,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(rectify,[],[f25])).
% 2.40/0.97  
% 2.40/0.97  fof(f27,plain,(
% 2.40/0.97    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f28,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.40/0.97  
% 2.40/0.97  fof(f43,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK1(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f28])).
% 2.40/0.97  
% 2.40/0.97  fof(f5,axiom,(
% 2.40/0.97    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f14,plain,(
% 2.40/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f5])).
% 2.40/0.97  
% 2.40/0.97  fof(f15,plain,(
% 2.40/0.97    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(flattening,[],[f14])).
% 2.40/0.97  
% 2.40/0.97  fof(f47,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f15])).
% 2.40/0.97  
% 2.40/0.97  fof(f55,plain,(
% 2.40/0.97    l1_orders_2(sK2)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f51,plain,(
% 2.40/0.97    ~v2_struct_0(sK2)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f52,plain,(
% 2.40/0.97    v3_orders_2(sK2)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f53,plain,(
% 2.40/0.97    v4_orders_2(sK2)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f54,plain,(
% 2.40/0.97    v5_orders_2(sK2)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f1,axiom,(
% 2.40/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f9,plain,(
% 2.40/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f1])).
% 2.40/0.97  
% 2.40/0.97  fof(f20,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(nnf_transformation,[],[f9])).
% 2.40/0.97  
% 2.40/0.97  fof(f21,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(rectify,[],[f20])).
% 2.40/0.97  
% 2.40/0.97  fof(f22,plain,(
% 2.40/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.40/0.97    introduced(choice_axiom,[])).
% 2.40/0.97  
% 2.40/0.97  fof(f23,plain,(
% 2.40/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.40/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.40/0.97  
% 2.40/0.97  fof(f36,plain,(
% 2.40/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f23])).
% 2.40/0.97  
% 2.40/0.97  fof(f3,axiom,(
% 2.40/0.97    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f10,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.40/0.97    inference(ennf_transformation,[],[f3])).
% 2.40/0.97  
% 2.40/0.97  fof(f11,plain,(
% 2.40/0.97    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.40/0.97    inference(flattening,[],[f10])).
% 2.40/0.97  
% 2.40/0.97  fof(f40,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f11])).
% 2.40/0.97  
% 2.40/0.97  fof(f44,plain,(
% 2.40/0.97    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X1) | k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f28])).
% 2.40/0.97  
% 2.40/0.97  fof(f62,plain,(
% 2.40/0.97    ( ! [X0,X3,X1] : (m1_orders_2(k3_orders_2(X0,X1,X3),X0,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(k3_orders_2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(equality_resolution,[],[f44])).
% 2.40/0.97  
% 2.40/0.97  fof(f58,plain,(
% 2.40/0.97    ~r1_tarski(sK4,sK3)),
% 2.40/0.97    inference(cnf_transformation,[],[f34])).
% 2.40/0.97  
% 2.40/0.97  fof(f45,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f28])).
% 2.40/0.97  
% 2.40/0.97  fof(f61,plain,(
% 2.40/0.97    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(equality_resolution,[],[f45])).
% 2.40/0.97  
% 2.40/0.97  fof(f37,plain,(
% 2.40/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f23])).
% 2.40/0.97  
% 2.40/0.97  fof(f6,axiom,(
% 2.40/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.40/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/0.97  
% 2.40/0.97  fof(f16,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.40/0.97    inference(ennf_transformation,[],[f6])).
% 2.40/0.97  
% 2.40/0.97  fof(f17,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(flattening,[],[f16])).
% 2.40/0.97  
% 2.40/0.97  fof(f29,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(nnf_transformation,[],[f17])).
% 2.40/0.97  
% 2.40/0.97  fof(f30,plain,(
% 2.40/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.40/0.97    inference(flattening,[],[f29])).
% 2.40/0.97  
% 2.40/0.97  fof(f49,plain,(
% 2.40/0.97    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f30])).
% 2.40/0.97  
% 2.40/0.97  fof(f41,plain,(
% 2.40/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.40/0.97    inference(cnf_transformation,[],[f28])).
% 2.40/0.97  
% 2.40/0.97  cnf(c_17,negated_conjecture,
% 2.40/0.97      ( m1_orders_2(sK4,sK2,sK3) ),
% 2.40/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1798,plain,
% 2.40/0.97      ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_18,negated_conjecture,
% 2.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1797,plain,
% 2.40/0.97      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_9,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | ~ l1_orders_2(X1)
% 2.40/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 2.40/0.97      | k1_xboole_0 = X2 ),
% 2.40/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_12,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | ~ l1_orders_2(X1) ),
% 2.40/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_147,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | ~ l1_orders_2(X1)
% 2.40/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 2.40/0.97      | k1_xboole_0 = X2 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_9,c_12]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_19,negated_conjecture,
% 2.40/0.97      ( l1_orders_2(sK2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_553,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | k3_orders_2(X1,X2,sK1(X1,X2,X0)) = X0
% 2.40/0.97      | sK2 != X1
% 2.40/0.97      | k1_xboole_0 = X2 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_147,c_19]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_554,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | v2_struct_0(sK2)
% 2.40/0.97      | ~ v3_orders_2(sK2)
% 2.40/0.97      | ~ v4_orders_2(sK2)
% 2.40/0.97      | ~ v5_orders_2(sK2)
% 2.40/0.97      | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
% 2.40/0.97      | k1_xboole_0 = X1 ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_553]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_23,negated_conjecture,
% 2.40/0.97      ( ~ v2_struct_0(sK2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f51]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_22,negated_conjecture,
% 2.40/0.97      ( v3_orders_2(sK2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f52]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_21,negated_conjecture,
% 2.40/0.97      ( v4_orders_2(sK2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_20,negated_conjecture,
% 2.40/0.97      ( v5_orders_2(sK2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_558,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | k3_orders_2(sK2,X1,sK1(sK2,X1,X0)) = X0
% 2.40/0.97      | k1_xboole_0 = X1 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_554,c_23,c_22,c_21,c_20]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1793,plain,
% 2.40/0.97      ( k3_orders_2(sK2,X0,sK1(sK2,X0,X1)) = X1
% 2.40/0.97      | k1_xboole_0 = X0
% 2.40/0.97      | m1_orders_2(X1,sK2,X0) != iProver_top
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_558]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2707,plain,
% 2.40/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,X0)) = X0
% 2.40/0.97      | sK3 = k1_xboole_0
% 2.40/0.97      | m1_orders_2(X0,sK2,sK3) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1797,c_1793]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2740,plain,
% 2.40/0.97      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) = sK4 | sK3 = k1_xboole_0 ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1798,c_2707]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1,plain,
% 2.40/0.97      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.40/0.97      inference(cnf_transformation,[],[f36]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1804,plain,
% 2.40/0.97      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.40/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_652,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | sK2 != X1 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_12,c_19]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_653,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | v2_struct_0(sK2)
% 2.40/0.97      | ~ v3_orders_2(sK2)
% 2.40/0.97      | ~ v4_orders_2(sK2)
% 2.40/0.97      | ~ v5_orders_2(sK2) ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_652]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_655,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_653,c_23,c_22,c_21,c_20]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1789,plain,
% 2.40/0.97      ( m1_orders_2(X0,sK2,X1) != iProver_top
% 2.40/0.97      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_655]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2002,plain,
% 2.40/0.97      ( m1_orders_2(X0,sK2,sK3) != iProver_top
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1797,c_1789]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_5,plain,
% 2.40/0.97      ( m1_subset_1(X0,X1)
% 2.40/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/0.97      | ~ r2_hidden(X0,X2) ),
% 2.40/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1800,plain,
% 2.40/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 2.40/0.97      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.40/0.97      | r2_hidden(X0,X2) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3037,plain,
% 2.40/0.97      ( m1_orders_2(X0,sK2,sK3) != iProver_top
% 2.40/0.97      | m1_subset_1(X1,u1_struct_0(sK2)) = iProver_top
% 2.40/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_2002,c_1800]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_3510,plain,
% 2.40/0.97      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 2.40/0.97      | r2_hidden(X0,sK4) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_1798,c_3037]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_8,plain,
% 2.40/0.97      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 2.40/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.97      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.97      | ~ r2_hidden(X2,X1)
% 2.40/0.97      | v2_struct_0(X0)
% 2.40/0.97      | ~ v3_orders_2(X0)
% 2.40/0.97      | ~ v4_orders_2(X0)
% 2.40/0.97      | ~ v5_orders_2(X0)
% 2.40/0.97      | ~ l1_orders_2(X0)
% 2.40/0.97      | k1_xboole_0 = X1 ),
% 2.40/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_481,plain,
% 2.40/0.97      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 2.40/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.40/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.97      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/0.97      | ~ r2_hidden(X2,X1)
% 2.40/0.97      | v2_struct_0(X0)
% 2.40/0.97      | ~ v3_orders_2(X0)
% 2.40/0.97      | ~ v4_orders_2(X0)
% 2.40/0.97      | ~ v5_orders_2(X0)
% 2.40/0.97      | sK2 != X0
% 2.40/0.97      | k1_xboole_0 = X1 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_482,plain,
% 2.40/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 2.40/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ r2_hidden(X1,X0)
% 2.40/0.97      | v2_struct_0(sK2)
% 2.40/0.97      | ~ v3_orders_2(sK2)
% 2.40/0.97      | ~ v4_orders_2(sK2)
% 2.40/0.97      | ~ v5_orders_2(sK2)
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_481]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_486,plain,
% 2.40/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 2.40/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ r2_hidden(X1,X0)
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_482,c_23,c_22,c_21,c_20]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_504,plain,
% 2.40/0.97      ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ r2_hidden(X1,X0)
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_486,c_5]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1796,plain,
% 2.40/0.97      ( k1_xboole_0 = X0
% 2.40/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.97      | m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2878,plain,
% 2.40/0.97      ( k1_xboole_0 = X0
% 2.40/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
% 2.40/0.97      | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,sK3) != iProver_top
% 2.40/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.97      | r2_hidden(X1,X0) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_2002,c_1796]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_5299,plain,
% 2.40/0.97      ( sK3 = k1_xboole_0
% 2.40/0.97      | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
% 2.40/0.97      | m1_orders_2(sK4,sK2,sK3) != iProver_top
% 2.40/0.97      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.97      | r2_hidden(sK1(sK2,sK3,sK4),sK3) != iProver_top ),
% 2.40/0.97      inference(superposition,[status(thm)],[c_2740,c_2878]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_30,plain,
% 2.40/0.97      ( m1_orders_2(sK4,sK2,sK3) = iProver_top ),
% 2.40/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_16,negated_conjecture,
% 2.40/0.97      ( ~ r1_tarski(sK4,sK3) ),
% 2.40/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1325,plain,( X0 = X0 ),theory(equality) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1344,plain,
% 2.40/0.97      ( k1_xboole_0 = k1_xboole_0 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1327,plain,
% 2.40/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.97      theory(equality) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1981,plain,
% 2.40/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1327]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_1983,plain,
% 2.40/0.97      ( r1_tarski(sK4,sK3)
% 2.40/0.97      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.40/0.97      | sK3 != k1_xboole_0
% 2.40/0.97      | sK4 != k1_xboole_0 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1981]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2044,plain,
% 2.40/0.97      ( sK3 = sK3 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_2063,plain,
% 2.40/0.97      ( sK2 = sK2 ),
% 2.40/0.97      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_7,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | ~ l1_orders_2(X1)
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(cnf_transformation,[],[f61]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_669,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,X1,k1_xboole_0)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.97      | v2_struct_0(X1)
% 2.40/0.97      | ~ v3_orders_2(X1)
% 2.40/0.97      | ~ v4_orders_2(X1)
% 2.40/0.97      | ~ v5_orders_2(X1)
% 2.40/0.97      | sK2 != X1
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_670,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | v2_struct_0(sK2)
% 2.40/0.97      | ~ v3_orders_2(sK2)
% 2.40/0.97      | ~ v4_orders_2(sK2)
% 2.40/0.97      | ~ v5_orders_2(sK2)
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(unflattening,[status(thm)],[c_669]) ).
% 2.40/0.97  
% 2.40/0.97  cnf(c_674,plain,
% 2.40/0.97      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 2.40/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.97      | k1_xboole_0 = X0 ),
% 2.40/0.97      inference(global_propositional_subsumption,
% 2.40/0.97                [status(thm)],
% 2.40/0.97                [c_670,c_23,c_22,c_21,c_20]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_684,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,sK2,k1_xboole_0)
% 2.40/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | k1_xboole_0 = X0 ),
% 2.40/0.98      inference(forward_subsumption_resolution,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_674,c_655]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2214,plain,
% 2.40/0.98      ( ~ m1_orders_2(sK4,sK2,k1_xboole_0)
% 2.40/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | k1_xboole_0 = sK4 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_684]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2225,plain,
% 2.40/0.98      ( sK4 = sK4 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_0,plain,
% 2.40/0.98      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f37]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1805,plain,
% 2.40/0.98      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.40/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2497,plain,
% 2.40/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1804,c_1805]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2498,plain,
% 2.40/0.98      ( r1_tarski(X0,X0) ),
% 2.40/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_2497]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2500,plain,
% 2.40/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2498]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1331,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.98      | m1_orders_2(X3,X4,X5)
% 2.40/0.98      | X3 != X0
% 2.40/0.98      | X4 != X1
% 2.40/0.98      | X5 != X2 ),
% 2.40/0.98      theory(equality) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1992,plain,
% 2.40/0.98      ( m1_orders_2(X0,X1,X2)
% 2.40/0.98      | ~ m1_orders_2(sK4,sK2,sK3)
% 2.40/0.98      | X1 != sK2
% 2.40/0.98      | X2 != sK3
% 2.40/0.98      | X0 != sK4 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1331]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2062,plain,
% 2.40/0.98      ( m1_orders_2(X0,sK2,X1)
% 2.40/0.98      | ~ m1_orders_2(sK4,sK2,sK3)
% 2.40/0.98      | X1 != sK3
% 2.40/0.98      | X0 != sK4
% 2.40/0.98      | sK2 != sK2 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1992]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2769,plain,
% 2.40/0.98      ( ~ m1_orders_2(sK4,sK2,sK3)
% 2.40/0.98      | m1_orders_2(sK4,sK2,k1_xboole_0)
% 2.40/0.98      | sK2 != sK2
% 2.40/0.98      | sK4 != sK4
% 2.40/0.98      | k1_xboole_0 != sK3 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2062]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1326,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2945,plain,
% 2.40/0.98      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2946,plain,
% 2.40/0.98      ( sK3 != k1_xboole_0
% 2.40/0.98      | k1_xboole_0 = sK3
% 2.40/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2945]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2105,plain,
% 2.40/0.98      ( k1_zfmisc_1(X0) = k1_zfmisc_1(X0) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1325]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2993,plain,
% 2.40/0.98      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2105]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2527,plain,
% 2.40/0.98      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1326]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3162,plain,
% 2.40/0.98      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2527]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3163,plain,
% 2.40/0.98      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_3162]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2279,plain,
% 2.40/0.98      ( m1_orders_2(X0,sK2,sK3)
% 2.40/0.98      | ~ m1_orders_2(sK4,sK2,sK3)
% 2.40/0.98      | X0 != sK4
% 2.40/0.98      | sK2 != sK2
% 2.40/0.98      | sK3 != sK3 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2062]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3366,plain,
% 2.40/0.98      ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3)
% 2.40/0.98      | ~ m1_orders_2(sK4,sK2,sK3)
% 2.40/0.98      | k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
% 2.40/0.98      | sK2 != sK2
% 2.40/0.98      | sK3 != sK3 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2279]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3369,plain,
% 2.40/0.98      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) != sK4
% 2.40/0.98      | sK2 != sK2
% 2.40/0.98      | sK3 != sK3
% 2.40/0.98      | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top
% 2.40/0.98      | m1_orders_2(sK4,sK2,sK3) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_3366]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1330,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.40/0.98      theory(equality) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1986,plain,
% 2.40/0.98      ( m1_subset_1(X0,X1)
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 2.40/0.98      | X0 != X2
% 2.40/0.98      | X1 != k1_zfmisc_1(X3) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1330]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_2104,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/0.98      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/0.98      | X2 != X0
% 2.40/0.98      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_1986]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3542,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | X1 != X0
% 2.40/0.98      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_2104]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3861,plain,
% 2.40/0.98      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | X0 != sK3
% 2.40/0.98      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2)) ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_3542]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_3863,plain,
% 2.40/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 2.40/0.98      | k1_xboole_0 != sK3 ),
% 2.40/0.98      inference(instantiation,[status(thm)],[c_3861]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5382,plain,
% 2.40/0.98      ( m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) = iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_5299,c_18,c_17,c_30,c_16,c_1344,c_1983,c_2044,c_2063,
% 2.40/0.98                 c_2214,c_2225,c_2500,c_2740,c_2769,c_2946,c_2993,c_3163,
% 2.40/0.98                 c_3369,c_3863]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5396,plain,
% 2.40/0.98      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))
% 2.40/0.98      | sK3 = k1_xboole_0 ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_5382,c_2707]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5427,plain,
% 2.40/0.98      ( k3_orders_2(sK2,sK3,sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)))) = k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)) ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_5396,c_18,c_17,c_16,c_1344,c_1983,c_2063,c_2214,
% 2.40/0.98                 c_2225,c_2500,c_2769,c_2946,c_2993,c_3163,c_3863]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_14,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.40/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | r2_hidden(X2,X3)
% 2.40/0.98      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 2.40/0.98      | v2_struct_0(X1)
% 2.40/0.98      | ~ v3_orders_2(X1)
% 2.40/0.98      | ~ v4_orders_2(X1)
% 2.40/0.98      | ~ v5_orders_2(X1)
% 2.40/0.98      | ~ l1_orders_2(X1) ),
% 2.40/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_625,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.40/0.98      | ~ m1_subset_1(X2,u1_struct_0(X1))
% 2.40/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | r2_hidden(X2,X3)
% 2.40/0.98      | ~ r2_hidden(X2,k3_orders_2(X1,X3,X0))
% 2.40/0.98      | v2_struct_0(X1)
% 2.40/0.98      | ~ v3_orders_2(X1)
% 2.40/0.98      | ~ v4_orders_2(X1)
% 2.40/0.98      | ~ v5_orders_2(X1)
% 2.40/0.98      | sK2 != X1 ),
% 2.40/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_626,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | r2_hidden(X0,X2)
% 2.40/0.98      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1))
% 2.40/0.98      | v2_struct_0(sK2)
% 2.40/0.98      | ~ v3_orders_2(sK2)
% 2.40/0.98      | ~ v4_orders_2(sK2)
% 2.40/0.98      | ~ v5_orders_2(sK2) ),
% 2.40/0.98      inference(unflattening,[status(thm)],[c_625]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_630,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | r2_hidden(X0,X2)
% 2.40/0.98      | ~ r2_hidden(X0,k3_orders_2(sK2,X2,X1)) ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_626,c_23,c_22,c_21,c_20]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_631,plain,
% 2.40/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK2))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | r2_hidden(X1,X2)
% 2.40/0.98      | ~ r2_hidden(X1,k3_orders_2(sK2,X2,X0)) ),
% 2.40/0.98      inference(renaming,[status(thm)],[c_630]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1790,plain,
% 2.40/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/0.98      | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
% 2.40/0.98      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,X2) = iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,X2,X1)) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5435,plain,
% 2.40/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/0.98      | m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
% 2.40/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_5427,c_1790]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_29,plain,
% 2.40/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5394,plain,
% 2.40/0.98      ( m1_subset_1(X0,u1_struct_0(sK2)) = iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_5382,c_3037]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5606,plain,
% 2.40/0.98      ( m1_subset_1(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),u1_struct_0(sK2)) != iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_5435,c_29,c_5394]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5615,plain,
% 2.40/0.98      ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,sK3) = iProver_top
% 2.40/0.98      | r2_hidden(sK1(sK2,sK3,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))),sK4) != iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_3510,c_5606]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_11,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 2.40/0.98      | v2_struct_0(X1)
% 2.40/0.98      | ~ v3_orders_2(X1)
% 2.40/0.98      | ~ v4_orders_2(X1)
% 2.40/0.98      | ~ v5_orders_2(X1)
% 2.40/0.98      | ~ l1_orders_2(X1)
% 2.40/0.98      | k1_xboole_0 = X2 ),
% 2.40/0.98      inference(cnf_transformation,[],[f41]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_137,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 2.40/0.98      | v2_struct_0(X1)
% 2.40/0.98      | ~ v3_orders_2(X1)
% 2.40/0.98      | ~ v4_orders_2(X1)
% 2.40/0.98      | ~ v5_orders_2(X1)
% 2.40/0.98      | ~ l1_orders_2(X1)
% 2.40/0.98      | k1_xboole_0 = X2 ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_11,c_12]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_601,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 2.40/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/0.98      | m1_subset_1(sK1(X1,X2,X0),u1_struct_0(X1))
% 2.40/0.98      | v2_struct_0(X1)
% 2.40/0.98      | ~ v3_orders_2(X1)
% 2.40/0.98      | ~ v4_orders_2(X1)
% 2.40/0.98      | ~ v5_orders_2(X1)
% 2.40/0.98      | sK2 != X1
% 2.40/0.98      | k1_xboole_0 = X2 ),
% 2.40/0.98      inference(resolution_lifted,[status(thm)],[c_137,c_19]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_602,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 2.40/0.98      | v2_struct_0(sK2)
% 2.40/0.98      | ~ v3_orders_2(sK2)
% 2.40/0.98      | ~ v4_orders_2(sK2)
% 2.40/0.98      | ~ v5_orders_2(sK2)
% 2.40/0.98      | k1_xboole_0 = X1 ),
% 2.40/0.98      inference(unflattening,[status(thm)],[c_601]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_606,plain,
% 2.40/0.98      ( ~ m1_orders_2(X0,sK2,X1)
% 2.40/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/0.98      | m1_subset_1(sK1(sK2,X1,X0),u1_struct_0(sK2))
% 2.40/0.98      | k1_xboole_0 = X1 ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_602,c_23,c_22,c_21,c_20]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_1791,plain,
% 2.40/0.98      ( k1_xboole_0 = X0
% 2.40/0.98      | m1_orders_2(X1,sK2,X0) != iProver_top
% 2.40/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | m1_subset_1(sK1(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5617,plain,
% 2.40/0.98      ( sK3 = k1_xboole_0
% 2.40/0.98      | m1_orders_2(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK2,sK3) != iProver_top
% 2.40/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1791,c_5606]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5675,plain,
% 2.40/0.98      ( r2_hidden(X0,sK3) = iProver_top
% 2.40/0.98      | r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top ),
% 2.40/0.98      inference(global_propositional_subsumption,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_5615,c_18,c_29,c_17,c_30,c_16,c_1344,c_1983,c_2044,
% 2.40/0.98                 c_2063,c_2214,c_2225,c_2500,c_2740,c_2769,c_2946,c_2993,
% 2.40/0.98                 c_3163,c_3369,c_3863,c_5617]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5676,plain,
% 2.40/0.98      ( r2_hidden(X0,k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4))) != iProver_top
% 2.40/0.98      | r2_hidden(X0,sK3) = iProver_top ),
% 2.40/0.98      inference(renaming,[status(thm)],[c_5675]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5683,plain,
% 2.40/0.98      ( r2_hidden(sK0(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),X0),sK3) = iProver_top
% 2.40/0.98      | r1_tarski(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),X0) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_1804,c_5676]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_5886,plain,
% 2.40/0.98      ( r1_tarski(k3_orders_2(sK2,sK3,sK1(sK2,sK3,sK4)),sK3) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_5683,c_1805]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_6025,plain,
% 2.40/0.98      ( sK3 = k1_xboole_0 | r1_tarski(sK4,sK3) = iProver_top ),
% 2.40/0.98      inference(superposition,[status(thm)],[c_2740,c_5886]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(c_31,plain,
% 2.40/0.98      ( r1_tarski(sK4,sK3) != iProver_top ),
% 2.40/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.40/0.98  
% 2.40/0.98  cnf(contradiction,plain,
% 2.40/0.98      ( $false ),
% 2.40/0.98      inference(minisat,
% 2.40/0.98                [status(thm)],
% 2.40/0.98                [c_6025,c_3863,c_3163,c_2993,c_2946,c_2769,c_2500,c_2225,
% 2.40/0.98                 c_2214,c_2063,c_1983,c_1344,c_31,c_16,c_17,c_18]) ).
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/0.98  
% 2.40/0.98  ------                               Statistics
% 2.40/0.98  
% 2.40/0.98  ------ General
% 2.40/0.98  
% 2.40/0.98  abstr_ref_over_cycles:                  0
% 2.40/0.98  abstr_ref_under_cycles:                 0
% 2.40/0.98  gc_basic_clause_elim:                   0
% 2.40/0.98  forced_gc_time:                         0
% 2.40/0.98  parsing_time:                           0.01
% 2.40/0.98  unif_index_cands_time:                  0.
% 2.40/0.98  unif_index_add_time:                    0.
% 2.40/0.98  orderings_time:                         0.
% 2.40/0.98  out_proof_time:                         0.014
% 2.40/0.98  total_time:                             0.212
% 2.40/0.98  num_of_symbols:                         50
% 2.40/0.98  num_of_terms:                           4501
% 2.40/0.98  
% 2.40/0.98  ------ Preprocessing
% 2.40/0.98  
% 2.40/0.98  num_of_splits:                          0
% 2.40/0.98  num_of_split_atoms:                     0
% 2.40/0.98  num_of_reused_defs:                     0
% 2.40/0.98  num_eq_ax_congr_red:                    20
% 2.40/0.98  num_of_sem_filtered_clauses:            1
% 2.40/0.98  num_of_subtypes:                        0
% 2.40/0.98  monotx_restored_types:                  0
% 2.40/0.98  sat_num_of_epr_types:                   0
% 2.40/0.98  sat_num_of_non_cyclic_types:            0
% 2.40/0.98  sat_guarded_non_collapsed_types:        0
% 2.40/0.98  num_pure_diseq_elim:                    0
% 2.40/0.98  simp_replaced_by:                       0
% 2.40/0.98  res_preprocessed:                       99
% 2.40/0.98  prep_upred:                             0
% 2.40/0.98  prep_unflattend:                        89
% 2.40/0.98  smt_new_axioms:                         0
% 2.40/0.98  pred_elim_cands:                        4
% 2.40/0.98  pred_elim:                              6
% 2.40/0.98  pred_elim_cl:                           6
% 2.40/0.98  pred_elim_cycles:                       10
% 2.40/0.98  merged_defs:                            8
% 2.40/0.98  merged_defs_ncl:                        0
% 2.40/0.98  bin_hyper_res:                          8
% 2.40/0.98  prep_cycles:                            4
% 2.40/0.98  pred_elim_time:                         0.026
% 2.40/0.98  splitting_time:                         0.
% 2.40/0.98  sem_filter_time:                        0.
% 2.40/0.98  monotx_time:                            0.
% 2.40/0.98  subtype_inf_time:                       0.
% 2.40/0.98  
% 2.40/0.98  ------ Problem properties
% 2.40/0.98  
% 2.40/0.98  clauses:                                18
% 2.40/0.98  conjectures:                            3
% 2.40/0.98  epr:                                    3
% 2.40/0.98  horn:                                   13
% 2.40/0.98  ground:                                 4
% 2.40/0.98  unary:                                  3
% 2.40/0.98  binary:                                 5
% 2.40/0.98  lits:                                   53
% 2.40/0.98  lits_eq:                                6
% 2.40/0.98  fd_pure:                                0
% 2.40/0.98  fd_pseudo:                              0
% 2.40/0.98  fd_cond:                                4
% 2.40/0.98  fd_pseudo_cond:                         0
% 2.40/0.98  ac_symbols:                             0
% 2.40/0.98  
% 2.40/0.98  ------ Propositional Solver
% 2.40/0.98  
% 2.40/0.98  prop_solver_calls:                      28
% 2.40/0.98  prop_fast_solver_calls:                 1127
% 2.40/0.98  smt_solver_calls:                       0
% 2.40/0.98  smt_fast_solver_calls:                  0
% 2.40/0.98  prop_num_of_clauses:                    1807
% 2.40/0.98  prop_preprocess_simplified:             5007
% 2.40/0.98  prop_fo_subsumed:                       56
% 2.40/0.98  prop_solver_time:                       0.
% 2.40/0.98  smt_solver_time:                        0.
% 2.40/0.98  smt_fast_solver_time:                   0.
% 2.40/0.98  prop_fast_solver_time:                  0.
% 2.40/0.98  prop_unsat_core_time:                   0.
% 2.40/0.98  
% 2.40/0.98  ------ QBF
% 2.40/0.98  
% 2.40/0.98  qbf_q_res:                              0
% 2.40/0.98  qbf_num_tautologies:                    0
% 2.40/0.98  qbf_prep_cycles:                        0
% 2.40/0.98  
% 2.40/0.98  ------ BMC1
% 2.40/0.98  
% 2.40/0.98  bmc1_current_bound:                     -1
% 2.40/0.98  bmc1_last_solved_bound:                 -1
% 2.40/0.98  bmc1_unsat_core_size:                   -1
% 2.40/0.98  bmc1_unsat_core_parents_size:           -1
% 2.40/0.98  bmc1_merge_next_fun:                    0
% 2.40/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.40/0.98  
% 2.40/0.98  ------ Instantiation
% 2.40/0.98  
% 2.40/0.98  inst_num_of_clauses:                    458
% 2.40/0.98  inst_num_in_passive:                    172
% 2.40/0.98  inst_num_in_active:                     258
% 2.40/0.98  inst_num_in_unprocessed:                28
% 2.40/0.98  inst_num_of_loops:                      330
% 2.40/0.98  inst_num_of_learning_restarts:          0
% 2.40/0.98  inst_num_moves_active_passive:          68
% 2.40/0.98  inst_lit_activity:                      0
% 2.40/0.98  inst_lit_activity_moves:                0
% 2.40/0.98  inst_num_tautologies:                   0
% 2.40/0.98  inst_num_prop_implied:                  0
% 2.40/0.98  inst_num_existing_simplified:           0
% 2.40/0.98  inst_num_eq_res_simplified:             0
% 2.40/0.98  inst_num_child_elim:                    0
% 2.40/0.98  inst_num_of_dismatching_blockings:      155
% 2.40/0.98  inst_num_of_non_proper_insts:           536
% 2.40/0.98  inst_num_of_duplicates:                 0
% 2.40/0.98  inst_inst_num_from_inst_to_res:         0
% 2.40/0.98  inst_dismatching_checking_time:         0.
% 2.40/0.98  
% 2.40/0.98  ------ Resolution
% 2.40/0.98  
% 2.40/0.98  res_num_of_clauses:                     0
% 2.40/0.98  res_num_in_passive:                     0
% 2.40/0.98  res_num_in_active:                      0
% 2.40/0.98  res_num_of_loops:                       103
% 2.40/0.98  res_forward_subset_subsumed:            24
% 2.40/0.98  res_backward_subset_subsumed:           0
% 2.40/0.98  res_forward_subsumed:                   0
% 2.40/0.98  res_backward_subsumed:                  0
% 2.40/0.98  res_forward_subsumption_resolution:     3
% 2.40/0.98  res_backward_subsumption_resolution:    0
% 2.40/0.98  res_clause_to_clause_subsumption:       626
% 2.40/0.98  res_orphan_elimination:                 0
% 2.40/0.98  res_tautology_del:                      55
% 2.40/0.98  res_num_eq_res_simplified:              0
% 2.40/0.98  res_num_sel_changes:                    0
% 2.40/0.98  res_moves_from_active_to_pass:          0
% 2.40/0.98  
% 2.40/0.98  ------ Superposition
% 2.40/0.98  
% 2.40/0.98  sup_time_total:                         0.
% 2.40/0.98  sup_time_generating:                    0.
% 2.40/0.98  sup_time_sim_full:                      0.
% 2.40/0.98  sup_time_sim_immed:                     0.
% 2.40/0.98  
% 2.40/0.98  sup_num_of_clauses:                     122
% 2.40/0.98  sup_num_in_active:                      65
% 2.40/0.98  sup_num_in_passive:                     57
% 2.40/0.98  sup_num_of_loops:                       64
% 2.40/0.98  sup_fw_superposition:                   57
% 2.40/0.98  sup_bw_superposition:                   75
% 2.40/0.98  sup_immediate_simplified:               19
% 2.40/0.98  sup_given_eliminated:                   0
% 2.40/0.98  comparisons_done:                       0
% 2.40/0.98  comparisons_avoided:                    13
% 2.40/0.98  
% 2.40/0.98  ------ Simplifications
% 2.40/0.98  
% 2.40/0.98  
% 2.40/0.98  sim_fw_subset_subsumed:                 12
% 2.40/0.98  sim_bw_subset_subsumed:                 2
% 2.40/0.98  sim_fw_subsumed:                        3
% 2.40/0.98  sim_bw_subsumed:                        0
% 2.40/0.98  sim_fw_subsumption_res:                 0
% 2.40/0.98  sim_bw_subsumption_res:                 0
% 2.40/0.98  sim_tautology_del:                      5
% 2.40/0.98  sim_eq_tautology_del:                   0
% 2.40/0.98  sim_eq_res_simp:                        0
% 2.40/0.98  sim_fw_demodulated:                     0
% 2.40/0.98  sim_bw_demodulated:                     0
% 2.40/0.98  sim_light_normalised:                   4
% 2.40/0.98  sim_joinable_taut:                      0
% 2.40/0.98  sim_joinable_simp:                      0
% 2.40/0.98  sim_ac_normalised:                      0
% 2.40/0.98  sim_smt_subsumption:                    0
% 2.40/0.98  
%------------------------------------------------------------------------------
