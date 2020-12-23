%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:39 EST 2020

% Result     : Theorem 1.43s
% Output     : CNFRefutation 1.43s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1686)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f6,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f7,plain,(
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
    inference(flattening,[],[f6])).

fof(f14,plain,(
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
    inference(nnf_transformation,[],[f7])).

fof(f15,plain,(
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
    inference(rectify,[],[f14])).

fof(f16,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).

fof(f23,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ( k1_xboole_0 = sK2
            & ~ m1_orders_2(sK2,X0,sK2) )
          | ( m1_orders_2(sK2,X0,sK2)
            & k1_xboole_0 != sK2 ) )
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK1,X1) )
            | ( m1_orders_2(X1,sK1,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ( ( k1_xboole_0 = sK2
        & ~ m1_orders_2(sK2,sK1,sK2) )
      | ( m1_orders_2(sK2,sK1,sK2)
        & k1_xboole_0 != sK2 ) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f21,f20])).

fof(f35,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f34,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f36,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f37,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f38,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_orders_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f39,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

fof(f42,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
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

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f18,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X2)
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
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
    inference(equality_resolution,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f8])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X2,X1)
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

cnf(c_5,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f23])).

cnf(c_17,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_366,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_367,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_18,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_16,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_15,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_371,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_19,c_18,c_16,c_15])).

cnf(c_1125,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1_45,X0_45),u1_struct_0(sK1))
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_1483,plain,
    ( k1_xboole_0 = X0_45
    | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(sK1,X0_45,X1_45),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1125])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1130,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1478,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1130])).

cnf(c_3,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f25])).

cnf(c_420,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_17])).

cnf(c_421,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_425,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_19,c_18,c_16,c_15])).

cnf(c_1123,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1_45,sK0(sK1,X1_45,X0_45)) = X0_45
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_425])).

cnf(c_1485,plain,
    ( k3_orders_2(sK1,X0_45,sK0(sK1,X0_45,X1_45)) = X1_45
    | k1_xboole_0 = X0_45
    | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
    | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1123])).

cnf(c_1933,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
    | sK2 = k1_xboole_0
    | m1_orders_2(X0_45,sK1,sK2) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_1485])).

cnf(c_25,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_0,plain,
    ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_352,plain,
    ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_353,plain,
    ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_352])).

cnf(c_355,plain,
    ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_19,c_18,c_16,c_15])).

cnf(c_13,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1131,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1640,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1123])).

cnf(c_1641,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
    | k1_xboole_0 = sK2
    | m1_orders_2(X0_45,sK1,sK2) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1640])).

cnf(c_1137,plain,
    ( ~ m1_subset_1(X0_45,X0_46)
    | m1_subset_1(X1_45,X0_46)
    | X1_45 != X0_45 ),
    theory(equality)).

cnf(c_1652,plain,
    ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_45 != sK2 ),
    inference(instantiation,[status(thm)],[c_1137])).

cnf(c_1654,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1652])).

cnf(c_1136,plain,
    ( ~ m1_orders_2(X0_45,X0_44,X1_45)
    | m1_orders_2(X2_45,X0_44,X3_45)
    | X2_45 != X0_45
    | X3_45 != X1_45 ),
    theory(equality)).

cnf(c_1738,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | m1_orders_2(sK2,sK1,sK2)
    | sK2 != X0_45
    | sK2 != X1_45 ),
    inference(instantiation,[status(thm)],[c_1136])).

cnf(c_1740,plain,
    ( m1_orders_2(sK2,sK1,sK2)
    | ~ m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_2019,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
    | m1_orders_2(X0_45,sK1,sK2) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1933,c_14,c_25,c_355,c_1131,c_1641,c_1654,c_1740])).

cnf(c_2028,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1478,c_2019])).

cnf(c_10,negated_conjecture,
    ( m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1132,negated_conjecture,
    ( m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1146,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1132])).

cnf(c_1134,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_1696,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1135,plain,
    ( X0_45 != X1_45
    | X2_45 != X1_45
    | X2_45 = X0_45 ),
    theory(equality)).

cnf(c_1669,plain,
    ( X0_45 != X1_45
    | sK2 != X1_45
    | sK2 = X0_45 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1734,plain,
    ( X0_45 != sK2
    | sK2 = X0_45
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1669])).

cnf(c_1735,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_2029,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2028])).

cnf(c_2031,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2028,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,c_1686,c_1696,c_1735,c_1740])).

cnf(c_9,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_265,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_17])).

cnf(c_266,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_270,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_19,c_18,c_16,c_15])).

cnf(c_271,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_1129,plain,
    ( r2_orders_2(sK1,X0_45,X1_45)
    | ~ r2_hidden(X0_45,k3_orders_2(sK1,X2_45,X1_45))
    | ~ m1_subset_1(X2_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_271])).

cnf(c_1479,plain,
    ( r2_orders_2(sK1,X0_45,X1_45) = iProver_top
    | r2_hidden(X0_45,k3_orders_2(sK1,X2_45,X1_45)) != iProver_top
    | m1_subset_1(X2_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1129])).

cnf(c_2036,plain,
    ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1479])).

cnf(c_2143,plain,
    ( m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2036,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,c_1680,c_1696,c_1735,c_1740])).

cnf(c_2144,plain,
    ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2143])).

cnf(c_2153,plain,
    ( sK2 = k1_xboole_0
    | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1483,c_2144])).

cnf(c_1145,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1134])).

cnf(c_1147,plain,
    ( k1_xboole_0 != sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1131])).

cnf(c_1650,plain,
    ( sK2 != X0_45
    | k1_xboole_0 != X0_45
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1135])).

cnf(c_1651,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1650])).

cnf(c_2,plain,
    ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_322,plain,
    ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_17])).

cnf(c_323,plain,
    ( m1_orders_2(k3_orders_2(sK1,X0,X1),sK1,X0)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k3_orders_2(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( m1_orders_2(k3_orders_2(sK1,X0,X1),sK1,X0)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k3_orders_2(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_19,c_18,c_16,c_15])).

cnf(c_1127,plain,
    ( m1_orders_2(k3_orders_2(sK1,X0_45,X1_45),sK1,X0_45)
    | ~ r2_hidden(X1_45,X0_45)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
    | ~ m1_subset_1(k3_orders_2(sK1,X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X0_45 ),
    inference(subtyping,[status(esa)],[c_327])).

cnf(c_1481,plain,
    ( k1_xboole_0 = X0_45
    | m1_orders_2(k3_orders_2(sK1,X0_45,X1_45),sK1,X0_45) = iProver_top
    | r2_hidden(X1_45,X0_45) != iProver_top
    | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1127])).

cnf(c_2139,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)),sK1,sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2031,c_1481])).

cnf(c_2140,plain,
    ( sK2 = k1_xboole_0
    | m1_orders_2(sK2,sK1,sK2) = iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2139,c_2031])).

cnf(c_28,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2246,plain,
    ( m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2140,c_14,c_13,c_28,c_355,c_1146,c_1654,c_1696,c_1735,c_1740])).

cnf(c_2252,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,c_1680,c_1696,c_1735,c_1740,c_2036])).

cnf(c_2253,plain,
    ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2252])).

cnf(c_6,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_550,plain,
    ( ~ r2_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X1)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_551,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_555,plain,
    ( ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_orders_2(sK1,X1,X0)
    | ~ r2_orders_2(sK1,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_16])).

cnf(c_556,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X0)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_555])).

cnf(c_1120,plain,
    ( ~ r2_orders_2(sK1,X0_45,X1_45)
    | ~ r2_orders_2(sK1,X1_45,X0_45)
    | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_556])).

cnf(c_1488,plain,
    ( r2_orders_2(sK1,X0_45,X1_45) != iProver_top
    | r2_orders_2(sK1,X1_45,X0_45) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1120])).

cnf(c_2261,plain,
    ( r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_1488])).

cnf(c_1625,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,sK2,X0_45),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1125])).

cnf(c_1679,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_1680,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1679])).

cnf(c_2318,plain,
    ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2261,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,c_1680,c_1696,c_1735,c_1740])).

cnf(c_2319,plain,
    ( r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top
    | r2_hidden(X0_45,sK2) != iProver_top
    | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2318])).

cnf(c_2327,plain,
    ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2253,c_2319])).

cnf(c_4,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f24])).

cnf(c_393,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_394,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_398,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_19,c_18,c_16,c_15])).

cnf(c_1124,plain,
    ( ~ m1_orders_2(X0_45,sK1,X1_45)
    | r2_hidden(sK0(sK1,X1_45,X0_45),X1_45)
    | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1_45 ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1630,plain,
    ( ~ m1_orders_2(X0_45,sK1,sK2)
    | r2_hidden(sK0(sK1,sK2,X0_45),sK2)
    | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1124])).

cnf(c_1682,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | r2_hidden(sK0(sK1,sK2,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1630])).

cnf(c_1683,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2327,c_2246,c_1683,c_1680,c_1147,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:04:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.43/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.43/0.97  
% 1.43/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.43/0.97  
% 1.43/0.97  ------  iProver source info
% 1.43/0.97  
% 1.43/0.97  git: date: 2020-06-30 10:37:57 +0100
% 1.43/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.43/0.97  git: non_committed_changes: false
% 1.43/0.97  git: last_make_outside_of_git: false
% 1.43/0.97  
% 1.43/0.97  ------ 
% 1.43/0.97  
% 1.43/0.97  ------ Input Options
% 1.43/0.97  
% 1.43/0.97  --out_options                           all
% 1.43/0.97  --tptp_safe_out                         true
% 1.43/0.97  --problem_path                          ""
% 1.43/0.97  --include_path                          ""
% 1.43/0.97  --clausifier                            res/vclausify_rel
% 1.43/0.97  --clausifier_options                    --mode clausify
% 1.43/0.97  --stdin                                 false
% 1.43/0.97  --stats_out                             all
% 1.43/0.97  
% 1.43/0.97  ------ General Options
% 1.43/0.97  
% 1.43/0.97  --fof                                   false
% 1.43/0.97  --time_out_real                         305.
% 1.43/0.97  --time_out_virtual                      -1.
% 1.43/0.97  --symbol_type_check                     false
% 1.43/0.97  --clausify_out                          false
% 1.43/0.97  --sig_cnt_out                           false
% 1.43/0.97  --trig_cnt_out                          false
% 1.43/0.97  --trig_cnt_out_tolerance                1.
% 1.43/0.97  --trig_cnt_out_sk_spl                   false
% 1.43/0.97  --abstr_cl_out                          false
% 1.43/0.97  
% 1.43/0.97  ------ Global Options
% 1.43/0.97  
% 1.43/0.97  --schedule                              default
% 1.43/0.97  --add_important_lit                     false
% 1.43/0.97  --prop_solver_per_cl                    1000
% 1.43/0.97  --min_unsat_core                        false
% 1.43/0.97  --soft_assumptions                      false
% 1.43/0.97  --soft_lemma_size                       3
% 1.43/0.97  --prop_impl_unit_size                   0
% 1.43/0.97  --prop_impl_unit                        []
% 1.43/0.97  --share_sel_clauses                     true
% 1.43/0.97  --reset_solvers                         false
% 1.43/0.97  --bc_imp_inh                            [conj_cone]
% 1.43/0.97  --conj_cone_tolerance                   3.
% 1.43/0.97  --extra_neg_conj                        none
% 1.43/0.97  --large_theory_mode                     true
% 1.43/0.97  --prolific_symb_bound                   200
% 1.43/0.97  --lt_threshold                          2000
% 1.43/0.97  --clause_weak_htbl                      true
% 1.43/0.97  --gc_record_bc_elim                     false
% 1.43/0.97  
% 1.43/0.97  ------ Preprocessing Options
% 1.43/0.97  
% 1.43/0.97  --preprocessing_flag                    true
% 1.43/0.97  --time_out_prep_mult                    0.1
% 1.43/0.97  --splitting_mode                        input
% 1.43/0.97  --splitting_grd                         true
% 1.43/0.97  --splitting_cvd                         false
% 1.43/0.97  --splitting_cvd_svl                     false
% 1.43/0.97  --splitting_nvd                         32
% 1.43/0.97  --sub_typing                            true
% 1.43/0.97  --prep_gs_sim                           true
% 1.43/0.97  --prep_unflatten                        true
% 1.43/0.97  --prep_res_sim                          true
% 1.43/0.97  --prep_upred                            true
% 1.43/0.97  --prep_sem_filter                       exhaustive
% 1.43/0.97  --prep_sem_filter_out                   false
% 1.43/0.97  --pred_elim                             true
% 1.43/0.97  --res_sim_input                         true
% 1.43/0.97  --eq_ax_congr_red                       true
% 1.43/0.97  --pure_diseq_elim                       true
% 1.43/0.97  --brand_transform                       false
% 1.43/0.97  --non_eq_to_eq                          false
% 1.43/0.97  --prep_def_merge                        true
% 1.43/0.97  --prep_def_merge_prop_impl              false
% 1.43/0.97  --prep_def_merge_mbd                    true
% 1.43/0.97  --prep_def_merge_tr_red                 false
% 1.43/0.97  --prep_def_merge_tr_cl                  false
% 1.43/0.97  --smt_preprocessing                     true
% 1.43/0.97  --smt_ac_axioms                         fast
% 1.43/0.97  --preprocessed_out                      false
% 1.43/0.97  --preprocessed_stats                    false
% 1.43/0.97  
% 1.43/0.97  ------ Abstraction refinement Options
% 1.43/0.97  
% 1.43/0.97  --abstr_ref                             []
% 1.43/0.97  --abstr_ref_prep                        false
% 1.43/0.97  --abstr_ref_until_sat                   false
% 1.43/0.97  --abstr_ref_sig_restrict                funpre
% 1.43/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.97  --abstr_ref_under                       []
% 1.43/0.97  
% 1.43/0.97  ------ SAT Options
% 1.43/0.97  
% 1.43/0.97  --sat_mode                              false
% 1.43/0.97  --sat_fm_restart_options                ""
% 1.43/0.97  --sat_gr_def                            false
% 1.43/0.97  --sat_epr_types                         true
% 1.43/0.97  --sat_non_cyclic_types                  false
% 1.43/0.97  --sat_finite_models                     false
% 1.43/0.97  --sat_fm_lemmas                         false
% 1.43/0.97  --sat_fm_prep                           false
% 1.43/0.97  --sat_fm_uc_incr                        true
% 1.43/0.97  --sat_out_model                         small
% 1.43/0.97  --sat_out_clauses                       false
% 1.43/0.97  
% 1.43/0.97  ------ QBF Options
% 1.43/0.97  
% 1.43/0.97  --qbf_mode                              false
% 1.43/0.97  --qbf_elim_univ                         false
% 1.43/0.97  --qbf_dom_inst                          none
% 1.43/0.97  --qbf_dom_pre_inst                      false
% 1.43/0.97  --qbf_sk_in                             false
% 1.43/0.97  --qbf_pred_elim                         true
% 1.43/0.97  --qbf_split                             512
% 1.43/0.97  
% 1.43/0.97  ------ BMC1 Options
% 1.43/0.97  
% 1.43/0.97  --bmc1_incremental                      false
% 1.43/0.97  --bmc1_axioms                           reachable_all
% 1.43/0.97  --bmc1_min_bound                        0
% 1.43/0.97  --bmc1_max_bound                        -1
% 1.43/0.97  --bmc1_max_bound_default                -1
% 1.43/0.97  --bmc1_symbol_reachability              true
% 1.43/0.97  --bmc1_property_lemmas                  false
% 1.43/0.97  --bmc1_k_induction                      false
% 1.43/0.97  --bmc1_non_equiv_states                 false
% 1.43/0.97  --bmc1_deadlock                         false
% 1.43/0.97  --bmc1_ucm                              false
% 1.43/0.97  --bmc1_add_unsat_core                   none
% 1.43/0.97  --bmc1_unsat_core_children              false
% 1.43/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.97  --bmc1_out_stat                         full
% 1.43/0.97  --bmc1_ground_init                      false
% 1.43/0.97  --bmc1_pre_inst_next_state              false
% 1.43/0.97  --bmc1_pre_inst_state                   false
% 1.43/0.97  --bmc1_pre_inst_reach_state             false
% 1.43/0.97  --bmc1_out_unsat_core                   false
% 1.43/0.97  --bmc1_aig_witness_out                  false
% 1.43/0.97  --bmc1_verbose                          false
% 1.43/0.97  --bmc1_dump_clauses_tptp                false
% 1.43/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.97  --bmc1_dump_file                        -
% 1.43/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.97  --bmc1_ucm_extend_mode                  1
% 1.43/0.97  --bmc1_ucm_init_mode                    2
% 1.43/0.97  --bmc1_ucm_cone_mode                    none
% 1.43/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.97  --bmc1_ucm_relax_model                  4
% 1.43/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.97  --bmc1_ucm_layered_model                none
% 1.43/0.97  --bmc1_ucm_max_lemma_size               10
% 1.43/0.97  
% 1.43/0.97  ------ AIG Options
% 1.43/0.97  
% 1.43/0.97  --aig_mode                              false
% 1.43/0.97  
% 1.43/0.97  ------ Instantiation Options
% 1.43/0.97  
% 1.43/0.97  --instantiation_flag                    true
% 1.43/0.97  --inst_sos_flag                         false
% 1.43/0.97  --inst_sos_phase                        true
% 1.43/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.97  --inst_lit_sel_side                     num_symb
% 1.43/0.97  --inst_solver_per_active                1400
% 1.43/0.97  --inst_solver_calls_frac                1.
% 1.43/0.97  --inst_passive_queue_type               priority_queues
% 1.43/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.97  --inst_passive_queues_freq              [25;2]
% 1.43/0.97  --inst_dismatching                      true
% 1.43/0.97  --inst_eager_unprocessed_to_passive     true
% 1.43/0.97  --inst_prop_sim_given                   true
% 1.43/0.97  --inst_prop_sim_new                     false
% 1.43/0.97  --inst_subs_new                         false
% 1.43/0.97  --inst_eq_res_simp                      false
% 1.43/0.97  --inst_subs_given                       false
% 1.43/0.97  --inst_orphan_elimination               true
% 1.43/0.97  --inst_learning_loop_flag               true
% 1.43/0.97  --inst_learning_start                   3000
% 1.43/0.97  --inst_learning_factor                  2
% 1.43/0.97  --inst_start_prop_sim_after_learn       3
% 1.43/0.97  --inst_sel_renew                        solver
% 1.43/0.97  --inst_lit_activity_flag                true
% 1.43/0.97  --inst_restr_to_given                   false
% 1.43/0.97  --inst_activity_threshold               500
% 1.43/0.97  --inst_out_proof                        true
% 1.43/0.97  
% 1.43/0.97  ------ Resolution Options
% 1.43/0.97  
% 1.43/0.97  --resolution_flag                       true
% 1.43/0.97  --res_lit_sel                           adaptive
% 1.43/0.97  --res_lit_sel_side                      none
% 1.43/0.97  --res_ordering                          kbo
% 1.43/0.97  --res_to_prop_solver                    active
% 1.43/0.97  --res_prop_simpl_new                    false
% 1.43/0.97  --res_prop_simpl_given                  true
% 1.43/0.97  --res_passive_queue_type                priority_queues
% 1.43/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.97  --res_passive_queues_freq               [15;5]
% 1.43/0.97  --res_forward_subs                      full
% 1.43/0.97  --res_backward_subs                     full
% 1.43/0.97  --res_forward_subs_resolution           true
% 1.43/0.97  --res_backward_subs_resolution          true
% 1.43/0.97  --res_orphan_elimination                true
% 1.43/0.97  --res_time_limit                        2.
% 1.43/0.97  --res_out_proof                         true
% 1.43/0.97  
% 1.43/0.97  ------ Superposition Options
% 1.43/0.97  
% 1.43/0.97  --superposition_flag                    true
% 1.43/0.97  --sup_passive_queue_type                priority_queues
% 1.43/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.97  --demod_completeness_check              fast
% 1.43/0.97  --demod_use_ground                      true
% 1.43/0.97  --sup_to_prop_solver                    passive
% 1.43/0.97  --sup_prop_simpl_new                    true
% 1.43/0.97  --sup_prop_simpl_given                  true
% 1.43/0.97  --sup_fun_splitting                     false
% 1.43/0.97  --sup_smt_interval                      50000
% 1.43/0.97  
% 1.43/0.97  ------ Superposition Simplification Setup
% 1.43/0.97  
% 1.43/0.97  --sup_indices_passive                   []
% 1.43/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_full_bw                           [BwDemod]
% 1.43/0.97  --sup_immed_triv                        [TrivRules]
% 1.43/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_immed_bw_main                     []
% 1.43/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.97  
% 1.43/0.97  ------ Combination Options
% 1.43/0.97  
% 1.43/0.97  --comb_res_mult                         3
% 1.43/0.97  --comb_sup_mult                         2
% 1.43/0.97  --comb_inst_mult                        10
% 1.43/0.97  
% 1.43/0.97  ------ Debug Options
% 1.43/0.97  
% 1.43/0.97  --dbg_backtrace                         false
% 1.43/0.97  --dbg_dump_prop_clauses                 false
% 1.43/0.97  --dbg_dump_prop_clauses_file            -
% 1.43/0.97  --dbg_out_stat                          false
% 1.43/0.97  ------ Parsing...
% 1.43/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.43/0.97  
% 1.43/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.43/0.97  
% 1.43/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.43/0.97  
% 1.43/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.43/0.97  ------ Proving...
% 1.43/0.97  ------ Problem Properties 
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  clauses                                 13
% 1.43/0.97  conjectures                             3
% 1.43/0.97  EPR                                     2
% 1.43/0.97  Horn                                    8
% 1.43/0.97  unary                                   1
% 1.43/0.97  binary                                  3
% 1.43/0.97  lits                                    52
% 1.43/0.97  lits eq                                 8
% 1.43/0.97  fd_pure                                 0
% 1.43/0.97  fd_pseudo                               0
% 1.43/0.97  fd_cond                                 4
% 1.43/0.97  fd_pseudo_cond                          0
% 1.43/0.97  AC symbols                              0
% 1.43/0.97  
% 1.43/0.97  ------ Schedule dynamic 5 is on 
% 1.43/0.97  
% 1.43/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  ------ 
% 1.43/0.97  Current options:
% 1.43/0.97  ------ 
% 1.43/0.97  
% 1.43/0.97  ------ Input Options
% 1.43/0.97  
% 1.43/0.97  --out_options                           all
% 1.43/0.97  --tptp_safe_out                         true
% 1.43/0.97  --problem_path                          ""
% 1.43/0.97  --include_path                          ""
% 1.43/0.97  --clausifier                            res/vclausify_rel
% 1.43/0.97  --clausifier_options                    --mode clausify
% 1.43/0.97  --stdin                                 false
% 1.43/0.97  --stats_out                             all
% 1.43/0.97  
% 1.43/0.97  ------ General Options
% 1.43/0.97  
% 1.43/0.97  --fof                                   false
% 1.43/0.97  --time_out_real                         305.
% 1.43/0.97  --time_out_virtual                      -1.
% 1.43/0.97  --symbol_type_check                     false
% 1.43/0.97  --clausify_out                          false
% 1.43/0.97  --sig_cnt_out                           false
% 1.43/0.97  --trig_cnt_out                          false
% 1.43/0.97  --trig_cnt_out_tolerance                1.
% 1.43/0.97  --trig_cnt_out_sk_spl                   false
% 1.43/0.97  --abstr_cl_out                          false
% 1.43/0.97  
% 1.43/0.97  ------ Global Options
% 1.43/0.97  
% 1.43/0.97  --schedule                              default
% 1.43/0.97  --add_important_lit                     false
% 1.43/0.97  --prop_solver_per_cl                    1000
% 1.43/0.97  --min_unsat_core                        false
% 1.43/0.97  --soft_assumptions                      false
% 1.43/0.97  --soft_lemma_size                       3
% 1.43/0.97  --prop_impl_unit_size                   0
% 1.43/0.97  --prop_impl_unit                        []
% 1.43/0.97  --share_sel_clauses                     true
% 1.43/0.97  --reset_solvers                         false
% 1.43/0.97  --bc_imp_inh                            [conj_cone]
% 1.43/0.97  --conj_cone_tolerance                   3.
% 1.43/0.97  --extra_neg_conj                        none
% 1.43/0.97  --large_theory_mode                     true
% 1.43/0.97  --prolific_symb_bound                   200
% 1.43/0.97  --lt_threshold                          2000
% 1.43/0.97  --clause_weak_htbl                      true
% 1.43/0.97  --gc_record_bc_elim                     false
% 1.43/0.97  
% 1.43/0.97  ------ Preprocessing Options
% 1.43/0.97  
% 1.43/0.97  --preprocessing_flag                    true
% 1.43/0.97  --time_out_prep_mult                    0.1
% 1.43/0.97  --splitting_mode                        input
% 1.43/0.97  --splitting_grd                         true
% 1.43/0.97  --splitting_cvd                         false
% 1.43/0.97  --splitting_cvd_svl                     false
% 1.43/0.97  --splitting_nvd                         32
% 1.43/0.97  --sub_typing                            true
% 1.43/0.97  --prep_gs_sim                           true
% 1.43/0.97  --prep_unflatten                        true
% 1.43/0.97  --prep_res_sim                          true
% 1.43/0.97  --prep_upred                            true
% 1.43/0.97  --prep_sem_filter                       exhaustive
% 1.43/0.97  --prep_sem_filter_out                   false
% 1.43/0.97  --pred_elim                             true
% 1.43/0.97  --res_sim_input                         true
% 1.43/0.97  --eq_ax_congr_red                       true
% 1.43/0.97  --pure_diseq_elim                       true
% 1.43/0.97  --brand_transform                       false
% 1.43/0.97  --non_eq_to_eq                          false
% 1.43/0.97  --prep_def_merge                        true
% 1.43/0.97  --prep_def_merge_prop_impl              false
% 1.43/0.97  --prep_def_merge_mbd                    true
% 1.43/0.97  --prep_def_merge_tr_red                 false
% 1.43/0.97  --prep_def_merge_tr_cl                  false
% 1.43/0.97  --smt_preprocessing                     true
% 1.43/0.97  --smt_ac_axioms                         fast
% 1.43/0.97  --preprocessed_out                      false
% 1.43/0.97  --preprocessed_stats                    false
% 1.43/0.97  
% 1.43/0.97  ------ Abstraction refinement Options
% 1.43/0.97  
% 1.43/0.97  --abstr_ref                             []
% 1.43/0.97  --abstr_ref_prep                        false
% 1.43/0.97  --abstr_ref_until_sat                   false
% 1.43/0.97  --abstr_ref_sig_restrict                funpre
% 1.43/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 1.43/0.97  --abstr_ref_under                       []
% 1.43/0.97  
% 1.43/0.97  ------ SAT Options
% 1.43/0.97  
% 1.43/0.97  --sat_mode                              false
% 1.43/0.97  --sat_fm_restart_options                ""
% 1.43/0.97  --sat_gr_def                            false
% 1.43/0.97  --sat_epr_types                         true
% 1.43/0.97  --sat_non_cyclic_types                  false
% 1.43/0.97  --sat_finite_models                     false
% 1.43/0.97  --sat_fm_lemmas                         false
% 1.43/0.97  --sat_fm_prep                           false
% 1.43/0.97  --sat_fm_uc_incr                        true
% 1.43/0.97  --sat_out_model                         small
% 1.43/0.97  --sat_out_clauses                       false
% 1.43/0.97  
% 1.43/0.97  ------ QBF Options
% 1.43/0.97  
% 1.43/0.97  --qbf_mode                              false
% 1.43/0.97  --qbf_elim_univ                         false
% 1.43/0.97  --qbf_dom_inst                          none
% 1.43/0.97  --qbf_dom_pre_inst                      false
% 1.43/0.97  --qbf_sk_in                             false
% 1.43/0.97  --qbf_pred_elim                         true
% 1.43/0.97  --qbf_split                             512
% 1.43/0.97  
% 1.43/0.97  ------ BMC1 Options
% 1.43/0.97  
% 1.43/0.97  --bmc1_incremental                      false
% 1.43/0.97  --bmc1_axioms                           reachable_all
% 1.43/0.97  --bmc1_min_bound                        0
% 1.43/0.97  --bmc1_max_bound                        -1
% 1.43/0.97  --bmc1_max_bound_default                -1
% 1.43/0.97  --bmc1_symbol_reachability              true
% 1.43/0.97  --bmc1_property_lemmas                  false
% 1.43/0.97  --bmc1_k_induction                      false
% 1.43/0.97  --bmc1_non_equiv_states                 false
% 1.43/0.97  --bmc1_deadlock                         false
% 1.43/0.97  --bmc1_ucm                              false
% 1.43/0.97  --bmc1_add_unsat_core                   none
% 1.43/0.97  --bmc1_unsat_core_children              false
% 1.43/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 1.43/0.97  --bmc1_out_stat                         full
% 1.43/0.97  --bmc1_ground_init                      false
% 1.43/0.97  --bmc1_pre_inst_next_state              false
% 1.43/0.97  --bmc1_pre_inst_state                   false
% 1.43/0.97  --bmc1_pre_inst_reach_state             false
% 1.43/0.97  --bmc1_out_unsat_core                   false
% 1.43/0.97  --bmc1_aig_witness_out                  false
% 1.43/0.97  --bmc1_verbose                          false
% 1.43/0.97  --bmc1_dump_clauses_tptp                false
% 1.43/0.97  --bmc1_dump_unsat_core_tptp             false
% 1.43/0.97  --bmc1_dump_file                        -
% 1.43/0.97  --bmc1_ucm_expand_uc_limit              128
% 1.43/0.97  --bmc1_ucm_n_expand_iterations          6
% 1.43/0.97  --bmc1_ucm_extend_mode                  1
% 1.43/0.97  --bmc1_ucm_init_mode                    2
% 1.43/0.97  --bmc1_ucm_cone_mode                    none
% 1.43/0.97  --bmc1_ucm_reduced_relation_type        0
% 1.43/0.97  --bmc1_ucm_relax_model                  4
% 1.43/0.97  --bmc1_ucm_full_tr_after_sat            true
% 1.43/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 1.43/0.97  --bmc1_ucm_layered_model                none
% 1.43/0.97  --bmc1_ucm_max_lemma_size               10
% 1.43/0.97  
% 1.43/0.97  ------ AIG Options
% 1.43/0.97  
% 1.43/0.97  --aig_mode                              false
% 1.43/0.97  
% 1.43/0.97  ------ Instantiation Options
% 1.43/0.97  
% 1.43/0.97  --instantiation_flag                    true
% 1.43/0.97  --inst_sos_flag                         false
% 1.43/0.97  --inst_sos_phase                        true
% 1.43/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.43/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.43/0.97  --inst_lit_sel_side                     none
% 1.43/0.97  --inst_solver_per_active                1400
% 1.43/0.97  --inst_solver_calls_frac                1.
% 1.43/0.97  --inst_passive_queue_type               priority_queues
% 1.43/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.43/0.97  --inst_passive_queues_freq              [25;2]
% 1.43/0.97  --inst_dismatching                      true
% 1.43/0.97  --inst_eager_unprocessed_to_passive     true
% 1.43/0.97  --inst_prop_sim_given                   true
% 1.43/0.97  --inst_prop_sim_new                     false
% 1.43/0.97  --inst_subs_new                         false
% 1.43/0.97  --inst_eq_res_simp                      false
% 1.43/0.97  --inst_subs_given                       false
% 1.43/0.97  --inst_orphan_elimination               true
% 1.43/0.97  --inst_learning_loop_flag               true
% 1.43/0.97  --inst_learning_start                   3000
% 1.43/0.97  --inst_learning_factor                  2
% 1.43/0.97  --inst_start_prop_sim_after_learn       3
% 1.43/0.97  --inst_sel_renew                        solver
% 1.43/0.97  --inst_lit_activity_flag                true
% 1.43/0.97  --inst_restr_to_given                   false
% 1.43/0.97  --inst_activity_threshold               500
% 1.43/0.97  --inst_out_proof                        true
% 1.43/0.97  
% 1.43/0.97  ------ Resolution Options
% 1.43/0.97  
% 1.43/0.97  --resolution_flag                       false
% 1.43/0.97  --res_lit_sel                           adaptive
% 1.43/0.97  --res_lit_sel_side                      none
% 1.43/0.97  --res_ordering                          kbo
% 1.43/0.97  --res_to_prop_solver                    active
% 1.43/0.97  --res_prop_simpl_new                    false
% 1.43/0.97  --res_prop_simpl_given                  true
% 1.43/0.97  --res_passive_queue_type                priority_queues
% 1.43/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.43/0.97  --res_passive_queues_freq               [15;5]
% 1.43/0.97  --res_forward_subs                      full
% 1.43/0.97  --res_backward_subs                     full
% 1.43/0.97  --res_forward_subs_resolution           true
% 1.43/0.97  --res_backward_subs_resolution          true
% 1.43/0.97  --res_orphan_elimination                true
% 1.43/0.97  --res_time_limit                        2.
% 1.43/0.97  --res_out_proof                         true
% 1.43/0.97  
% 1.43/0.97  ------ Superposition Options
% 1.43/0.97  
% 1.43/0.97  --superposition_flag                    true
% 1.43/0.97  --sup_passive_queue_type                priority_queues
% 1.43/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.43/0.97  --sup_passive_queues_freq               [8;1;4]
% 1.43/0.97  --demod_completeness_check              fast
% 1.43/0.97  --demod_use_ground                      true
% 1.43/0.97  --sup_to_prop_solver                    passive
% 1.43/0.97  --sup_prop_simpl_new                    true
% 1.43/0.97  --sup_prop_simpl_given                  true
% 1.43/0.97  --sup_fun_splitting                     false
% 1.43/0.97  --sup_smt_interval                      50000
% 1.43/0.97  
% 1.43/0.97  ------ Superposition Simplification Setup
% 1.43/0.97  
% 1.43/0.97  --sup_indices_passive                   []
% 1.43/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.43/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 1.43/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_full_bw                           [BwDemod]
% 1.43/0.97  --sup_immed_triv                        [TrivRules]
% 1.43/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.43/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_immed_bw_main                     []
% 1.43/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 1.43/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.43/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.43/0.97  
% 1.43/0.97  ------ Combination Options
% 1.43/0.97  
% 1.43/0.97  --comb_res_mult                         3
% 1.43/0.97  --comb_sup_mult                         2
% 1.43/0.97  --comb_inst_mult                        10
% 1.43/0.97  
% 1.43/0.97  ------ Debug Options
% 1.43/0.97  
% 1.43/0.97  --dbg_backtrace                         false
% 1.43/0.97  --dbg_dump_prop_clauses                 false
% 1.43/0.97  --dbg_dump_prop_clauses_file            -
% 1.43/0.97  --dbg_out_stat                          false
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  ------ Proving...
% 1.43/0.97  
% 1.43/0.97  
% 1.43/0.97  % SZS status Theorem for theBenchmark.p
% 1.43/0.97  
% 1.43/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 1.43/0.97  
% 1.43/0.97  fof(f1,axiom,(
% 1.43/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.43/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.97  
% 1.43/0.97  fof(f6,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.97    inference(ennf_transformation,[],[f1])).
% 1.43/0.97  
% 1.43/0.97  fof(f7,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(flattening,[],[f6])).
% 1.43/0.97  
% 1.43/0.97  fof(f14,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(nnf_transformation,[],[f7])).
% 1.43/0.97  
% 1.43/0.97  fof(f15,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(rectify,[],[f14])).
% 1.43/0.97  
% 1.43/0.97  fof(f16,plain,(
% 1.43/0.97    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.43/0.97    introduced(choice_axiom,[])).
% 1.43/0.97  
% 1.43/0.97  fof(f17,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f16])).
% 1.43/0.97  
% 1.43/0.97  fof(f23,plain,(
% 1.43/0.97    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f17])).
% 1.43/0.97  
% 1.43/0.97  fof(f4,conjecture,(
% 1.43/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.43/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.97  
% 1.43/0.97  fof(f5,negated_conjecture,(
% 1.43/0.97    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.43/0.97    inference(negated_conjecture,[],[f4])).
% 1.43/0.97  
% 1.43/0.97  fof(f12,plain,(
% 1.43/0.97    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.43/0.97    inference(ennf_transformation,[],[f5])).
% 1.43/0.97  
% 1.43/0.97  fof(f13,plain,(
% 1.43/0.97    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.43/0.97    inference(flattening,[],[f12])).
% 1.43/0.97  
% 1.43/0.97  fof(f21,plain,(
% 1.43/0.97    ( ! [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k1_xboole_0 = sK2 & ~m1_orders_2(sK2,X0,sK2)) | (m1_orders_2(sK2,X0,sK2) & k1_xboole_0 != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.43/0.97    introduced(choice_axiom,[])).
% 1.43/0.97  
% 1.43/0.97  fof(f20,plain,(
% 1.43/0.97    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK1,X1)) | (m1_orders_2(X1,sK1,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.43/0.97    introduced(choice_axiom,[])).
% 1.43/0.97  
% 1.43/0.97  fof(f22,plain,(
% 1.43/0.97    (((k1_xboole_0 = sK2 & ~m1_orders_2(sK2,sK1,sK2)) | (m1_orders_2(sK2,sK1,sK2) & k1_xboole_0 != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.43/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f13,f21,f20])).
% 1.43/0.97  
% 1.43/0.97  fof(f35,plain,(
% 1.43/0.97    v4_orders_2(sK1)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f33,plain,(
% 1.43/0.97    ~v2_struct_0(sK1)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f34,plain,(
% 1.43/0.97    v3_orders_2(sK1)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f36,plain,(
% 1.43/0.97    v5_orders_2(sK1)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f37,plain,(
% 1.43/0.97    l1_orders_2(sK1)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f38,plain,(
% 1.43/0.97    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f25,plain,(
% 1.43/0.97    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f17])).
% 1.43/0.97  
% 1.43/0.97  fof(f28,plain,(
% 1.43/0.97    ( ! [X2,X0,X1] : (m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f17])).
% 1.43/0.97  
% 1.43/0.97  fof(f43,plain,(
% 1.43/0.97    ( ! [X0,X1] : (m1_orders_2(k1_xboole_0,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(equality_resolution,[],[f28])).
% 1.43/0.97  
% 1.43/0.97  fof(f44,plain,(
% 1.43/0.97    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(equality_resolution,[],[f43])).
% 1.43/0.97  
% 1.43/0.97  fof(f39,plain,(
% 1.43/0.97    ~m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f42,plain,(
% 1.43/0.97    k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2)),
% 1.43/0.97    inference(cnf_transformation,[],[f22])).
% 1.43/0.97  
% 1.43/0.97  fof(f3,axiom,(
% 1.43/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.43/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.97  
% 1.43/0.97  fof(f10,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.43/0.97    inference(ennf_transformation,[],[f3])).
% 1.43/0.97  
% 1.43/0.97  fof(f11,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(flattening,[],[f10])).
% 1.43/0.97  
% 1.43/0.97  fof(f18,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(nnf_transformation,[],[f11])).
% 1.43/0.97  
% 1.43/0.97  fof(f19,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.43/0.97    inference(flattening,[],[f18])).
% 1.43/0.97  
% 1.43/0.97  fof(f30,plain,(
% 1.43/0.97    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f19])).
% 1.43/0.97  
% 1.43/0.97  fof(f26,plain,(
% 1.43/0.97    ( ! [X2,X0,X3,X1] : (m1_orders_2(X2,X0,X1) | k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f17])).
% 1.43/0.97  
% 1.43/0.97  fof(f46,plain,(
% 1.43/0.97    ( ! [X0,X3,X1] : (m1_orders_2(k3_orders_2(X0,X1,X3),X0,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | k1_xboole_0 = X1 | ~m1_subset_1(k3_orders_2(X0,X1,X3),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(equality_resolution,[],[f26])).
% 1.43/0.97  
% 1.43/0.97  fof(f2,axiom,(
% 1.43/0.97    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 1.43/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.43/0.97  
% 1.43/0.97  fof(f8,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 1.43/0.97    inference(ennf_transformation,[],[f2])).
% 1.43/0.97  
% 1.43/0.97  fof(f9,plain,(
% 1.43/0.97    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 1.43/0.97    inference(flattening,[],[f8])).
% 1.43/0.97  
% 1.43/0.97  fof(f29,plain,(
% 1.43/0.97    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f9])).
% 1.43/0.97  
% 1.43/0.97  fof(f24,plain,(
% 1.43/0.97    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.43/0.97    inference(cnf_transformation,[],[f17])).
% 1.43/0.97  
% 1.43/0.97  cnf(c_5,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.43/0.97      | v2_struct_0(X1)
% 1.43/0.97      | ~ v3_orders_2(X1)
% 1.43/0.97      | ~ v4_orders_2(X1)
% 1.43/0.97      | ~ v5_orders_2(X1)
% 1.43/0.97      | ~ l1_orders_2(X1)
% 1.43/0.97      | k1_xboole_0 = X2 ),
% 1.43/0.97      inference(cnf_transformation,[],[f23]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_17,negated_conjecture,
% 1.43/0.97      ( v4_orders_2(sK1) ),
% 1.43/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_366,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.43/0.97      | v2_struct_0(X1)
% 1.43/0.97      | ~ v3_orders_2(X1)
% 1.43/0.97      | ~ v5_orders_2(X1)
% 1.43/0.97      | ~ l1_orders_2(X1)
% 1.43/0.97      | sK1 != X1
% 1.43/0.97      | k1_xboole_0 = X2 ),
% 1.43/0.97      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_367,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.43/0.97      | v2_struct_0(sK1)
% 1.43/0.97      | ~ v3_orders_2(sK1)
% 1.43/0.97      | ~ v5_orders_2(sK1)
% 1.43/0.97      | ~ l1_orders_2(sK1)
% 1.43/0.97      | k1_xboole_0 = X1 ),
% 1.43/0.97      inference(unflattening,[status(thm)],[c_366]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_19,negated_conjecture,
% 1.43/0.97      ( ~ v2_struct_0(sK1) ),
% 1.43/0.97      inference(cnf_transformation,[],[f33]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_18,negated_conjecture,
% 1.43/0.97      ( v3_orders_2(sK1) ),
% 1.43/0.97      inference(cnf_transformation,[],[f34]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_16,negated_conjecture,
% 1.43/0.97      ( v5_orders_2(sK1) ),
% 1.43/0.97      inference(cnf_transformation,[],[f36]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_15,negated_conjecture,
% 1.43/0.97      ( l1_orders_2(sK1) ),
% 1.43/0.97      inference(cnf_transformation,[],[f37]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_371,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.43/0.97      | k1_xboole_0 = X1 ),
% 1.43/0.97      inference(global_propositional_subsumption,
% 1.43/0.97                [status(thm)],
% 1.43/0.97                [c_367,c_19,c_18,c_16,c_15]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1125,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.43/0.97      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | m1_subset_1(sK0(sK1,X1_45,X0_45),u1_struct_0(sK1))
% 1.43/0.97      | k1_xboole_0 = X1_45 ),
% 1.43/0.97      inference(subtyping,[status(esa)],[c_371]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1483,plain,
% 1.43/0.97      ( k1_xboole_0 = X0_45
% 1.43/0.97      | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
% 1.43/0.97      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.97      | m1_subset_1(sK0(sK1,X0_45,X1_45),u1_struct_0(sK1)) = iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_1125]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_14,negated_conjecture,
% 1.43/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1130,negated_conjecture,
% 1.43/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.97      inference(subtyping,[status(esa)],[c_14]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1478,plain,
% 1.43/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_1130]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_3,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | v2_struct_0(X1)
% 1.43/0.97      | ~ v3_orders_2(X1)
% 1.43/0.97      | ~ v4_orders_2(X1)
% 1.43/0.97      | ~ v5_orders_2(X1)
% 1.43/0.97      | ~ l1_orders_2(X1)
% 1.43/0.97      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.43/0.97      | k1_xboole_0 = X2 ),
% 1.43/0.97      inference(cnf_transformation,[],[f25]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_420,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.97      | v2_struct_0(X1)
% 1.43/0.97      | ~ v3_orders_2(X1)
% 1.43/0.97      | ~ v5_orders_2(X1)
% 1.43/0.97      | ~ l1_orders_2(X1)
% 1.43/0.97      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.43/0.97      | sK1 != X1
% 1.43/0.97      | k1_xboole_0 = X2 ),
% 1.43/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_17]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_421,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | v2_struct_0(sK1)
% 1.43/0.97      | ~ v3_orders_2(sK1)
% 1.43/0.97      | ~ v5_orders_2(sK1)
% 1.43/0.97      | ~ l1_orders_2(sK1)
% 1.43/0.97      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.43/0.97      | k1_xboole_0 = X1 ),
% 1.43/0.97      inference(unflattening,[status(thm)],[c_420]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_425,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.43/0.97      | k1_xboole_0 = X1 ),
% 1.43/0.97      inference(global_propositional_subsumption,
% 1.43/0.97                [status(thm)],
% 1.43/0.97                [c_421,c_19,c_18,c_16,c_15]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1123,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.43/0.97      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | k3_orders_2(sK1,X1_45,sK0(sK1,X1_45,X0_45)) = X0_45
% 1.43/0.97      | k1_xboole_0 = X1_45 ),
% 1.43/0.97      inference(subtyping,[status(esa)],[c_425]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1485,plain,
% 1.43/0.97      ( k3_orders_2(sK1,X0_45,sK0(sK1,X0_45,X1_45)) = X1_45
% 1.43/0.97      | k1_xboole_0 = X0_45
% 1.43/0.97      | m1_orders_2(X1_45,sK1,X0_45) != iProver_top
% 1.43/0.97      | m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_1123]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1933,plain,
% 1.43/0.97      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
% 1.43/0.97      | sK2 = k1_xboole_0
% 1.43/0.97      | m1_orders_2(X0_45,sK1,sK2) != iProver_top
% 1.43/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.97      inference(superposition,[status(thm)],[c_1478,c_1485]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_25,plain,
% 1.43/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_0,plain,
% 1.43/0.97      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
% 1.43/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.97      | v2_struct_0(X0)
% 1.43/0.97      | ~ v3_orders_2(X0)
% 1.43/0.97      | ~ v4_orders_2(X0)
% 1.43/0.97      | ~ v5_orders_2(X0)
% 1.43/0.97      | ~ l1_orders_2(X0) ),
% 1.43/0.97      inference(cnf_transformation,[],[f44]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_352,plain,
% 1.43/0.97      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
% 1.43/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.97      | v2_struct_0(X0)
% 1.43/0.97      | ~ v3_orders_2(X0)
% 1.43/0.97      | ~ v5_orders_2(X0)
% 1.43/0.97      | ~ l1_orders_2(X0)
% 1.43/0.97      | sK1 != X0 ),
% 1.43/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_17]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_353,plain,
% 1.43/0.97      ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.43/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | v2_struct_0(sK1)
% 1.43/0.97      | ~ v3_orders_2(sK1)
% 1.43/0.97      | ~ v5_orders_2(sK1)
% 1.43/0.97      | ~ l1_orders_2(sK1) ),
% 1.43/0.97      inference(unflattening,[status(thm)],[c_352]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_355,plain,
% 1.43/0.97      ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.43/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.43/0.97      inference(global_propositional_subsumption,
% 1.43/0.97                [status(thm)],
% 1.43/0.97                [c_353,c_19,c_18,c_16,c_15]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_13,negated_conjecture,
% 1.43/0.97      ( ~ m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2 ),
% 1.43/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1131,negated_conjecture,
% 1.43/0.97      ( ~ m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2 ),
% 1.43/0.97      inference(subtyping,[status(esa)],[c_13]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1640,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0_45,sK1,sK2)
% 1.43/0.97      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
% 1.43/0.97      | k1_xboole_0 = sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1123]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1641,plain,
% 1.43/0.97      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
% 1.43/0.97      | k1_xboole_0 = sK2
% 1.43/0.97      | m1_orders_2(X0_45,sK1,sK2) != iProver_top
% 1.43/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.97      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_1640]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1137,plain,
% 1.43/0.97      ( ~ m1_subset_1(X0_45,X0_46)
% 1.43/0.97      | m1_subset_1(X1_45,X0_46)
% 1.43/0.97      | X1_45 != X0_45 ),
% 1.43/0.97      theory(equality) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1652,plain,
% 1.43/0.97      ( m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | X0_45 != sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1137]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1654,plain,
% 1.43/0.97      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | k1_xboole_0 != sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1652]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1136,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0_45,X0_44,X1_45)
% 1.43/0.97      | m1_orders_2(X2_45,X0_44,X3_45)
% 1.43/0.97      | X2_45 != X0_45
% 1.43/0.97      | X3_45 != X1_45 ),
% 1.43/0.97      theory(equality) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1738,plain,
% 1.43/0.97      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.43/0.97      | m1_orders_2(sK2,sK1,sK2)
% 1.43/0.97      | sK2 != X0_45
% 1.43/0.97      | sK2 != X1_45 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1136]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1740,plain,
% 1.43/0.97      ( m1_orders_2(sK2,sK1,sK2)
% 1.43/0.97      | ~ m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.43/0.97      | sK2 != k1_xboole_0 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1738]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_2019,plain,
% 1.43/0.97      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_45)) = X0_45
% 1.43/0.97      | m1_orders_2(X0_45,sK1,sK2) != iProver_top
% 1.43/0.97      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.97      inference(global_propositional_subsumption,
% 1.43/0.97                [status(thm)],
% 1.43/0.97                [c_1933,c_14,c_25,c_355,c_1131,c_1641,c_1654,c_1740]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_2028,plain,
% 1.43/0.97      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
% 1.43/0.97      | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
% 1.43/0.97      inference(superposition,[status(thm)],[c_1478,c_2019]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_10,negated_conjecture,
% 1.43/0.97      ( m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 = sK2 ),
% 1.43/0.97      inference(cnf_transformation,[],[f42]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1132,negated_conjecture,
% 1.43/0.97      ( m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 = sK2 ),
% 1.43/0.97      inference(subtyping,[status(esa)],[c_10]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1146,plain,
% 1.43/0.97      ( k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.43/0.97      inference(predicate_to_equality,[status(thm)],[c_1132]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1134,plain,( X0_45 = X0_45 ),theory(equality) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1696,plain,
% 1.43/0.97      ( sK2 = sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1134]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1135,plain,
% 1.43/0.97      ( X0_45 != X1_45 | X2_45 != X1_45 | X2_45 = X0_45 ),
% 1.43/0.97      theory(equality) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1669,plain,
% 1.43/0.97      ( X0_45 != X1_45 | sK2 != X1_45 | sK2 = X0_45 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1135]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1734,plain,
% 1.43/0.97      ( X0_45 != sK2 | sK2 = X0_45 | sK2 != sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1669]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_1735,plain,
% 1.43/0.97      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.43/0.97      inference(instantiation,[status(thm)],[c_1734]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_2029,plain,
% 1.43/0.97      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.43/0.97      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
% 1.43/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2028]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_2031,plain,
% 1.43/0.97      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
% 1.43/0.97      inference(global_propositional_subsumption,
% 1.43/0.97                [status(thm)],
% 1.43/0.97                [c_2028,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,
% 1.43/0.97                 c_1686,c_1696,c_1735,c_1740]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_9,plain,
% 1.43/0.97      ( r2_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 1.43/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.43/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.97      | v2_struct_0(X0)
% 1.43/0.97      | ~ v3_orders_2(X0)
% 1.43/0.97      | ~ v4_orders_2(X0)
% 1.43/0.97      | ~ v5_orders_2(X0)
% 1.43/0.97      | ~ l1_orders_2(X0) ),
% 1.43/0.97      inference(cnf_transformation,[],[f30]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_265,plain,
% 1.43/0.97      ( r2_orders_2(X0,X1,X2)
% 1.43/0.97      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 1.43/0.97      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.97      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.97      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.43/0.97      | v2_struct_0(X0)
% 1.43/0.97      | ~ v3_orders_2(X0)
% 1.43/0.97      | ~ v5_orders_2(X0)
% 1.43/0.97      | ~ l1_orders_2(X0)
% 1.43/0.97      | sK1 != X0 ),
% 1.43/0.97      inference(resolution_lifted,[status(thm)],[c_9,c_17]) ).
% 1.43/0.97  
% 1.43/0.97  cnf(c_266,plain,
% 1.43/0.97      ( r2_orders_2(sK1,X0,X1)
% 1.43/0.97      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 1.43/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.97      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.43/0.97      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.97      | v2_struct_0(sK1)
% 1.43/0.97      | ~ v3_orders_2(sK1)
% 1.43/0.97      | ~ v5_orders_2(sK1)
% 1.43/0.97      | ~ l1_orders_2(sK1) ),
% 1.43/0.98      inference(unflattening,[status(thm)],[c_265]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_270,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0,X1)
% 1.43/0.98      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 1.43/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_266,c_19,c_18,c_16,c_15]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_271,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0,X1)
% 1.43/0.98      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 1.43/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_270]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1129,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,X1_45)
% 1.43/0.98      | ~ r2_hidden(X0_45,k3_orders_2(sK1,X2_45,X1_45))
% 1.43/0.98      | ~ m1_subset_1(X2_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
% 1.43/0.98      inference(subtyping,[status(esa)],[c_271]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1479,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,X1_45) = iProver_top
% 1.43/0.98      | r2_hidden(X0_45,k3_orders_2(sK1,X2_45,X1_45)) != iProver_top
% 1.43/0.98      | m1_subset_1(X2_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1129]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2036,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(superposition,[status(thm)],[c_2031,c_1479]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2143,plain,
% 1.43/0.98      ( m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_2036,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,
% 1.43/0.98                 c_1680,c_1696,c_1735,c_1740]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2144,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_2143]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2153,plain,
% 1.43/0.98      ( sK2 = k1_xboole_0
% 1.43/0.98      | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
% 1.43/0.98      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(superposition,[status(thm)],[c_1483,c_2144]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1145,plain,
% 1.43/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1134]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1147,plain,
% 1.43/0.98      ( k1_xboole_0 != sK2 | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1131]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1650,plain,
% 1.43/0.98      ( sK2 != X0_45 | k1_xboole_0 != X0_45 | k1_xboole_0 = sK2 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1135]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1651,plain,
% 1.43/0.98      ( sK2 != k1_xboole_0
% 1.43/0.98      | k1_xboole_0 = sK2
% 1.43/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1650]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2,plain,
% 1.43/0.98      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 1.43/0.98      | ~ r2_hidden(X2,X1)
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.98      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.98      | v2_struct_0(X0)
% 1.43/0.98      | ~ v3_orders_2(X0)
% 1.43/0.98      | ~ v4_orders_2(X0)
% 1.43/0.98      | ~ v5_orders_2(X0)
% 1.43/0.98      | ~ l1_orders_2(X0)
% 1.43/0.98      | k1_xboole_0 = X1 ),
% 1.43/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_322,plain,
% 1.43/0.98      ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
% 1.43/0.98      | ~ r2_hidden(X2,X1)
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.98      | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
% 1.43/0.98      | v2_struct_0(X0)
% 1.43/0.98      | ~ v3_orders_2(X0)
% 1.43/0.98      | ~ v5_orders_2(X0)
% 1.43/0.98      | ~ l1_orders_2(X0)
% 1.43/0.98      | sK1 != X0
% 1.43/0.98      | k1_xboole_0 = X1 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_17]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_323,plain,
% 1.43/0.98      ( m1_orders_2(k3_orders_2(sK1,X0,X1),sK1,X0)
% 1.43/0.98      | ~ r2_hidden(X1,X0)
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(k3_orders_2(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | v2_struct_0(sK1)
% 1.43/0.98      | ~ v3_orders_2(sK1)
% 1.43/0.98      | ~ v5_orders_2(sK1)
% 1.43/0.98      | ~ l1_orders_2(sK1)
% 1.43/0.98      | k1_xboole_0 = X0 ),
% 1.43/0.98      inference(unflattening,[status(thm)],[c_322]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_327,plain,
% 1.43/0.98      ( m1_orders_2(k3_orders_2(sK1,X0,X1),sK1,X0)
% 1.43/0.98      | ~ r2_hidden(X1,X0)
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(k3_orders_2(sK1,X0,X1),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = X0 ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_323,c_19,c_18,c_16,c_15]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1127,plain,
% 1.43/0.98      ( m1_orders_2(k3_orders_2(sK1,X0_45,X1_45),sK1,X0_45)
% 1.43/0.98      | ~ r2_hidden(X1_45,X0_45)
% 1.43/0.98      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(k3_orders_2(sK1,X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = X0_45 ),
% 1.43/0.98      inference(subtyping,[status(esa)],[c_327]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1481,plain,
% 1.43/0.98      ( k1_xboole_0 = X0_45
% 1.43/0.98      | m1_orders_2(k3_orders_2(sK1,X0_45,X1_45),sK1,X0_45) = iProver_top
% 1.43/0.98      | r2_hidden(X1_45,X0_45) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.43/0.98      | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(k3_orders_2(sK1,X0_45,X1_45),k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1127]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2139,plain,
% 1.43/0.98      ( sK2 = k1_xboole_0
% 1.43/0.98      | m1_orders_2(k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)),sK1,sK2) = iProver_top
% 1.43/0.98      | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(superposition,[status(thm)],[c_2031,c_1481]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2140,plain,
% 1.43/0.98      ( sK2 = k1_xboole_0
% 1.43/0.98      | m1_orders_2(sK2,sK1,sK2) = iProver_top
% 1.43/0.98      | r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(light_normalisation,[status(thm)],[c_2139,c_2031]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_28,plain,
% 1.43/0.98      ( k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2246,plain,
% 1.43/0.98      ( m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_2140,c_14,c_13,c_28,c_355,c_1146,c_1654,c_1696,c_1735,
% 1.43/0.98                 c_1740]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2252,plain,
% 1.43/0.98      ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_2153,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,
% 1.43/0.98                 c_1680,c_1696,c_1735,c_1740,c_2036]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2253,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,sK0(sK1,sK2,sK2)) = iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_2252]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_6,plain,
% 1.43/0.98      ( ~ r2_orders_2(X0,X1,X2)
% 1.43/0.98      | ~ r2_orders_2(X0,X2,X1)
% 1.43/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.43/0.98      | ~ v5_orders_2(X0)
% 1.43/0.98      | ~ l1_orders_2(X0) ),
% 1.43/0.98      inference(cnf_transformation,[],[f29]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_550,plain,
% 1.43/0.98      ( ~ r2_orders_2(X0,X1,X2)
% 1.43/0.98      | ~ r2_orders_2(X0,X2,X1)
% 1.43/0.98      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.43/0.98      | ~ v5_orders_2(X0)
% 1.43/0.98      | sK1 != X0 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_551,plain,
% 1.43/0.98      ( ~ r2_orders_2(sK1,X0,X1)
% 1.43/0.98      | ~ r2_orders_2(sK1,X1,X0)
% 1.43/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ v5_orders_2(sK1) ),
% 1.43/0.98      inference(unflattening,[status(thm)],[c_550]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_555,plain,
% 1.43/0.98      ( ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.43/0.98      | ~ r2_orders_2(sK1,X1,X0)
% 1.43/0.98      | ~ r2_orders_2(sK1,X0,X1) ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_551,c_16]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_556,plain,
% 1.43/0.98      ( ~ r2_orders_2(sK1,X0,X1)
% 1.43/0.98      | ~ r2_orders_2(sK1,X1,X0)
% 1.43/0.98      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_555]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1120,plain,
% 1.43/0.98      ( ~ r2_orders_2(sK1,X0_45,X1_45)
% 1.43/0.98      | ~ r2_orders_2(sK1,X1_45,X0_45)
% 1.43/0.98      | ~ m1_subset_1(X1_45,u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(X0_45,u1_struct_0(sK1)) ),
% 1.43/0.98      inference(subtyping,[status(esa)],[c_556]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1488,plain,
% 1.43/0.98      ( r2_orders_2(sK1,X0_45,X1_45) != iProver_top
% 1.43/0.98      | r2_orders_2(sK1,X1_45,X0_45) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(X1_45,u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1120]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2261,plain,
% 1.43/0.98      ( r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(superposition,[status(thm)],[c_2253,c_1488]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1625,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0_45,sK1,sK2)
% 1.43/0.98      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,X0_45),u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = sK2 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1125]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1679,plain,
% 1.43/0.98      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1))
% 1.43/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = sK2 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1625]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1680,plain,
% 1.43/0.98      ( k1_xboole_0 = sK2
% 1.43/0.98      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) = iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1679]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2318,plain,
% 1.43/0.98      ( m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_2261,c_14,c_25,c_13,c_28,c_355,c_1146,c_1147,c_1654,
% 1.43/0.98                 c_1680,c_1696,c_1735,c_1740]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2319,plain,
% 1.43/0.98      ( r2_orders_2(sK1,sK0(sK1,sK2,sK2),X0_45) != iProver_top
% 1.43/0.98      | r2_hidden(X0_45,sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(X0_45,u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(renaming,[status(thm)],[c_2318]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_2327,plain,
% 1.43/0.98      ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
% 1.43/0.98      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top ),
% 1.43/0.98      inference(superposition,[status(thm)],[c_2253,c_2319]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_4,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.98      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | ~ v3_orders_2(X1)
% 1.43/0.98      | ~ v4_orders_2(X1)
% 1.43/0.98      | ~ v5_orders_2(X1)
% 1.43/0.98      | ~ l1_orders_2(X1)
% 1.43/0.98      | k1_xboole_0 = X2 ),
% 1.43/0.98      inference(cnf_transformation,[],[f24]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_393,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0,X1,X2)
% 1.43/0.98      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.43/0.98      | v2_struct_0(X1)
% 1.43/0.98      | ~ v3_orders_2(X1)
% 1.43/0.98      | ~ v5_orders_2(X1)
% 1.43/0.98      | ~ l1_orders_2(X1)
% 1.43/0.98      | sK1 != X1
% 1.43/0.98      | k1_xboole_0 = X2 ),
% 1.43/0.98      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_394,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.98      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | v2_struct_0(sK1)
% 1.43/0.98      | ~ v3_orders_2(sK1)
% 1.43/0.98      | ~ v5_orders_2(sK1)
% 1.43/0.98      | ~ l1_orders_2(sK1)
% 1.43/0.98      | k1_xboole_0 = X1 ),
% 1.43/0.98      inference(unflattening,[status(thm)],[c_393]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_398,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0,sK1,X1)
% 1.43/0.98      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.43/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = X1 ),
% 1.43/0.98      inference(global_propositional_subsumption,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_394,c_19,c_18,c_16,c_15]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1124,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0_45,sK1,X1_45)
% 1.43/0.98      | r2_hidden(sK0(sK1,X1_45,X0_45),X1_45)
% 1.43/0.98      | ~ m1_subset_1(X1_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = X1_45 ),
% 1.43/0.98      inference(subtyping,[status(esa)],[c_398]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1630,plain,
% 1.43/0.98      ( ~ m1_orders_2(X0_45,sK1,sK2)
% 1.43/0.98      | r2_hidden(sK0(sK1,sK2,X0_45),sK2)
% 1.43/0.98      | ~ m1_subset_1(X0_45,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = sK2 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1124]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1682,plain,
% 1.43/0.98      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.43/0.98      | r2_hidden(sK0(sK1,sK2,sK2),sK2)
% 1.43/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.43/0.98      | k1_xboole_0 = sK2 ),
% 1.43/0.98      inference(instantiation,[status(thm)],[c_1630]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(c_1683,plain,
% 1.43/0.98      ( k1_xboole_0 = sK2
% 1.43/0.98      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.43/0.98      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 1.43/0.98      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.43/0.98      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 1.43/0.98  
% 1.43/0.98  cnf(contradiction,plain,
% 1.43/0.98      ( $false ),
% 1.43/0.98      inference(minisat,
% 1.43/0.98                [status(thm)],
% 1.43/0.98                [c_2327,c_2246,c_1683,c_1680,c_1147,c_25]) ).
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.43/0.98  
% 1.43/0.98  ------                               Statistics
% 1.43/0.98  
% 1.43/0.98  ------ General
% 1.43/0.98  
% 1.43/0.98  abstr_ref_over_cycles:                  0
% 1.43/0.98  abstr_ref_under_cycles:                 0
% 1.43/0.98  gc_basic_clause_elim:                   0
% 1.43/0.98  forced_gc_time:                         0
% 1.43/0.98  parsing_time:                           0.011
% 1.43/0.98  unif_index_cands_time:                  0.
% 1.43/0.98  unif_index_add_time:                    0.
% 1.43/0.98  orderings_time:                         0.
% 1.43/0.98  out_proof_time:                         0.013
% 1.43/0.98  total_time:                             0.107
% 1.43/0.98  num_of_symbols:                         47
% 1.43/0.98  num_of_terms:                           1570
% 1.43/0.98  
% 1.43/0.98  ------ Preprocessing
% 1.43/0.98  
% 1.43/0.98  num_of_splits:                          0
% 1.43/0.98  num_of_split_atoms:                     0
% 1.43/0.98  num_of_reused_defs:                     0
% 1.43/0.98  num_eq_ax_congr_red:                    25
% 1.43/0.98  num_of_sem_filtered_clauses:            1
% 1.43/0.98  num_of_subtypes:                        3
% 1.43/0.98  monotx_restored_types:                  0
% 1.43/0.98  sat_num_of_epr_types:                   0
% 1.43/0.98  sat_num_of_non_cyclic_types:            0
% 1.43/0.98  sat_guarded_non_collapsed_types:        1
% 1.43/0.98  num_pure_diseq_elim:                    0
% 1.43/0.98  simp_replaced_by:                       0
% 1.43/0.98  res_preprocessed:                       70
% 1.43/0.98  prep_upred:                             0
% 1.43/0.98  prep_unflattend:                        56
% 1.43/0.98  smt_new_axioms:                         0
% 1.43/0.98  pred_elim_cands:                        4
% 1.43/0.98  pred_elim:                              5
% 1.43/0.98  pred_elim_cl:                           5
% 1.43/0.98  pred_elim_cycles:                       7
% 1.43/0.98  merged_defs:                            8
% 1.43/0.98  merged_defs_ncl:                        0
% 1.43/0.98  bin_hyper_res:                          8
% 1.43/0.98  prep_cycles:                            4
% 1.43/0.98  pred_elim_time:                         0.015
% 1.43/0.98  splitting_time:                         0.
% 1.43/0.98  sem_filter_time:                        0.
% 1.43/0.98  monotx_time:                            0.
% 1.43/0.98  subtype_inf_time:                       0.
% 1.43/0.98  
% 1.43/0.98  ------ Problem properties
% 1.43/0.98  
% 1.43/0.98  clauses:                                13
% 1.43/0.98  conjectures:                            3
% 1.43/0.98  epr:                                    2
% 1.43/0.98  horn:                                   8
% 1.43/0.98  ground:                                 4
% 1.43/0.98  unary:                                  1
% 1.43/0.98  binary:                                 3
% 1.43/0.98  lits:                                   52
% 1.43/0.98  lits_eq:                                8
% 1.43/0.98  fd_pure:                                0
% 1.43/0.98  fd_pseudo:                              0
% 1.43/0.98  fd_cond:                                4
% 1.43/0.98  fd_pseudo_cond:                         0
% 1.43/0.98  ac_symbols:                             0
% 1.43/0.98  
% 1.43/0.98  ------ Propositional Solver
% 1.43/0.98  
% 1.43/0.98  prop_solver_calls:                      27
% 1.43/0.98  prop_fast_solver_calls:                 924
% 1.43/0.98  smt_solver_calls:                       0
% 1.43/0.98  smt_fast_solver_calls:                  0
% 1.43/0.98  prop_num_of_clauses:                    521
% 1.43/0.98  prop_preprocess_simplified:             2308
% 1.43/0.98  prop_fo_subsumed:                       56
% 1.43/0.98  prop_solver_time:                       0.
% 1.43/0.98  smt_solver_time:                        0.
% 1.43/0.98  smt_fast_solver_time:                   0.
% 1.43/0.98  prop_fast_solver_time:                  0.
% 1.43/0.98  prop_unsat_core_time:                   0.
% 1.43/0.98  
% 1.43/0.98  ------ QBF
% 1.43/0.98  
% 1.43/0.98  qbf_q_res:                              0
% 1.43/0.98  qbf_num_tautologies:                    0
% 1.43/0.98  qbf_prep_cycles:                        0
% 1.43/0.98  
% 1.43/0.98  ------ BMC1
% 1.43/0.98  
% 1.43/0.98  bmc1_current_bound:                     -1
% 1.43/0.98  bmc1_last_solved_bound:                 -1
% 1.43/0.98  bmc1_unsat_core_size:                   -1
% 1.43/0.98  bmc1_unsat_core_parents_size:           -1
% 1.43/0.98  bmc1_merge_next_fun:                    0
% 1.43/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.43/0.98  
% 1.43/0.98  ------ Instantiation
% 1.43/0.98  
% 1.43/0.98  inst_num_of_clauses:                    119
% 1.43/0.98  inst_num_in_passive:                    7
% 1.43/0.98  inst_num_in_active:                     77
% 1.43/0.98  inst_num_in_unprocessed:                35
% 1.43/0.98  inst_num_of_loops:                      100
% 1.43/0.98  inst_num_of_learning_restarts:          0
% 1.43/0.98  inst_num_moves_active_passive:          18
% 1.43/0.98  inst_lit_activity:                      0
% 1.43/0.98  inst_lit_activity_moves:                0
% 1.43/0.98  inst_num_tautologies:                   0
% 1.43/0.98  inst_num_prop_implied:                  0
% 1.43/0.98  inst_num_existing_simplified:           0
% 1.43/0.98  inst_num_eq_res_simplified:             0
% 1.43/0.98  inst_num_child_elim:                    0
% 1.43/0.98  inst_num_of_dismatching_blockings:      4
% 1.43/0.98  inst_num_of_non_proper_insts:           114
% 1.43/0.98  inst_num_of_duplicates:                 0
% 1.43/0.98  inst_inst_num_from_inst_to_res:         0
% 1.43/0.98  inst_dismatching_checking_time:         0.
% 1.43/0.98  
% 1.43/0.98  ------ Resolution
% 1.43/0.98  
% 1.43/0.98  res_num_of_clauses:                     0
% 1.43/0.98  res_num_in_passive:                     0
% 1.43/0.98  res_num_in_active:                      0
% 1.43/0.98  res_num_of_loops:                       74
% 1.43/0.98  res_forward_subset_subsumed:            7
% 1.43/0.98  res_backward_subset_subsumed:           0
% 1.43/0.98  res_forward_subsumed:                   0
% 1.43/0.98  res_backward_subsumed:                  0
% 1.43/0.98  res_forward_subsumption_resolution:     0
% 1.43/0.98  res_backward_subsumption_resolution:    0
% 1.43/0.98  res_clause_to_clause_subsumption:       29
% 1.43/0.98  res_orphan_elimination:                 0
% 1.43/0.98  res_tautology_del:                      44
% 1.43/0.98  res_num_eq_res_simplified:              0
% 1.43/0.98  res_num_sel_changes:                    0
% 1.43/0.98  res_moves_from_active_to_pass:          0
% 1.43/0.98  
% 1.43/0.98  ------ Superposition
% 1.43/0.98  
% 1.43/0.98  sup_time_total:                         0.
% 1.43/0.98  sup_time_generating:                    0.
% 1.43/0.98  sup_time_sim_full:                      0.
% 1.43/0.98  sup_time_sim_immed:                     0.
% 1.43/0.98  
% 1.43/0.98  sup_num_of_clauses:                     21
% 1.43/0.98  sup_num_in_active:                      18
% 1.43/0.98  sup_num_in_passive:                     3
% 1.43/0.98  sup_num_of_loops:                       18
% 1.43/0.98  sup_fw_superposition:                   5
% 1.43/0.98  sup_bw_superposition:                   8
% 1.43/0.98  sup_immediate_simplified:               1
% 1.43/0.98  sup_given_eliminated:                   0
% 1.43/0.98  comparisons_done:                       0
% 1.43/0.98  comparisons_avoided:                    1
% 1.43/0.98  
% 1.43/0.98  ------ Simplifications
% 1.43/0.98  
% 1.43/0.98  
% 1.43/0.98  sim_fw_subset_subsumed:                 0
% 1.43/0.98  sim_bw_subset_subsumed:                 1
% 1.43/0.98  sim_fw_subsumed:                        0
% 1.43/0.98  sim_bw_subsumed:                        0
% 1.43/0.98  sim_fw_subsumption_res:                 0
% 1.43/0.98  sim_bw_subsumption_res:                 0
% 1.43/0.98  sim_tautology_del:                      4
% 1.43/0.98  sim_eq_tautology_del:                   0
% 1.43/0.98  sim_eq_res_simp:                        0
% 1.43/0.98  sim_fw_demodulated:                     0
% 1.43/0.98  sim_bw_demodulated:                     0
% 1.43/0.98  sim_light_normalised:                   1
% 1.43/0.98  sim_joinable_taut:                      0
% 1.43/0.98  sim_joinable_simp:                      0
% 1.43/0.98  sim_ac_normalised:                      0
% 1.43/0.98  sim_smt_subsumption:                    0
% 1.43/0.98  
%------------------------------------------------------------------------------
