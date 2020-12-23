%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:02 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1925)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
        & r2_hidden(sK0(X0,X1,X2),X2)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2)
                    & r2_hidden(sK0(X0,X1,X2),X2)
                    & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5))
        & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))
    & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f34,f33])).

fof(f56,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f53,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f55,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
     => m2_orders_2(sK2(X0,X1),X0,X1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK2(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m2_orders_2(sK2(X0,X1),X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X3] :
                    ( ( r2_hidden(X3,X2)
                      | ~ m2_orders_2(X3,X0,X1) )
                    & ( m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ? [X3] :
                    ( ( ~ m2_orders_2(X3,X0,X1)
                      | ~ r2_hidden(X3,X2) )
                    & ( m2_orders_2(X3,X0,X1)
                      | r2_hidden(X3,X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK1(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK1(X0,X1,X2),X0,X1)
                    | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
              & ( ! [X4] :
                    ( ( r2_hidden(X4,X2)
                      | ~ m2_orders_2(X4,X0,X1) )
                    & ( m2_orders_2(X4,X0,X1)
                      | ~ r2_hidden(X4,X2) ) )
                | k4_orders_2(X0,X1) != X2 ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ m2_orders_2(X4,X0,X1)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m2_orders_2(X4,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f58,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X1] :
              ( r2_hidden(X1,X0)
              & k1_xboole_0 != X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f8,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f5])).

fof(f17,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f31])).

fof(f49,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_11,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_5,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_376,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(k1_xboole_0,X3,X4)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ v3_orders_2(X1)
    | ~ v3_orders_2(X3)
    | ~ v4_orders_2(X1)
    | ~ v4_orders_2(X3)
    | ~ v5_orders_2(X1)
    | ~ v5_orders_2(X3)
    | ~ l1_orders_2(X1)
    | ~ l1_orders_2(X3)
    | X3 != X1
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_5])).

cnf(c_377,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_10,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_401,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_377,c_10])).

cnf(c_18,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_711,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_401,c_18])).

cnf(c_712,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m2_orders_2(k1_xboole_0,sK4,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_711])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_21,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_19,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_716,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m2_orders_2(k1_xboole_0,sK4,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_712,c_22,c_21,c_20,c_19])).

cnf(c_1842,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_716])).

cnf(c_1843,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_716])).

cnf(c_1929,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m2_orders_2(k1_xboole_0,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1842,c_1925])).

cnf(c_1930,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_1929])).

cnf(c_3190,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,sK5)
    | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_1930])).

cnf(c_12,plain,
    ( m2_orders_2(sK2(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_735,plain,
    ( m2_orders_2(sK2(X0,X1),X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_18])).

cnf(c_736,plain,
    ( m2_orders_2(sK2(sK4,X0),sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_735])).

cnf(c_740,plain,
    ( m2_orders_2(sK2(sK4,X0),sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_736,c_22,c_21,c_20,c_19])).

cnf(c_2152,plain,
    ( m2_orders_2(sK2(sK4,X0),sK4,X0) = iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_740])).

cnf(c_17,negated_conjecture,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2163,plain,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_690,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | r2_hidden(X0,k4_orders_2(X1,X2))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_18])).

cnf(c_691,plain,
    ( ~ m2_orders_2(X0,sK4,X1)
    | r2_hidden(X0,k4_orders_2(sK4,X1))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_690])).

cnf(c_695,plain,
    ( ~ m2_orders_2(X0,sK4,X1)
    | r2_hidden(X0,k4_orders_2(sK4,X1))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_22,c_21,c_20,c_19])).

cnf(c_2156,plain,
    ( m2_orders_2(X0,sK4,X1) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,X1)) = iProver_top
    | m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_2354,plain,
    ( m2_orders_2(X0,sK4,sK5) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2163,c_2156])).

cnf(c_16,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2164,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2613,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_2164])).

cnf(c_2693,plain,
    ( k1_xboole_0 = X0
    | m2_orders_2(X0,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2354,c_2613])).

cnf(c_2705,plain,
    ( sK2(sK4,sK5) = k1_xboole_0
    | m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2152,c_2693])).

cnf(c_1846,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2656,plain,
    ( X0 != X1
    | X0 = sK2(sK4,sK5)
    | sK2(sK4,sK5) != X1 ),
    inference(instantiation,[status(thm)],[c_1846])).

cnf(c_2657,plain,
    ( sK2(sK4,sK5) != k1_xboole_0
    | k1_xboole_0 = sK2(sK4,sK5)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2656])).

cnf(c_1845,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2586,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_1847,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X2)
    | X3 != X0
    | X4 != X1 ),
    theory(equality)).

cnf(c_2361,plain,
    ( m2_orders_2(X0,X1,sK5)
    | ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
    | X0 != sK2(sK4,sK5)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2585,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
    | X0 != sK2(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2361])).

cnf(c_2588,plain,
    ( ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
    | m2_orders_2(k1_xboole_0,sK4,sK5)
    | sK4 != sK4
    | k1_xboole_0 != sK2(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_2309,plain,
    ( m2_orders_2(sK2(sK4,sK5),sK4,sK5)
    | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_1878,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1845])).

cnf(c_28,plain,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3190,c_2705,c_2657,c_2586,c_2588,c_2309,c_1878,c_28,c_17])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:07:02 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.50/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.50/0.98  
% 1.50/0.98  ------  iProver source info
% 1.50/0.98  
% 1.50/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.50/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.50/0.98  git: non_committed_changes: false
% 1.50/0.98  git: last_make_outside_of_git: false
% 1.50/0.98  
% 1.50/0.98  ------ 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options
% 1.50/0.98  
% 1.50/0.98  --out_options                           all
% 1.50/0.98  --tptp_safe_out                         true
% 1.50/0.98  --problem_path                          ""
% 1.50/0.98  --include_path                          ""
% 1.50/0.98  --clausifier                            res/vclausify_rel
% 1.50/0.98  --clausifier_options                    --mode clausify
% 1.50/0.98  --stdin                                 false
% 1.50/0.98  --stats_out                             all
% 1.50/0.98  
% 1.50/0.98  ------ General Options
% 1.50/0.98  
% 1.50/0.98  --fof                                   false
% 1.50/0.98  --time_out_real                         305.
% 1.50/0.98  --time_out_virtual                      -1.
% 1.50/0.98  --symbol_type_check                     false
% 1.50/0.98  --clausify_out                          false
% 1.50/0.98  --sig_cnt_out                           false
% 1.50/0.98  --trig_cnt_out                          false
% 1.50/0.98  --trig_cnt_out_tolerance                1.
% 1.50/0.98  --trig_cnt_out_sk_spl                   false
% 1.50/0.98  --abstr_cl_out                          false
% 1.50/0.98  
% 1.50/0.98  ------ Global Options
% 1.50/0.98  
% 1.50/0.98  --schedule                              default
% 1.50/0.98  --add_important_lit                     false
% 1.50/0.98  --prop_solver_per_cl                    1000
% 1.50/0.98  --min_unsat_core                        false
% 1.50/0.98  --soft_assumptions                      false
% 1.50/0.98  --soft_lemma_size                       3
% 1.50/0.98  --prop_impl_unit_size                   0
% 1.50/0.98  --prop_impl_unit                        []
% 1.50/0.98  --share_sel_clauses                     true
% 1.50/0.98  --reset_solvers                         false
% 1.50/0.98  --bc_imp_inh                            [conj_cone]
% 1.50/0.98  --conj_cone_tolerance                   3.
% 1.50/0.98  --extra_neg_conj                        none
% 1.50/0.98  --large_theory_mode                     true
% 1.50/0.98  --prolific_symb_bound                   200
% 1.50/0.98  --lt_threshold                          2000
% 1.50/0.98  --clause_weak_htbl                      true
% 1.50/0.98  --gc_record_bc_elim                     false
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing Options
% 1.50/0.98  
% 1.50/0.98  --preprocessing_flag                    true
% 1.50/0.98  --time_out_prep_mult                    0.1
% 1.50/0.98  --splitting_mode                        input
% 1.50/0.98  --splitting_grd                         true
% 1.50/0.98  --splitting_cvd                         false
% 1.50/0.98  --splitting_cvd_svl                     false
% 1.50/0.98  --splitting_nvd                         32
% 1.50/0.98  --sub_typing                            true
% 1.50/0.98  --prep_gs_sim                           true
% 1.50/0.98  --prep_unflatten                        true
% 1.50/0.98  --prep_res_sim                          true
% 1.50/0.98  --prep_upred                            true
% 1.50/0.98  --prep_sem_filter                       exhaustive
% 1.50/0.98  --prep_sem_filter_out                   false
% 1.50/0.98  --pred_elim                             true
% 1.50/0.98  --res_sim_input                         true
% 1.50/0.98  --eq_ax_congr_red                       true
% 1.50/0.98  --pure_diseq_elim                       true
% 1.50/0.98  --brand_transform                       false
% 1.50/0.98  --non_eq_to_eq                          false
% 1.50/0.98  --prep_def_merge                        true
% 1.50/0.98  --prep_def_merge_prop_impl              false
% 1.50/0.98  --prep_def_merge_mbd                    true
% 1.50/0.98  --prep_def_merge_tr_red                 false
% 1.50/0.98  --prep_def_merge_tr_cl                  false
% 1.50/0.98  --smt_preprocessing                     true
% 1.50/0.98  --smt_ac_axioms                         fast
% 1.50/0.98  --preprocessed_out                      false
% 1.50/0.98  --preprocessed_stats                    false
% 1.50/0.98  
% 1.50/0.98  ------ Abstraction refinement Options
% 1.50/0.98  
% 1.50/0.98  --abstr_ref                             []
% 1.50/0.98  --abstr_ref_prep                        false
% 1.50/0.98  --abstr_ref_until_sat                   false
% 1.50/0.98  --abstr_ref_sig_restrict                funpre
% 1.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.98  --abstr_ref_under                       []
% 1.50/0.98  
% 1.50/0.98  ------ SAT Options
% 1.50/0.98  
% 1.50/0.98  --sat_mode                              false
% 1.50/0.98  --sat_fm_restart_options                ""
% 1.50/0.98  --sat_gr_def                            false
% 1.50/0.98  --sat_epr_types                         true
% 1.50/0.98  --sat_non_cyclic_types                  false
% 1.50/0.98  --sat_finite_models                     false
% 1.50/0.98  --sat_fm_lemmas                         false
% 1.50/0.98  --sat_fm_prep                           false
% 1.50/0.98  --sat_fm_uc_incr                        true
% 1.50/0.98  --sat_out_model                         small
% 1.50/0.98  --sat_out_clauses                       false
% 1.50/0.98  
% 1.50/0.98  ------ QBF Options
% 1.50/0.98  
% 1.50/0.98  --qbf_mode                              false
% 1.50/0.98  --qbf_elim_univ                         false
% 1.50/0.98  --qbf_dom_inst                          none
% 1.50/0.98  --qbf_dom_pre_inst                      false
% 1.50/0.98  --qbf_sk_in                             false
% 1.50/0.98  --qbf_pred_elim                         true
% 1.50/0.98  --qbf_split                             512
% 1.50/0.98  
% 1.50/0.98  ------ BMC1 Options
% 1.50/0.98  
% 1.50/0.98  --bmc1_incremental                      false
% 1.50/0.98  --bmc1_axioms                           reachable_all
% 1.50/0.98  --bmc1_min_bound                        0
% 1.50/0.98  --bmc1_max_bound                        -1
% 1.50/0.98  --bmc1_max_bound_default                -1
% 1.50/0.98  --bmc1_symbol_reachability              true
% 1.50/0.98  --bmc1_property_lemmas                  false
% 1.50/0.98  --bmc1_k_induction                      false
% 1.50/0.98  --bmc1_non_equiv_states                 false
% 1.50/0.98  --bmc1_deadlock                         false
% 1.50/0.98  --bmc1_ucm                              false
% 1.50/0.98  --bmc1_add_unsat_core                   none
% 1.50/0.98  --bmc1_unsat_core_children              false
% 1.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.98  --bmc1_out_stat                         full
% 1.50/0.98  --bmc1_ground_init                      false
% 1.50/0.98  --bmc1_pre_inst_next_state              false
% 1.50/0.98  --bmc1_pre_inst_state                   false
% 1.50/0.98  --bmc1_pre_inst_reach_state             false
% 1.50/0.98  --bmc1_out_unsat_core                   false
% 1.50/0.98  --bmc1_aig_witness_out                  false
% 1.50/0.98  --bmc1_verbose                          false
% 1.50/0.98  --bmc1_dump_clauses_tptp                false
% 1.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.98  --bmc1_dump_file                        -
% 1.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.98  --bmc1_ucm_extend_mode                  1
% 1.50/0.98  --bmc1_ucm_init_mode                    2
% 1.50/0.98  --bmc1_ucm_cone_mode                    none
% 1.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.98  --bmc1_ucm_relax_model                  4
% 1.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.98  --bmc1_ucm_layered_model                none
% 1.50/0.98  --bmc1_ucm_max_lemma_size               10
% 1.50/0.98  
% 1.50/0.98  ------ AIG Options
% 1.50/0.98  
% 1.50/0.98  --aig_mode                              false
% 1.50/0.98  
% 1.50/0.98  ------ Instantiation Options
% 1.50/0.98  
% 1.50/0.98  --instantiation_flag                    true
% 1.50/0.98  --inst_sos_flag                         false
% 1.50/0.98  --inst_sos_phase                        true
% 1.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel_side                     num_symb
% 1.50/0.98  --inst_solver_per_active                1400
% 1.50/0.98  --inst_solver_calls_frac                1.
% 1.50/0.98  --inst_passive_queue_type               priority_queues
% 1.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.98  --inst_passive_queues_freq              [25;2]
% 1.50/0.98  --inst_dismatching                      true
% 1.50/0.98  --inst_eager_unprocessed_to_passive     true
% 1.50/0.98  --inst_prop_sim_given                   true
% 1.50/0.98  --inst_prop_sim_new                     false
% 1.50/0.98  --inst_subs_new                         false
% 1.50/0.98  --inst_eq_res_simp                      false
% 1.50/0.98  --inst_subs_given                       false
% 1.50/0.98  --inst_orphan_elimination               true
% 1.50/0.98  --inst_learning_loop_flag               true
% 1.50/0.98  --inst_learning_start                   3000
% 1.50/0.98  --inst_learning_factor                  2
% 1.50/0.98  --inst_start_prop_sim_after_learn       3
% 1.50/0.98  --inst_sel_renew                        solver
% 1.50/0.98  --inst_lit_activity_flag                true
% 1.50/0.98  --inst_restr_to_given                   false
% 1.50/0.98  --inst_activity_threshold               500
% 1.50/0.98  --inst_out_proof                        true
% 1.50/0.98  
% 1.50/0.98  ------ Resolution Options
% 1.50/0.98  
% 1.50/0.98  --resolution_flag                       true
% 1.50/0.98  --res_lit_sel                           adaptive
% 1.50/0.98  --res_lit_sel_side                      none
% 1.50/0.98  --res_ordering                          kbo
% 1.50/0.98  --res_to_prop_solver                    active
% 1.50/0.98  --res_prop_simpl_new                    false
% 1.50/0.98  --res_prop_simpl_given                  true
% 1.50/0.98  --res_passive_queue_type                priority_queues
% 1.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.98  --res_passive_queues_freq               [15;5]
% 1.50/0.98  --res_forward_subs                      full
% 1.50/0.98  --res_backward_subs                     full
% 1.50/0.98  --res_forward_subs_resolution           true
% 1.50/0.98  --res_backward_subs_resolution          true
% 1.50/0.98  --res_orphan_elimination                true
% 1.50/0.98  --res_time_limit                        2.
% 1.50/0.98  --res_out_proof                         true
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Options
% 1.50/0.98  
% 1.50/0.98  --superposition_flag                    true
% 1.50/0.98  --sup_passive_queue_type                priority_queues
% 1.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.98  --demod_completeness_check              fast
% 1.50/0.98  --demod_use_ground                      true
% 1.50/0.98  --sup_to_prop_solver                    passive
% 1.50/0.98  --sup_prop_simpl_new                    true
% 1.50/0.98  --sup_prop_simpl_given                  true
% 1.50/0.98  --sup_fun_splitting                     false
% 1.50/0.98  --sup_smt_interval                      50000
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Simplification Setup
% 1.50/0.98  
% 1.50/0.98  --sup_indices_passive                   []
% 1.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_full_bw                           [BwDemod]
% 1.50/0.98  --sup_immed_triv                        [TrivRules]
% 1.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_immed_bw_main                     []
% 1.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  
% 1.50/0.98  ------ Combination Options
% 1.50/0.98  
% 1.50/0.98  --comb_res_mult                         3
% 1.50/0.98  --comb_sup_mult                         2
% 1.50/0.98  --comb_inst_mult                        10
% 1.50/0.98  
% 1.50/0.98  ------ Debug Options
% 1.50/0.98  
% 1.50/0.98  --dbg_backtrace                         false
% 1.50/0.98  --dbg_dump_prop_clauses                 false
% 1.50/0.98  --dbg_dump_prop_clauses_file            -
% 1.50/0.98  --dbg_out_stat                          false
% 1.50/0.98  ------ Parsing...
% 1.50/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 8 0s  sf_e  pe_s  pe_e 
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.50/0.98  ------ Proving...
% 1.50/0.98  ------ Problem Properties 
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  clauses                                 18
% 1.50/0.98  conjectures                             2
% 1.50/0.98  EPR                                     1
% 1.50/0.98  Horn                                    13
% 1.50/0.98  unary                                   3
% 1.50/0.98  binary                                  3
% 1.50/0.98  lits                                    58
% 1.50/0.98  lits eq                                 13
% 1.50/0.98  fd_pure                                 0
% 1.50/0.98  fd_pseudo                               0
% 1.50/0.98  fd_cond                                 4
% 1.50/0.98  fd_pseudo_cond                          2
% 1.50/0.98  AC symbols                              0
% 1.50/0.98  
% 1.50/0.98  ------ Schedule dynamic 5 is on 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  ------ 
% 1.50/0.98  Current options:
% 1.50/0.98  ------ 
% 1.50/0.98  
% 1.50/0.98  ------ Input Options
% 1.50/0.98  
% 1.50/0.98  --out_options                           all
% 1.50/0.98  --tptp_safe_out                         true
% 1.50/0.98  --problem_path                          ""
% 1.50/0.98  --include_path                          ""
% 1.50/0.98  --clausifier                            res/vclausify_rel
% 1.50/0.98  --clausifier_options                    --mode clausify
% 1.50/0.98  --stdin                                 false
% 1.50/0.98  --stats_out                             all
% 1.50/0.98  
% 1.50/0.98  ------ General Options
% 1.50/0.98  
% 1.50/0.98  --fof                                   false
% 1.50/0.98  --time_out_real                         305.
% 1.50/0.98  --time_out_virtual                      -1.
% 1.50/0.98  --symbol_type_check                     false
% 1.50/0.98  --clausify_out                          false
% 1.50/0.98  --sig_cnt_out                           false
% 1.50/0.98  --trig_cnt_out                          false
% 1.50/0.98  --trig_cnt_out_tolerance                1.
% 1.50/0.98  --trig_cnt_out_sk_spl                   false
% 1.50/0.98  --abstr_cl_out                          false
% 1.50/0.98  
% 1.50/0.98  ------ Global Options
% 1.50/0.98  
% 1.50/0.98  --schedule                              default
% 1.50/0.98  --add_important_lit                     false
% 1.50/0.98  --prop_solver_per_cl                    1000
% 1.50/0.98  --min_unsat_core                        false
% 1.50/0.98  --soft_assumptions                      false
% 1.50/0.98  --soft_lemma_size                       3
% 1.50/0.98  --prop_impl_unit_size                   0
% 1.50/0.98  --prop_impl_unit                        []
% 1.50/0.98  --share_sel_clauses                     true
% 1.50/0.98  --reset_solvers                         false
% 1.50/0.98  --bc_imp_inh                            [conj_cone]
% 1.50/0.98  --conj_cone_tolerance                   3.
% 1.50/0.98  --extra_neg_conj                        none
% 1.50/0.98  --large_theory_mode                     true
% 1.50/0.98  --prolific_symb_bound                   200
% 1.50/0.98  --lt_threshold                          2000
% 1.50/0.98  --clause_weak_htbl                      true
% 1.50/0.98  --gc_record_bc_elim                     false
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing Options
% 1.50/0.98  
% 1.50/0.98  --preprocessing_flag                    true
% 1.50/0.98  --time_out_prep_mult                    0.1
% 1.50/0.98  --splitting_mode                        input
% 1.50/0.98  --splitting_grd                         true
% 1.50/0.98  --splitting_cvd                         false
% 1.50/0.98  --splitting_cvd_svl                     false
% 1.50/0.98  --splitting_nvd                         32
% 1.50/0.98  --sub_typing                            true
% 1.50/0.98  --prep_gs_sim                           true
% 1.50/0.98  --prep_unflatten                        true
% 1.50/0.98  --prep_res_sim                          true
% 1.50/0.98  --prep_upred                            true
% 1.50/0.98  --prep_sem_filter                       exhaustive
% 1.50/0.98  --prep_sem_filter_out                   false
% 1.50/0.98  --pred_elim                             true
% 1.50/0.98  --res_sim_input                         true
% 1.50/0.98  --eq_ax_congr_red                       true
% 1.50/0.98  --pure_diseq_elim                       true
% 1.50/0.98  --brand_transform                       false
% 1.50/0.98  --non_eq_to_eq                          false
% 1.50/0.98  --prep_def_merge                        true
% 1.50/0.98  --prep_def_merge_prop_impl              false
% 1.50/0.98  --prep_def_merge_mbd                    true
% 1.50/0.98  --prep_def_merge_tr_red                 false
% 1.50/0.98  --prep_def_merge_tr_cl                  false
% 1.50/0.98  --smt_preprocessing                     true
% 1.50/0.98  --smt_ac_axioms                         fast
% 1.50/0.98  --preprocessed_out                      false
% 1.50/0.98  --preprocessed_stats                    false
% 1.50/0.98  
% 1.50/0.98  ------ Abstraction refinement Options
% 1.50/0.98  
% 1.50/0.98  --abstr_ref                             []
% 1.50/0.98  --abstr_ref_prep                        false
% 1.50/0.98  --abstr_ref_until_sat                   false
% 1.50/0.98  --abstr_ref_sig_restrict                funpre
% 1.50/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.50/0.98  --abstr_ref_under                       []
% 1.50/0.98  
% 1.50/0.98  ------ SAT Options
% 1.50/0.98  
% 1.50/0.98  --sat_mode                              false
% 1.50/0.98  --sat_fm_restart_options                ""
% 1.50/0.98  --sat_gr_def                            false
% 1.50/0.98  --sat_epr_types                         true
% 1.50/0.98  --sat_non_cyclic_types                  false
% 1.50/0.98  --sat_finite_models                     false
% 1.50/0.98  --sat_fm_lemmas                         false
% 1.50/0.98  --sat_fm_prep                           false
% 1.50/0.98  --sat_fm_uc_incr                        true
% 1.50/0.98  --sat_out_model                         small
% 1.50/0.98  --sat_out_clauses                       false
% 1.50/0.98  
% 1.50/0.98  ------ QBF Options
% 1.50/0.98  
% 1.50/0.98  --qbf_mode                              false
% 1.50/0.98  --qbf_elim_univ                         false
% 1.50/0.98  --qbf_dom_inst                          none
% 1.50/0.98  --qbf_dom_pre_inst                      false
% 1.50/0.98  --qbf_sk_in                             false
% 1.50/0.98  --qbf_pred_elim                         true
% 1.50/0.98  --qbf_split                             512
% 1.50/0.98  
% 1.50/0.98  ------ BMC1 Options
% 1.50/0.98  
% 1.50/0.98  --bmc1_incremental                      false
% 1.50/0.98  --bmc1_axioms                           reachable_all
% 1.50/0.98  --bmc1_min_bound                        0
% 1.50/0.98  --bmc1_max_bound                        -1
% 1.50/0.98  --bmc1_max_bound_default                -1
% 1.50/0.98  --bmc1_symbol_reachability              true
% 1.50/0.98  --bmc1_property_lemmas                  false
% 1.50/0.98  --bmc1_k_induction                      false
% 1.50/0.98  --bmc1_non_equiv_states                 false
% 1.50/0.98  --bmc1_deadlock                         false
% 1.50/0.98  --bmc1_ucm                              false
% 1.50/0.98  --bmc1_add_unsat_core                   none
% 1.50/0.98  --bmc1_unsat_core_children              false
% 1.50/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.50/0.98  --bmc1_out_stat                         full
% 1.50/0.98  --bmc1_ground_init                      false
% 1.50/0.98  --bmc1_pre_inst_next_state              false
% 1.50/0.98  --bmc1_pre_inst_state                   false
% 1.50/0.98  --bmc1_pre_inst_reach_state             false
% 1.50/0.98  --bmc1_out_unsat_core                   false
% 1.50/0.98  --bmc1_aig_witness_out                  false
% 1.50/0.98  --bmc1_verbose                          false
% 1.50/0.98  --bmc1_dump_clauses_tptp                false
% 1.50/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.50/0.98  --bmc1_dump_file                        -
% 1.50/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.50/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.50/0.98  --bmc1_ucm_extend_mode                  1
% 1.50/0.98  --bmc1_ucm_init_mode                    2
% 1.50/0.98  --bmc1_ucm_cone_mode                    none
% 1.50/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.50/0.98  --bmc1_ucm_relax_model                  4
% 1.50/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.50/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.50/0.98  --bmc1_ucm_layered_model                none
% 1.50/0.98  --bmc1_ucm_max_lemma_size               10
% 1.50/0.98  
% 1.50/0.98  ------ AIG Options
% 1.50/0.98  
% 1.50/0.98  --aig_mode                              false
% 1.50/0.98  
% 1.50/0.98  ------ Instantiation Options
% 1.50/0.98  
% 1.50/0.98  --instantiation_flag                    true
% 1.50/0.98  --inst_sos_flag                         false
% 1.50/0.98  --inst_sos_phase                        true
% 1.50/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.50/0.98  --inst_lit_sel_side                     none
% 1.50/0.98  --inst_solver_per_active                1400
% 1.50/0.98  --inst_solver_calls_frac                1.
% 1.50/0.98  --inst_passive_queue_type               priority_queues
% 1.50/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.50/0.98  --inst_passive_queues_freq              [25;2]
% 1.50/0.98  --inst_dismatching                      true
% 1.50/0.98  --inst_eager_unprocessed_to_passive     true
% 1.50/0.98  --inst_prop_sim_given                   true
% 1.50/0.98  --inst_prop_sim_new                     false
% 1.50/0.98  --inst_subs_new                         false
% 1.50/0.98  --inst_eq_res_simp                      false
% 1.50/0.98  --inst_subs_given                       false
% 1.50/0.98  --inst_orphan_elimination               true
% 1.50/0.98  --inst_learning_loop_flag               true
% 1.50/0.98  --inst_learning_start                   3000
% 1.50/0.98  --inst_learning_factor                  2
% 1.50/0.98  --inst_start_prop_sim_after_learn       3
% 1.50/0.98  --inst_sel_renew                        solver
% 1.50/0.98  --inst_lit_activity_flag                true
% 1.50/0.98  --inst_restr_to_given                   false
% 1.50/0.98  --inst_activity_threshold               500
% 1.50/0.98  --inst_out_proof                        true
% 1.50/0.98  
% 1.50/0.98  ------ Resolution Options
% 1.50/0.98  
% 1.50/0.98  --resolution_flag                       false
% 1.50/0.98  --res_lit_sel                           adaptive
% 1.50/0.98  --res_lit_sel_side                      none
% 1.50/0.98  --res_ordering                          kbo
% 1.50/0.98  --res_to_prop_solver                    active
% 1.50/0.98  --res_prop_simpl_new                    false
% 1.50/0.98  --res_prop_simpl_given                  true
% 1.50/0.98  --res_passive_queue_type                priority_queues
% 1.50/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.50/0.98  --res_passive_queues_freq               [15;5]
% 1.50/0.98  --res_forward_subs                      full
% 1.50/0.98  --res_backward_subs                     full
% 1.50/0.98  --res_forward_subs_resolution           true
% 1.50/0.98  --res_backward_subs_resolution          true
% 1.50/0.98  --res_orphan_elimination                true
% 1.50/0.98  --res_time_limit                        2.
% 1.50/0.98  --res_out_proof                         true
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Options
% 1.50/0.98  
% 1.50/0.98  --superposition_flag                    true
% 1.50/0.98  --sup_passive_queue_type                priority_queues
% 1.50/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.50/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.50/0.98  --demod_completeness_check              fast
% 1.50/0.98  --demod_use_ground                      true
% 1.50/0.98  --sup_to_prop_solver                    passive
% 1.50/0.98  --sup_prop_simpl_new                    true
% 1.50/0.98  --sup_prop_simpl_given                  true
% 1.50/0.98  --sup_fun_splitting                     false
% 1.50/0.98  --sup_smt_interval                      50000
% 1.50/0.98  
% 1.50/0.98  ------ Superposition Simplification Setup
% 1.50/0.98  
% 1.50/0.98  --sup_indices_passive                   []
% 1.50/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.50/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.50/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_full_bw                           [BwDemod]
% 1.50/0.98  --sup_immed_triv                        [TrivRules]
% 1.50/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.50/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_immed_bw_main                     []
% 1.50/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.50/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.50/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.50/0.98  
% 1.50/0.98  ------ Combination Options
% 1.50/0.98  
% 1.50/0.98  --comb_res_mult                         3
% 1.50/0.98  --comb_sup_mult                         2
% 1.50/0.98  --comb_inst_mult                        10
% 1.50/0.98  
% 1.50/0.98  ------ Debug Options
% 1.50/0.98  
% 1.50/0.98  --dbg_backtrace                         false
% 1.50/0.98  --dbg_dump_prop_clauses                 false
% 1.50/0.98  --dbg_dump_prop_clauses_file            -
% 1.50/0.98  --dbg_out_stat                          false
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  ------ Proving...
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  % SZS status Theorem for theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  fof(f3,axiom,(
% 1.50/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f13,plain,(
% 1.50/0.98    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f3])).
% 1.50/0.98  
% 1.50/0.98  fof(f14,plain,(
% 1.50/0.98    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f13])).
% 1.50/0.98  
% 1.50/0.98  fof(f46,plain,(
% 1.50/0.98    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(cnf_transformation,[],[f14])).
% 1.50/0.98  
% 1.50/0.98  fof(f1,axiom,(
% 1.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f9,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f1])).
% 1.50/0.98  
% 1.50/0.98  fof(f10,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f9])).
% 1.50/0.98  
% 1.50/0.98  fof(f20,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(nnf_transformation,[],[f10])).
% 1.50/0.98  
% 1.50/0.98  fof(f21,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f20])).
% 1.50/0.98  
% 1.50/0.98  fof(f22,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(rectify,[],[f21])).
% 1.50/0.98  
% 1.50/0.98  fof(f23,plain,(
% 1.50/0.98    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f24,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK0(X0,X1,X2)))) != sK0(X0,X1,X2) & r2_hidden(sK0(X0,X1,X2),X2) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 1.50/0.98  
% 1.50/0.98  fof(f36,plain,(
% 1.50/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(cnf_transformation,[],[f24])).
% 1.50/0.98  
% 1.50/0.98  fof(f59,plain,(
% 1.50/0.98    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(equality_resolution,[],[f36])).
% 1.50/0.98  
% 1.50/0.98  fof(f47,plain,(
% 1.50/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(cnf_transformation,[],[f14])).
% 1.50/0.98  
% 1.50/0.98  fof(f6,conjecture,(
% 1.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f7,negated_conjecture,(
% 1.50/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.50/0.98    inference(negated_conjecture,[],[f6])).
% 1.50/0.98  
% 1.50/0.98  fof(f18,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f7])).
% 1.50/0.98  
% 1.50/0.98  fof(f19,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f18])).
% 1.50/0.98  
% 1.50/0.98  fof(f34,plain,(
% 1.50/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))))) )),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f33,plain,(
% 1.50/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f35,plain,(
% 1.50/0.98    (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f19,f34,f33])).
% 1.50/0.98  
% 1.50/0.98  fof(f56,plain,(
% 1.50/0.98    l1_orders_2(sK4)),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f52,plain,(
% 1.50/0.98    ~v2_struct_0(sK4)),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f53,plain,(
% 1.50/0.98    v3_orders_2(sK4)),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f54,plain,(
% 1.50/0.98    v4_orders_2(sK4)),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f55,plain,(
% 1.50/0.98    v5_orders_2(sK4)),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f4,axiom,(
% 1.50/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f15,plain,(
% 1.50/0.98    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f4])).
% 1.50/0.98  
% 1.50/0.98  fof(f16,plain,(
% 1.50/0.98    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f15])).
% 1.50/0.98  
% 1.50/0.98  fof(f29,plain,(
% 1.50/0.98    ! [X1,X0] : (? [X2] : m2_orders_2(X2,X0,X1) => m2_orders_2(sK2(X0,X1),X0,X1))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f30,plain,(
% 1.50/0.98    ! [X0,X1] : (m2_orders_2(sK2(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f29])).
% 1.50/0.98  
% 1.50/0.98  fof(f48,plain,(
% 1.50/0.98    ( ! [X0,X1] : (m2_orders_2(sK2(X0,X1),X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(cnf_transformation,[],[f30])).
% 1.50/0.98  
% 1.50/0.98  fof(f57,plain,(
% 1.50/0.98    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f2,axiom,(
% 1.50/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f11,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.50/0.98    inference(ennf_transformation,[],[f2])).
% 1.50/0.98  
% 1.50/0.98  fof(f12,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(flattening,[],[f11])).
% 1.50/0.98  
% 1.50/0.98  fof(f25,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(nnf_transformation,[],[f12])).
% 1.50/0.98  
% 1.50/0.98  fof(f26,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(rectify,[],[f25])).
% 1.50/0.98  
% 1.50/0.98  fof(f27,plain,(
% 1.50/0.98    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f28,plain,(
% 1.50/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK1(X0,X1,X2),X0,X1) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (m2_orders_2(sK1(X0,X1,X2),X0,X1) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 1.50/0.98  
% 1.50/0.98  fof(f43,plain,(
% 1.50/0.98    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(cnf_transformation,[],[f28])).
% 1.50/0.98  
% 1.50/0.98  fof(f60,plain,(
% 1.50/0.98    ( ! [X4,X0,X1] : (r2_hidden(X4,k4_orders_2(X0,X1)) | ~m2_orders_2(X4,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.50/0.98    inference(equality_resolution,[],[f43])).
% 1.50/0.98  
% 1.50/0.98  fof(f58,plain,(
% 1.50/0.98    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))),
% 1.50/0.98    inference(cnf_transformation,[],[f35])).
% 1.50/0.98  
% 1.50/0.98  fof(f5,axiom,(
% 1.50/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.50/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.50/0.98  
% 1.50/0.98  fof(f8,plain,(
% 1.50/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.50/0.98    inference(rectify,[],[f5])).
% 1.50/0.98  
% 1.50/0.98  fof(f17,plain,(
% 1.50/0.98    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.50/0.98    inference(ennf_transformation,[],[f8])).
% 1.50/0.98  
% 1.50/0.98  fof(f31,plain,(
% 1.50/0.98    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)))),
% 1.50/0.98    introduced(choice_axiom,[])).
% 1.50/0.98  
% 1.50/0.98  fof(f32,plain,(
% 1.50/0.98    ! [X0] : (((r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.50/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f31])).
% 1.50/0.98  
% 1.50/0.98  fof(f49,plain,(
% 1.50/0.98    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.50/0.98    inference(cnf_transformation,[],[f32])).
% 1.50/0.98  
% 1.50/0.98  cnf(c_11,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.50/0.98      | v6_orders_2(X0,X1)
% 1.50/0.98      | v2_struct_0(X1)
% 1.50/0.98      | ~ v3_orders_2(X1)
% 1.50/0.98      | ~ v4_orders_2(X1)
% 1.50/0.98      | ~ v5_orders_2(X1)
% 1.50/0.98      | ~ l1_orders_2(X1) ),
% 1.50/0.98      inference(cnf_transformation,[],[f46]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_5,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | ~ v6_orders_2(k1_xboole_0,X0)
% 1.50/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | ~ l1_orders_2(X0) ),
% 1.50/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_376,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,X3,X4)
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.50/0.98      | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
% 1.50/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
% 1.50/0.98      | v2_struct_0(X1)
% 1.50/0.98      | v2_struct_0(X3)
% 1.50/0.98      | ~ v3_orders_2(X1)
% 1.50/0.98      | ~ v3_orders_2(X3)
% 1.50/0.98      | ~ v4_orders_2(X1)
% 1.50/0.98      | ~ v4_orders_2(X3)
% 1.50/0.98      | ~ v5_orders_2(X1)
% 1.50/0.98      | ~ v5_orders_2(X3)
% 1.50/0.98      | ~ l1_orders_2(X1)
% 1.50/0.98      | ~ l1_orders_2(X3)
% 1.50/0.98      | X3 != X1
% 1.50/0.98      | k1_xboole_0 != X0 ),
% 1.50/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_5]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_377,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | ~ l1_orders_2(X0) ),
% 1.50/0.98      inference(unflattening,[status(thm)],[c_376]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_10,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.50/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.50/0.98      | v2_struct_0(X1)
% 1.50/0.98      | ~ v3_orders_2(X1)
% 1.50/0.98      | ~ v4_orders_2(X1)
% 1.50/0.98      | ~ v5_orders_2(X1)
% 1.50/0.98      | ~ l1_orders_2(X1) ),
% 1.50/0.98      inference(cnf_transformation,[],[f47]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_401,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | ~ l1_orders_2(X0) ),
% 1.50/0.98      inference(forward_subsumption_resolution,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_377,c_10]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_18,negated_conjecture,
% 1.50/0.98      ( l1_orders_2(sK4) ),
% 1.50/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_711,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | sK4 != X0 ),
% 1.50/0.98      inference(resolution_lifted,[status(thm)],[c_401,c_18]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_712,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X1)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | v2_struct_0(sK4)
% 1.50/0.98      | ~ v3_orders_2(sK4)
% 1.50/0.98      | ~ v4_orders_2(sK4)
% 1.50/0.98      | ~ v5_orders_2(sK4) ),
% 1.50/0.98      inference(unflattening,[status(thm)],[c_711]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_22,negated_conjecture,
% 1.50/0.98      ( ~ v2_struct_0(sK4) ),
% 1.50/0.98      inference(cnf_transformation,[],[f52]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_21,negated_conjecture,
% 1.50/0.98      ( v3_orders_2(sK4) ),
% 1.50/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_20,negated_conjecture,
% 1.50/0.98      ( v4_orders_2(sK4) ),
% 1.50/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_19,negated_conjecture,
% 1.50/0.98      ( v5_orders_2(sK4) ),
% 1.50/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_716,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X1)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(global_propositional_subsumption,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_712,c_22,c_21,c_20,c_19]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1842,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | ~ sP0_iProver_split ),
% 1.50/0.98      inference(splitting,
% 1.50/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.50/0.98                [c_716]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1843,plain,
% 1.50/0.98      ( sP0_iProver_split ),
% 1.50/0.98      inference(splitting,
% 1.50/0.98                [splitting(split),new_symbols(definition,[])],
% 1.50/0.98                [c_716]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1929,plain,
% 1.50/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X0) ),
% 1.50/0.98      inference(global_propositional_subsumption,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_1842,c_1925]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1930,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(renaming,[status(thm)],[c_1929]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_3190,plain,
% 1.50/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,sK5)
% 1.50/0.98      | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_1930]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_12,plain,
% 1.50/0.98      ( m2_orders_2(sK2(X0,X1),X0,X1)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | ~ l1_orders_2(X0) ),
% 1.50/0.98      inference(cnf_transformation,[],[f48]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_735,plain,
% 1.50/0.98      ( m2_orders_2(sK2(X0,X1),X0,X1)
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.50/0.98      | v2_struct_0(X0)
% 1.50/0.98      | ~ v3_orders_2(X0)
% 1.50/0.98      | ~ v4_orders_2(X0)
% 1.50/0.98      | ~ v5_orders_2(X0)
% 1.50/0.98      | sK4 != X0 ),
% 1.50/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_18]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_736,plain,
% 1.50/0.98      ( m2_orders_2(sK2(sK4,X0),sK4,X0)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | v2_struct_0(sK4)
% 1.50/0.98      | ~ v3_orders_2(sK4)
% 1.50/0.98      | ~ v4_orders_2(sK4)
% 1.50/0.98      | ~ v5_orders_2(sK4) ),
% 1.50/0.98      inference(unflattening,[status(thm)],[c_735]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_740,plain,
% 1.50/0.98      ( m2_orders_2(sK2(sK4,X0),sK4,X0)
% 1.50/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(global_propositional_subsumption,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_736,c_22,c_21,c_20,c_19]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2152,plain,
% 1.50/0.98      ( m2_orders_2(sK2(sK4,X0),sK4,X0) = iProver_top
% 1.50/0.98      | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
% 1.50/0.98      inference(predicate_to_equality,[status(thm)],[c_740]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_17,negated_conjecture,
% 1.50/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(cnf_transformation,[],[f57]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2163,plain,
% 1.50/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
% 1.50/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_8,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.50/0.98      | v2_struct_0(X1)
% 1.50/0.98      | ~ v3_orders_2(X1)
% 1.50/0.98      | ~ v4_orders_2(X1)
% 1.50/0.98      | ~ v5_orders_2(X1)
% 1.50/0.98      | ~ l1_orders_2(X1) ),
% 1.50/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_690,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(X1,X2))
% 1.50/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.50/0.98      | v2_struct_0(X1)
% 1.50/0.98      | ~ v3_orders_2(X1)
% 1.50/0.98      | ~ v4_orders_2(X1)
% 1.50/0.98      | ~ v5_orders_2(X1)
% 1.50/0.98      | sK4 != X1 ),
% 1.50/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_18]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_691,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,sK4,X1)
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(sK4,X1))
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
% 1.50/0.98      | v2_struct_0(sK4)
% 1.50/0.98      | ~ v3_orders_2(sK4)
% 1.50/0.98      | ~ v4_orders_2(sK4)
% 1.50/0.98      | ~ v5_orders_2(sK4) ),
% 1.50/0.98      inference(unflattening,[status(thm)],[c_690]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_695,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,sK4,X1)
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(sK4,X1))
% 1.50/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(global_propositional_subsumption,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_691,c_22,c_21,c_20,c_19]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2156,plain,
% 1.50/0.98      ( m2_orders_2(X0,sK4,X1) != iProver_top
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(sK4,X1)) = iProver_top
% 1.50/0.98      | m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
% 1.50/0.98      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2354,plain,
% 1.50/0.98      ( m2_orders_2(X0,sK4,sK5) != iProver_top
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.50/0.98      inference(superposition,[status(thm)],[c_2163,c_2156]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_16,negated_conjecture,
% 1.50/0.98      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
% 1.50/0.98      inference(cnf_transformation,[],[f58]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_15,plain,
% 1.50/0.98      ( ~ r2_hidden(X0,X1)
% 1.50/0.98      | k3_tarski(X1) != k1_xboole_0
% 1.50/0.98      | k1_xboole_0 = X0 ),
% 1.50/0.98      inference(cnf_transformation,[],[f49]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2164,plain,
% 1.50/0.98      ( k3_tarski(X0) != k1_xboole_0
% 1.50/0.98      | k1_xboole_0 = X1
% 1.50/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 1.50/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2613,plain,
% 1.50/0.98      ( k1_xboole_0 = X0
% 1.50/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.50/0.98      inference(superposition,[status(thm)],[c_16,c_2164]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2693,plain,
% 1.50/0.98      ( k1_xboole_0 = X0 | m2_orders_2(X0,sK4,sK5) != iProver_top ),
% 1.50/0.98      inference(superposition,[status(thm)],[c_2354,c_2613]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2705,plain,
% 1.50/0.98      ( sK2(sK4,sK5) = k1_xboole_0
% 1.50/0.98      | m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) != iProver_top ),
% 1.50/0.98      inference(superposition,[status(thm)],[c_2152,c_2693]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1846,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2656,plain,
% 1.50/0.98      ( X0 != X1 | X0 = sK2(sK4,sK5) | sK2(sK4,sK5) != X1 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_1846]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2657,plain,
% 1.50/0.98      ( sK2(sK4,sK5) != k1_xboole_0
% 1.50/0.98      | k1_xboole_0 = sK2(sK4,sK5)
% 1.50/0.98      | k1_xboole_0 != k1_xboole_0 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_2656]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1845,plain,( X0 = X0 ),theory(equality) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2586,plain,
% 1.50/0.98      ( sK4 = sK4 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_1845]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1847,plain,
% 1.50/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.50/0.98      | m2_orders_2(X3,X4,X2)
% 1.50/0.98      | X3 != X0
% 1.50/0.98      | X4 != X1 ),
% 1.50/0.98      theory(equality) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2361,plain,
% 1.50/0.98      ( m2_orders_2(X0,X1,sK5)
% 1.50/0.98      | ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
% 1.50/0.98      | X0 != sK2(sK4,sK5)
% 1.50/0.98      | X1 != sK4 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_1847]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2585,plain,
% 1.50/0.98      ( m2_orders_2(X0,sK4,sK5)
% 1.50/0.98      | ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
% 1.50/0.98      | X0 != sK2(sK4,sK5)
% 1.50/0.98      | sK4 != sK4 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_2361]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2588,plain,
% 1.50/0.98      ( ~ m2_orders_2(sK2(sK4,sK5),sK4,sK5)
% 1.50/0.98      | m2_orders_2(k1_xboole_0,sK4,sK5)
% 1.50/0.98      | sK4 != sK4
% 1.50/0.98      | k1_xboole_0 != sK2(sK4,sK5) ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_2585]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_2309,plain,
% 1.50/0.98      ( m2_orders_2(sK2(sK4,sK5),sK4,sK5)
% 1.50/0.98      | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_740]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_1878,plain,
% 1.50/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 1.50/0.98      inference(instantiation,[status(thm)],[c_1845]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(c_28,plain,
% 1.50/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
% 1.50/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.50/0.98  
% 1.50/0.98  cnf(contradiction,plain,
% 1.50/0.98      ( $false ),
% 1.50/0.98      inference(minisat,
% 1.50/0.98                [status(thm)],
% 1.50/0.98                [c_3190,c_2705,c_2657,c_2586,c_2588,c_2309,c_1878,c_28,
% 1.50/0.98                 c_17]) ).
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.50/0.98  
% 1.50/0.98  ------                               Statistics
% 1.50/0.98  
% 1.50/0.98  ------ General
% 1.50/0.98  
% 1.50/0.98  abstr_ref_over_cycles:                  0
% 1.50/0.98  abstr_ref_under_cycles:                 0
% 1.50/0.98  gc_basic_clause_elim:                   0
% 1.50/0.98  forced_gc_time:                         0
% 1.50/0.98  parsing_time:                           0.009
% 1.50/0.98  unif_index_cands_time:                  0.
% 1.50/0.98  unif_index_add_time:                    0.
% 1.50/0.98  orderings_time:                         0.
% 1.50/0.98  out_proof_time:                         0.007
% 1.50/0.98  total_time:                             0.122
% 1.50/0.98  num_of_symbols:                         59
% 1.50/0.98  num_of_terms:                           2530
% 1.50/0.98  
% 1.50/0.98  ------ Preprocessing
% 1.50/0.98  
% 1.50/0.98  num_of_splits:                          2
% 1.50/0.98  num_of_split_atoms:                     1
% 1.50/0.98  num_of_reused_defs:                     1
% 1.50/0.98  num_eq_ax_congr_red:                    36
% 1.50/0.98  num_of_sem_filtered_clauses:            2
% 1.50/0.98  num_of_subtypes:                        0
% 1.50/0.98  monotx_restored_types:                  0
% 1.50/0.98  sat_num_of_epr_types:                   0
% 1.50/0.98  sat_num_of_non_cyclic_types:            0
% 1.50/0.98  sat_guarded_non_collapsed_types:        0
% 1.50/0.98  num_pure_diseq_elim:                    0
% 1.50/0.98  simp_replaced_by:                       0
% 1.50/0.98  res_preprocessed:                       107
% 1.50/0.98  prep_upred:                             0
% 1.50/0.98  prep_unflattend:                        71
% 1.50/0.98  smt_new_axioms:                         0
% 1.50/0.98  pred_elim_cands:                        4
% 1.50/0.98  pred_elim:                              7
% 1.50/0.98  pred_elim_cl:                           7
% 1.50/0.98  pred_elim_cycles:                       12
% 1.50/0.98  merged_defs:                            0
% 1.50/0.98  merged_defs_ncl:                        0
% 1.50/0.98  bin_hyper_res:                          0
% 1.50/0.98  prep_cycles:                            4
% 1.50/0.98  pred_elim_time:                         0.035
% 1.50/0.98  splitting_time:                         0.
% 1.50/0.98  sem_filter_time:                        0.
% 1.50/0.98  monotx_time:                            0.001
% 1.50/0.98  subtype_inf_time:                       0.
% 1.50/0.98  
% 1.50/0.98  ------ Problem properties
% 1.50/0.98  
% 1.50/0.98  clauses:                                18
% 1.50/0.98  conjectures:                            2
% 1.50/0.98  epr:                                    1
% 1.50/0.98  horn:                                   13
% 1.50/0.98  ground:                                 3
% 1.50/0.98  unary:                                  3
% 1.50/0.98  binary:                                 3
% 1.50/0.98  lits:                                   58
% 1.50/0.98  lits_eq:                                13
% 1.50/0.98  fd_pure:                                0
% 1.50/0.98  fd_pseudo:                              0
% 1.50/0.98  fd_cond:                                4
% 1.50/0.98  fd_pseudo_cond:                         2
% 1.50/0.98  ac_symbols:                             0
% 1.50/0.98  
% 1.50/0.98  ------ Propositional Solver
% 1.50/0.98  
% 1.50/0.98  prop_solver_calls:                      26
% 1.50/0.98  prop_fast_solver_calls:                 1335
% 1.50/0.98  smt_solver_calls:                       0
% 1.50/0.98  smt_fast_solver_calls:                  0
% 1.50/0.98  prop_num_of_clauses:                    687
% 1.50/0.98  prop_preprocess_simplified:             3650
% 1.50/0.98  prop_fo_subsumed:                       59
% 1.50/0.98  prop_solver_time:                       0.
% 1.50/0.98  smt_solver_time:                        0.
% 1.50/0.98  smt_fast_solver_time:                   0.
% 1.50/0.98  prop_fast_solver_time:                  0.
% 1.50/0.98  prop_unsat_core_time:                   0.
% 1.50/0.98  
% 1.50/0.98  ------ QBF
% 1.50/0.98  
% 1.50/0.98  qbf_q_res:                              0
% 1.50/0.98  qbf_num_tautologies:                    0
% 1.50/0.98  qbf_prep_cycles:                        0
% 1.50/0.98  
% 1.50/0.98  ------ BMC1
% 1.50/0.98  
% 1.50/0.98  bmc1_current_bound:                     -1
% 1.50/0.98  bmc1_last_solved_bound:                 -1
% 1.50/0.98  bmc1_unsat_core_size:                   -1
% 1.50/0.98  bmc1_unsat_core_parents_size:           -1
% 1.50/0.98  bmc1_merge_next_fun:                    0
% 1.50/0.98  bmc1_unsat_core_clauses_time:           0.
% 1.50/0.98  
% 1.50/0.98  ------ Instantiation
% 1.50/0.98  
% 1.50/0.98  inst_num_of_clauses:                    173
% 1.50/0.98  inst_num_in_passive:                    33
% 1.50/0.98  inst_num_in_active:                     114
% 1.50/0.98  inst_num_in_unprocessed:                26
% 1.50/0.98  inst_num_of_loops:                      135
% 1.50/0.98  inst_num_of_learning_restarts:          0
% 1.50/0.98  inst_num_moves_active_passive:          17
% 1.50/0.98  inst_lit_activity:                      0
% 1.50/0.98  inst_lit_activity_moves:                0
% 1.50/0.98  inst_num_tautologies:                   0
% 1.50/0.98  inst_num_prop_implied:                  0
% 1.50/0.98  inst_num_existing_simplified:           0
% 1.50/0.98  inst_num_eq_res_simplified:             0
% 1.50/0.98  inst_num_child_elim:                    0
% 1.50/0.98  inst_num_of_dismatching_blockings:      8
% 1.50/0.98  inst_num_of_non_proper_insts:           91
% 1.50/0.98  inst_num_of_duplicates:                 0
% 1.50/0.98  inst_inst_num_from_inst_to_res:         0
% 1.50/0.98  inst_dismatching_checking_time:         0.
% 1.50/0.98  
% 1.50/0.98  ------ Resolution
% 1.50/0.98  
% 1.50/0.98  res_num_of_clauses:                     0
% 1.50/0.98  res_num_in_passive:                     0
% 1.50/0.98  res_num_in_active:                      0
% 1.50/0.98  res_num_of_loops:                       111
% 1.50/0.98  res_forward_subset_subsumed:            3
% 1.50/0.98  res_backward_subset_subsumed:           2
% 1.50/0.98  res_forward_subsumed:                   0
% 1.50/0.98  res_backward_subsumed:                  0
% 1.50/0.98  res_forward_subsumption_resolution:     3
% 1.50/0.98  res_backward_subsumption_resolution:    0
% 1.50/0.98  res_clause_to_clause_subsumption:       40
% 1.50/0.98  res_orphan_elimination:                 0
% 1.50/0.98  res_tautology_del:                      11
% 1.50/0.98  res_num_eq_res_simplified:              0
% 1.50/0.98  res_num_sel_changes:                    0
% 1.50/0.98  res_moves_from_active_to_pass:          0
% 1.50/0.98  
% 1.50/0.98  ------ Superposition
% 1.50/0.98  
% 1.50/0.98  sup_time_total:                         0.
% 1.50/0.98  sup_time_generating:                    0.
% 1.50/0.98  sup_time_sim_full:                      0.
% 1.50/0.98  sup_time_sim_immed:                     0.
% 1.50/0.98  
% 1.50/0.98  sup_num_of_clauses:                     32
% 1.50/0.98  sup_num_in_active:                      26
% 1.50/0.98  sup_num_in_passive:                     6
% 1.50/0.98  sup_num_of_loops:                       26
% 1.50/0.98  sup_fw_superposition:                   12
% 1.50/0.98  sup_bw_superposition:                   12
% 1.50/0.98  sup_immediate_simplified:               4
% 1.50/0.98  sup_given_eliminated:                   0
% 1.50/0.98  comparisons_done:                       0
% 1.50/0.98  comparisons_avoided:                    2
% 1.50/0.98  
% 1.50/0.98  ------ Simplifications
% 1.50/0.98  
% 1.50/0.98  
% 1.50/0.98  sim_fw_subset_subsumed:                 1
% 1.50/0.98  sim_bw_subset_subsumed:                 0
% 1.50/0.98  sim_fw_subsumed:                        2
% 1.50/0.98  sim_bw_subsumed:                        0
% 1.50/0.98  sim_fw_subsumption_res:                 1
% 1.50/0.98  sim_bw_subsumption_res:                 0
% 1.50/0.98  sim_tautology_del:                      2
% 1.50/0.98  sim_eq_tautology_del:                   6
% 1.50/0.98  sim_eq_res_simp:                        0
% 1.50/0.98  sim_fw_demodulated:                     2
% 1.50/0.98  sim_bw_demodulated:                     0
% 1.50/0.98  sim_light_normalised:                   1
% 1.50/0.98  sim_joinable_taut:                      0
% 1.50/0.98  sim_joinable_simp:                      0
% 1.50/0.98  sim_ac_normalised:                      0
% 1.50/0.98  sim_smt_subsumption:                    0
% 1.50/0.98  
%------------------------------------------------------------------------------
