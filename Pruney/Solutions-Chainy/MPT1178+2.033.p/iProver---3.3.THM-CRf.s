%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:13:04 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 392 expanded)
%              Number of clauses        :   47 (  87 expanded)
%              Number of leaves         :   14 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  623 (2568 expanded)
%              Number of equality atoms :  107 ( 405 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK1(X0,X1,X2)))) != sK1(X0,X1,X2)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK1(X0,X1,X2)))) != sK1(X0,X1,X2)
                    & r2_hidden(sK1(X0,X1,X2),X2)
                    & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f29])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f43])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5))
        & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
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

fof(f38,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))
    & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f37,f36])).

fof(f63,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f60,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f61,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK0(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK0(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f23])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f65,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f38])).

fof(f7,axiom,(
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

fof(f10,plain,(
    ! [X0] :
      ( ~ ( ! [X1] :
              ~ ( r2_hidden(X1,X0)
                & k1_xboole_0 != X1 )
          & k1_xboole_0 != k3_tarski(X0) )
      & ~ ( k1_xboole_0 = k3_tarski(X0)
          & ? [X2] :
              ( r2_hidden(X2,X0)
              & k1_xboole_0 != X2 ) ) ) ),
    inference(rectify,[],[f7])).

fof(f20,plain,(
    ! [X0] :
      ( ( ? [X1] :
            ( r2_hidden(X1,X0)
            & k1_xboole_0 != X1 )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,X0)
          & k1_xboole_0 != X1 )
     => ( r2_hidden(sK3(X0),X0)
        & k1_xboole_0 != sK3(X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( r2_hidden(sK3(X0),X0)
          & k1_xboole_0 != sK3(X0) )
        | k1_xboole_0 = k3_tarski(X0) )
      & ( k1_xboole_0 != k3_tarski(X0)
        | ! [X2] :
            ( ~ r2_hidden(X2,X0)
            | k1_xboole_0 = X2 ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f34])).

fof(f56,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 != k3_tarski(X0)
      | ~ r2_hidden(X2,X0)
      | k1_xboole_0 = X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
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

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f31,plain,(
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
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ m2_orders_2(X3,X0,X1)
            | ~ r2_hidden(X3,X2) )
          & ( m2_orders_2(X3,X0,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k4_orders_2(X0,X1) = X2
                | ( ( ~ m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | ~ r2_hidden(sK2(X0,X1,X2),X2) )
                  & ( m2_orders_2(sK2(X0,X1,X2),X0,X1)
                    | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,X2)
      | k4_orders_2(X0,X1) != X2
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X4,X0,X1] :
      ( m2_orders_2(X4,X0,X1)
      | ~ r2_hidden(X4,k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f49])).

cnf(c_15,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_9,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_452,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_9])).

cnf(c_453,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_14,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_477,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_453,c_14])).

cnf(c_22,negated_conjecture,
    ( l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_805,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_477,c_22])).

cnf(c_806,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m2_orders_2(k1_xboole_0,sK4,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_805])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_24,negated_conjecture,
    ( v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_23,negated_conjecture,
    ( v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_810,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m2_orders_2(k1_xboole_0,sK4,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_806,c_26,c_25,c_24,c_23])).

cnf(c_2489,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_810])).

cnf(c_2490,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_810])).

cnf(c_2574,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | ~ m2_orders_2(k1_xboole_0,sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2489,c_2490])).

cnf(c_2575,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
    inference(renaming,[status(thm)],[c_2574])).

cnf(c_3803,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK4,sK5)
    | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_2575])).

cnf(c_3,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_2855,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,X1)
    | k3_tarski(X1) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2853,plain,
    ( k3_tarski(X0) != k1_xboole_0
    | k1_xboole_0 = X1
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3347,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_2853])).

cnf(c_3352,plain,
    ( k4_orders_2(sK4,sK5) = k1_xboole_0
    | sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2855,c_3347])).

cnf(c_21,negated_conjecture,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_16,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_295,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k4_orders_2(X1,X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_697,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k4_orders_2(X1,X0) != k1_xboole_0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_295,c_22])).

cnf(c_698,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | k4_orders_2(sK4,X0) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_702,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
    | k4_orders_2(sK4,X0) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_698,c_26,c_25,c_24,c_23])).

cnf(c_3023,plain,
    ( ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
    | k4_orders_2(sK4,sK5) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_3632,plain,
    ( sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3352,c_21,c_3023])).

cnf(c_3635,plain,
    ( k4_orders_2(sK4,sK5) = k1_xboole_0
    | r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3632,c_2855])).

cnf(c_3636,plain,
    ( r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5))
    | k4_orders_2(sK4,sK5) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3635])).

cnf(c_2852,plain,
    ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_13,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_763,plain,
    ( m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | ~ r2_hidden(X0,k4_orders_2(X1,X2))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_764,plain,
    ( m2_orders_2(X0,sK4,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,k4_orders_2(sK4,X1))
    | v2_struct_0(sK4)
    | ~ v3_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v5_orders_2(sK4) ),
    inference(unflattening,[status(thm)],[c_763])).

cnf(c_768,plain,
    ( m2_orders_2(X0,sK4,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
    | ~ r2_hidden(X0,k4_orders_2(sK4,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_764,c_26,c_25,c_24,c_23])).

cnf(c_2845,plain,
    ( m2_orders_2(X0,sK4,X1) = iProver_top
    | m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_768])).

cnf(c_3080,plain,
    ( m2_orders_2(X0,sK4,sK5) = iProver_top
    | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2852,c_2845])).

cnf(c_3081,plain,
    ( m2_orders_2(X0,sK4,sK5)
    | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3080])).

cnf(c_3083,plain,
    ( m2_orders_2(k1_xboole_0,sK4,sK5)
    | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_3081])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3803,c_3636,c_3083,c_3023,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 1.96/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.96/0.98  
% 1.96/0.98  ------  iProver source info
% 1.96/0.98  
% 1.96/0.98  git: date: 2020-06-30 10:37:57 +0100
% 1.96/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.96/0.98  git: non_committed_changes: false
% 1.96/0.98  git: last_make_outside_of_git: false
% 1.96/0.98  
% 1.96/0.98  ------ 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options
% 1.96/0.98  
% 1.96/0.98  --out_options                           all
% 1.96/0.98  --tptp_safe_out                         true
% 1.96/0.98  --problem_path                          ""
% 1.96/0.98  --include_path                          ""
% 1.96/0.98  --clausifier                            res/vclausify_rel
% 1.96/0.98  --clausifier_options                    --mode clausify
% 1.96/0.98  --stdin                                 false
% 1.96/0.98  --stats_out                             all
% 1.96/0.98  
% 1.96/0.98  ------ General Options
% 1.96/0.98  
% 1.96/0.98  --fof                                   false
% 1.96/0.98  --time_out_real                         305.
% 1.96/0.98  --time_out_virtual                      -1.
% 1.96/0.98  --symbol_type_check                     false
% 1.96/0.98  --clausify_out                          false
% 1.96/0.98  --sig_cnt_out                           false
% 1.96/0.98  --trig_cnt_out                          false
% 1.96/0.98  --trig_cnt_out_tolerance                1.
% 1.96/0.98  --trig_cnt_out_sk_spl                   false
% 1.96/0.98  --abstr_cl_out                          false
% 1.96/0.98  
% 1.96/0.98  ------ Global Options
% 1.96/0.98  
% 1.96/0.98  --schedule                              default
% 1.96/0.98  --add_important_lit                     false
% 1.96/0.98  --prop_solver_per_cl                    1000
% 1.96/0.98  --min_unsat_core                        false
% 1.96/0.98  --soft_assumptions                      false
% 1.96/0.98  --soft_lemma_size                       3
% 1.96/0.98  --prop_impl_unit_size                   0
% 1.96/0.98  --prop_impl_unit                        []
% 1.96/0.98  --share_sel_clauses                     true
% 1.96/0.98  --reset_solvers                         false
% 1.96/0.98  --bc_imp_inh                            [conj_cone]
% 1.96/0.98  --conj_cone_tolerance                   3.
% 1.96/0.98  --extra_neg_conj                        none
% 1.96/0.98  --large_theory_mode                     true
% 1.96/0.98  --prolific_symb_bound                   200
% 1.96/0.98  --lt_threshold                          2000
% 1.96/0.98  --clause_weak_htbl                      true
% 1.96/0.98  --gc_record_bc_elim                     false
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing Options
% 1.96/0.98  
% 1.96/0.98  --preprocessing_flag                    true
% 1.96/0.98  --time_out_prep_mult                    0.1
% 1.96/0.98  --splitting_mode                        input
% 1.96/0.98  --splitting_grd                         true
% 1.96/0.98  --splitting_cvd                         false
% 1.96/0.98  --splitting_cvd_svl                     false
% 1.96/0.98  --splitting_nvd                         32
% 1.96/0.98  --sub_typing                            true
% 1.96/0.98  --prep_gs_sim                           true
% 1.96/0.98  --prep_unflatten                        true
% 1.96/0.98  --prep_res_sim                          true
% 1.96/0.98  --prep_upred                            true
% 1.96/0.98  --prep_sem_filter                       exhaustive
% 1.96/0.98  --prep_sem_filter_out                   false
% 1.96/0.98  --pred_elim                             true
% 1.96/0.98  --res_sim_input                         true
% 1.96/0.98  --eq_ax_congr_red                       true
% 1.96/0.98  --pure_diseq_elim                       true
% 1.96/0.98  --brand_transform                       false
% 1.96/0.98  --non_eq_to_eq                          false
% 1.96/0.98  --prep_def_merge                        true
% 1.96/0.98  --prep_def_merge_prop_impl              false
% 1.96/0.98  --prep_def_merge_mbd                    true
% 1.96/0.98  --prep_def_merge_tr_red                 false
% 1.96/0.98  --prep_def_merge_tr_cl                  false
% 1.96/0.98  --smt_preprocessing                     true
% 1.96/0.98  --smt_ac_axioms                         fast
% 1.96/0.98  --preprocessed_out                      false
% 1.96/0.98  --preprocessed_stats                    false
% 1.96/0.98  
% 1.96/0.98  ------ Abstraction refinement Options
% 1.96/0.98  
% 1.96/0.98  --abstr_ref                             []
% 1.96/0.98  --abstr_ref_prep                        false
% 1.96/0.98  --abstr_ref_until_sat                   false
% 1.96/0.98  --abstr_ref_sig_restrict                funpre
% 1.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.98  --abstr_ref_under                       []
% 1.96/0.98  
% 1.96/0.98  ------ SAT Options
% 1.96/0.98  
% 1.96/0.98  --sat_mode                              false
% 1.96/0.98  --sat_fm_restart_options                ""
% 1.96/0.98  --sat_gr_def                            false
% 1.96/0.98  --sat_epr_types                         true
% 1.96/0.98  --sat_non_cyclic_types                  false
% 1.96/0.98  --sat_finite_models                     false
% 1.96/0.98  --sat_fm_lemmas                         false
% 1.96/0.98  --sat_fm_prep                           false
% 1.96/0.98  --sat_fm_uc_incr                        true
% 1.96/0.98  --sat_out_model                         small
% 1.96/0.98  --sat_out_clauses                       false
% 1.96/0.98  
% 1.96/0.98  ------ QBF Options
% 1.96/0.98  
% 1.96/0.98  --qbf_mode                              false
% 1.96/0.98  --qbf_elim_univ                         false
% 1.96/0.98  --qbf_dom_inst                          none
% 1.96/0.98  --qbf_dom_pre_inst                      false
% 1.96/0.98  --qbf_sk_in                             false
% 1.96/0.98  --qbf_pred_elim                         true
% 1.96/0.98  --qbf_split                             512
% 1.96/0.98  
% 1.96/0.98  ------ BMC1 Options
% 1.96/0.98  
% 1.96/0.98  --bmc1_incremental                      false
% 1.96/0.98  --bmc1_axioms                           reachable_all
% 1.96/0.98  --bmc1_min_bound                        0
% 1.96/0.98  --bmc1_max_bound                        -1
% 1.96/0.98  --bmc1_max_bound_default                -1
% 1.96/0.98  --bmc1_symbol_reachability              true
% 1.96/0.98  --bmc1_property_lemmas                  false
% 1.96/0.98  --bmc1_k_induction                      false
% 1.96/0.98  --bmc1_non_equiv_states                 false
% 1.96/0.98  --bmc1_deadlock                         false
% 1.96/0.98  --bmc1_ucm                              false
% 1.96/0.98  --bmc1_add_unsat_core                   none
% 1.96/0.98  --bmc1_unsat_core_children              false
% 1.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.98  --bmc1_out_stat                         full
% 1.96/0.98  --bmc1_ground_init                      false
% 1.96/0.98  --bmc1_pre_inst_next_state              false
% 1.96/0.98  --bmc1_pre_inst_state                   false
% 1.96/0.98  --bmc1_pre_inst_reach_state             false
% 1.96/0.98  --bmc1_out_unsat_core                   false
% 1.96/0.98  --bmc1_aig_witness_out                  false
% 1.96/0.98  --bmc1_verbose                          false
% 1.96/0.98  --bmc1_dump_clauses_tptp                false
% 1.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.98  --bmc1_dump_file                        -
% 1.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.98  --bmc1_ucm_extend_mode                  1
% 1.96/0.98  --bmc1_ucm_init_mode                    2
% 1.96/0.98  --bmc1_ucm_cone_mode                    none
% 1.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.98  --bmc1_ucm_relax_model                  4
% 1.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.98  --bmc1_ucm_layered_model                none
% 1.96/0.98  --bmc1_ucm_max_lemma_size               10
% 1.96/0.98  
% 1.96/0.98  ------ AIG Options
% 1.96/0.98  
% 1.96/0.98  --aig_mode                              false
% 1.96/0.98  
% 1.96/0.98  ------ Instantiation Options
% 1.96/0.98  
% 1.96/0.98  --instantiation_flag                    true
% 1.96/0.98  --inst_sos_flag                         false
% 1.96/0.98  --inst_sos_phase                        true
% 1.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel_side                     num_symb
% 1.96/0.98  --inst_solver_per_active                1400
% 1.96/0.98  --inst_solver_calls_frac                1.
% 1.96/0.98  --inst_passive_queue_type               priority_queues
% 1.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.98  --inst_passive_queues_freq              [25;2]
% 1.96/0.98  --inst_dismatching                      true
% 1.96/0.98  --inst_eager_unprocessed_to_passive     true
% 1.96/0.98  --inst_prop_sim_given                   true
% 1.96/0.98  --inst_prop_sim_new                     false
% 1.96/0.98  --inst_subs_new                         false
% 1.96/0.98  --inst_eq_res_simp                      false
% 1.96/0.98  --inst_subs_given                       false
% 1.96/0.98  --inst_orphan_elimination               true
% 1.96/0.98  --inst_learning_loop_flag               true
% 1.96/0.98  --inst_learning_start                   3000
% 1.96/0.98  --inst_learning_factor                  2
% 1.96/0.98  --inst_start_prop_sim_after_learn       3
% 1.96/0.98  --inst_sel_renew                        solver
% 1.96/0.98  --inst_lit_activity_flag                true
% 1.96/0.98  --inst_restr_to_given                   false
% 1.96/0.98  --inst_activity_threshold               500
% 1.96/0.98  --inst_out_proof                        true
% 1.96/0.98  
% 1.96/0.98  ------ Resolution Options
% 1.96/0.98  
% 1.96/0.98  --resolution_flag                       true
% 1.96/0.98  --res_lit_sel                           adaptive
% 1.96/0.98  --res_lit_sel_side                      none
% 1.96/0.98  --res_ordering                          kbo
% 1.96/0.98  --res_to_prop_solver                    active
% 1.96/0.98  --res_prop_simpl_new                    false
% 1.96/0.98  --res_prop_simpl_given                  true
% 1.96/0.98  --res_passive_queue_type                priority_queues
% 1.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.98  --res_passive_queues_freq               [15;5]
% 1.96/0.98  --res_forward_subs                      full
% 1.96/0.98  --res_backward_subs                     full
% 1.96/0.98  --res_forward_subs_resolution           true
% 1.96/0.98  --res_backward_subs_resolution          true
% 1.96/0.98  --res_orphan_elimination                true
% 1.96/0.98  --res_time_limit                        2.
% 1.96/0.98  --res_out_proof                         true
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Options
% 1.96/0.98  
% 1.96/0.98  --superposition_flag                    true
% 1.96/0.98  --sup_passive_queue_type                priority_queues
% 1.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.98  --demod_completeness_check              fast
% 1.96/0.98  --demod_use_ground                      true
% 1.96/0.98  --sup_to_prop_solver                    passive
% 1.96/0.98  --sup_prop_simpl_new                    true
% 1.96/0.98  --sup_prop_simpl_given                  true
% 1.96/0.98  --sup_fun_splitting                     false
% 1.96/0.98  --sup_smt_interval                      50000
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Simplification Setup
% 1.96/0.98  
% 1.96/0.98  --sup_indices_passive                   []
% 1.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_full_bw                           [BwDemod]
% 1.96/0.98  --sup_immed_triv                        [TrivRules]
% 1.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_immed_bw_main                     []
% 1.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  
% 1.96/0.98  ------ Combination Options
% 1.96/0.98  
% 1.96/0.98  --comb_res_mult                         3
% 1.96/0.98  --comb_sup_mult                         2
% 1.96/0.98  --comb_inst_mult                        10
% 1.96/0.98  
% 1.96/0.98  ------ Debug Options
% 1.96/0.98  
% 1.96/0.98  --dbg_backtrace                         false
% 1.96/0.98  --dbg_dump_prop_clauses                 false
% 1.96/0.98  --dbg_dump_prop_clauses_file            -
% 1.96/0.98  --dbg_out_stat                          false
% 1.96/0.98  ------ Parsing...
% 1.96/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.96/0.98  ------ Proving...
% 1.96/0.98  ------ Problem Properties 
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  clauses                                 21
% 1.96/0.98  conjectures                             2
% 1.96/0.98  EPR                                     1
% 1.96/0.98  Horn                                    15
% 1.96/0.98  unary                                   3
% 1.96/0.98  binary                                  4
% 1.96/0.98  lits                                    66
% 1.96/0.98  lits eq                                 19
% 1.96/0.98  fd_pure                                 0
% 1.96/0.98  fd_pseudo                               0
% 1.96/0.98  fd_cond                                 7
% 1.96/0.98  fd_pseudo_cond                          2
% 1.96/0.98  AC symbols                              0
% 1.96/0.98  
% 1.96/0.98  ------ Schedule dynamic 5 is on 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  ------ 
% 1.96/0.98  Current options:
% 1.96/0.98  ------ 
% 1.96/0.98  
% 1.96/0.98  ------ Input Options
% 1.96/0.98  
% 1.96/0.98  --out_options                           all
% 1.96/0.98  --tptp_safe_out                         true
% 1.96/0.98  --problem_path                          ""
% 1.96/0.98  --include_path                          ""
% 1.96/0.98  --clausifier                            res/vclausify_rel
% 1.96/0.98  --clausifier_options                    --mode clausify
% 1.96/0.98  --stdin                                 false
% 1.96/0.98  --stats_out                             all
% 1.96/0.98  
% 1.96/0.98  ------ General Options
% 1.96/0.98  
% 1.96/0.98  --fof                                   false
% 1.96/0.98  --time_out_real                         305.
% 1.96/0.98  --time_out_virtual                      -1.
% 1.96/0.98  --symbol_type_check                     false
% 1.96/0.98  --clausify_out                          false
% 1.96/0.98  --sig_cnt_out                           false
% 1.96/0.98  --trig_cnt_out                          false
% 1.96/0.98  --trig_cnt_out_tolerance                1.
% 1.96/0.98  --trig_cnt_out_sk_spl                   false
% 1.96/0.98  --abstr_cl_out                          false
% 1.96/0.98  
% 1.96/0.98  ------ Global Options
% 1.96/0.98  
% 1.96/0.98  --schedule                              default
% 1.96/0.98  --add_important_lit                     false
% 1.96/0.98  --prop_solver_per_cl                    1000
% 1.96/0.98  --min_unsat_core                        false
% 1.96/0.98  --soft_assumptions                      false
% 1.96/0.98  --soft_lemma_size                       3
% 1.96/0.98  --prop_impl_unit_size                   0
% 1.96/0.98  --prop_impl_unit                        []
% 1.96/0.98  --share_sel_clauses                     true
% 1.96/0.98  --reset_solvers                         false
% 1.96/0.98  --bc_imp_inh                            [conj_cone]
% 1.96/0.98  --conj_cone_tolerance                   3.
% 1.96/0.98  --extra_neg_conj                        none
% 1.96/0.98  --large_theory_mode                     true
% 1.96/0.98  --prolific_symb_bound                   200
% 1.96/0.98  --lt_threshold                          2000
% 1.96/0.98  --clause_weak_htbl                      true
% 1.96/0.98  --gc_record_bc_elim                     false
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing Options
% 1.96/0.98  
% 1.96/0.98  --preprocessing_flag                    true
% 1.96/0.98  --time_out_prep_mult                    0.1
% 1.96/0.98  --splitting_mode                        input
% 1.96/0.98  --splitting_grd                         true
% 1.96/0.98  --splitting_cvd                         false
% 1.96/0.98  --splitting_cvd_svl                     false
% 1.96/0.98  --splitting_nvd                         32
% 1.96/0.98  --sub_typing                            true
% 1.96/0.98  --prep_gs_sim                           true
% 1.96/0.98  --prep_unflatten                        true
% 1.96/0.98  --prep_res_sim                          true
% 1.96/0.98  --prep_upred                            true
% 1.96/0.98  --prep_sem_filter                       exhaustive
% 1.96/0.98  --prep_sem_filter_out                   false
% 1.96/0.98  --pred_elim                             true
% 1.96/0.98  --res_sim_input                         true
% 1.96/0.98  --eq_ax_congr_red                       true
% 1.96/0.98  --pure_diseq_elim                       true
% 1.96/0.98  --brand_transform                       false
% 1.96/0.98  --non_eq_to_eq                          false
% 1.96/0.98  --prep_def_merge                        true
% 1.96/0.98  --prep_def_merge_prop_impl              false
% 1.96/0.98  --prep_def_merge_mbd                    true
% 1.96/0.98  --prep_def_merge_tr_red                 false
% 1.96/0.98  --prep_def_merge_tr_cl                  false
% 1.96/0.98  --smt_preprocessing                     true
% 1.96/0.98  --smt_ac_axioms                         fast
% 1.96/0.98  --preprocessed_out                      false
% 1.96/0.98  --preprocessed_stats                    false
% 1.96/0.98  
% 1.96/0.98  ------ Abstraction refinement Options
% 1.96/0.98  
% 1.96/0.98  --abstr_ref                             []
% 1.96/0.98  --abstr_ref_prep                        false
% 1.96/0.98  --abstr_ref_until_sat                   false
% 1.96/0.98  --abstr_ref_sig_restrict                funpre
% 1.96/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 1.96/0.98  --abstr_ref_under                       []
% 1.96/0.98  
% 1.96/0.98  ------ SAT Options
% 1.96/0.98  
% 1.96/0.98  --sat_mode                              false
% 1.96/0.98  --sat_fm_restart_options                ""
% 1.96/0.98  --sat_gr_def                            false
% 1.96/0.98  --sat_epr_types                         true
% 1.96/0.98  --sat_non_cyclic_types                  false
% 1.96/0.98  --sat_finite_models                     false
% 1.96/0.98  --sat_fm_lemmas                         false
% 1.96/0.98  --sat_fm_prep                           false
% 1.96/0.98  --sat_fm_uc_incr                        true
% 1.96/0.98  --sat_out_model                         small
% 1.96/0.98  --sat_out_clauses                       false
% 1.96/0.98  
% 1.96/0.98  ------ QBF Options
% 1.96/0.98  
% 1.96/0.98  --qbf_mode                              false
% 1.96/0.98  --qbf_elim_univ                         false
% 1.96/0.98  --qbf_dom_inst                          none
% 1.96/0.98  --qbf_dom_pre_inst                      false
% 1.96/0.98  --qbf_sk_in                             false
% 1.96/0.98  --qbf_pred_elim                         true
% 1.96/0.98  --qbf_split                             512
% 1.96/0.98  
% 1.96/0.98  ------ BMC1 Options
% 1.96/0.98  
% 1.96/0.98  --bmc1_incremental                      false
% 1.96/0.98  --bmc1_axioms                           reachable_all
% 1.96/0.98  --bmc1_min_bound                        0
% 1.96/0.98  --bmc1_max_bound                        -1
% 1.96/0.98  --bmc1_max_bound_default                -1
% 1.96/0.98  --bmc1_symbol_reachability              true
% 1.96/0.98  --bmc1_property_lemmas                  false
% 1.96/0.98  --bmc1_k_induction                      false
% 1.96/0.98  --bmc1_non_equiv_states                 false
% 1.96/0.98  --bmc1_deadlock                         false
% 1.96/0.98  --bmc1_ucm                              false
% 1.96/0.98  --bmc1_add_unsat_core                   none
% 1.96/0.98  --bmc1_unsat_core_children              false
% 1.96/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 1.96/0.98  --bmc1_out_stat                         full
% 1.96/0.98  --bmc1_ground_init                      false
% 1.96/0.98  --bmc1_pre_inst_next_state              false
% 1.96/0.98  --bmc1_pre_inst_state                   false
% 1.96/0.98  --bmc1_pre_inst_reach_state             false
% 1.96/0.98  --bmc1_out_unsat_core                   false
% 1.96/0.98  --bmc1_aig_witness_out                  false
% 1.96/0.98  --bmc1_verbose                          false
% 1.96/0.98  --bmc1_dump_clauses_tptp                false
% 1.96/0.98  --bmc1_dump_unsat_core_tptp             false
% 1.96/0.98  --bmc1_dump_file                        -
% 1.96/0.98  --bmc1_ucm_expand_uc_limit              128
% 1.96/0.98  --bmc1_ucm_n_expand_iterations          6
% 1.96/0.98  --bmc1_ucm_extend_mode                  1
% 1.96/0.98  --bmc1_ucm_init_mode                    2
% 1.96/0.98  --bmc1_ucm_cone_mode                    none
% 1.96/0.98  --bmc1_ucm_reduced_relation_type        0
% 1.96/0.98  --bmc1_ucm_relax_model                  4
% 1.96/0.98  --bmc1_ucm_full_tr_after_sat            true
% 1.96/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 1.96/0.98  --bmc1_ucm_layered_model                none
% 1.96/0.98  --bmc1_ucm_max_lemma_size               10
% 1.96/0.98  
% 1.96/0.98  ------ AIG Options
% 1.96/0.98  
% 1.96/0.98  --aig_mode                              false
% 1.96/0.98  
% 1.96/0.98  ------ Instantiation Options
% 1.96/0.98  
% 1.96/0.98  --instantiation_flag                    true
% 1.96/0.98  --inst_sos_flag                         false
% 1.96/0.98  --inst_sos_phase                        true
% 1.96/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.96/0.98  --inst_lit_sel_side                     none
% 1.96/0.98  --inst_solver_per_active                1400
% 1.96/0.98  --inst_solver_calls_frac                1.
% 1.96/0.98  --inst_passive_queue_type               priority_queues
% 1.96/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.96/0.98  --inst_passive_queues_freq              [25;2]
% 1.96/0.98  --inst_dismatching                      true
% 1.96/0.98  --inst_eager_unprocessed_to_passive     true
% 1.96/0.98  --inst_prop_sim_given                   true
% 1.96/0.98  --inst_prop_sim_new                     false
% 1.96/0.98  --inst_subs_new                         false
% 1.96/0.98  --inst_eq_res_simp                      false
% 1.96/0.98  --inst_subs_given                       false
% 1.96/0.98  --inst_orphan_elimination               true
% 1.96/0.98  --inst_learning_loop_flag               true
% 1.96/0.98  --inst_learning_start                   3000
% 1.96/0.98  --inst_learning_factor                  2
% 1.96/0.98  --inst_start_prop_sim_after_learn       3
% 1.96/0.98  --inst_sel_renew                        solver
% 1.96/0.98  --inst_lit_activity_flag                true
% 1.96/0.98  --inst_restr_to_given                   false
% 1.96/0.98  --inst_activity_threshold               500
% 1.96/0.98  --inst_out_proof                        true
% 1.96/0.98  
% 1.96/0.98  ------ Resolution Options
% 1.96/0.98  
% 1.96/0.98  --resolution_flag                       false
% 1.96/0.98  --res_lit_sel                           adaptive
% 1.96/0.98  --res_lit_sel_side                      none
% 1.96/0.98  --res_ordering                          kbo
% 1.96/0.98  --res_to_prop_solver                    active
% 1.96/0.98  --res_prop_simpl_new                    false
% 1.96/0.98  --res_prop_simpl_given                  true
% 1.96/0.98  --res_passive_queue_type                priority_queues
% 1.96/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.96/0.98  --res_passive_queues_freq               [15;5]
% 1.96/0.98  --res_forward_subs                      full
% 1.96/0.98  --res_backward_subs                     full
% 1.96/0.98  --res_forward_subs_resolution           true
% 1.96/0.98  --res_backward_subs_resolution          true
% 1.96/0.98  --res_orphan_elimination                true
% 1.96/0.98  --res_time_limit                        2.
% 1.96/0.98  --res_out_proof                         true
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Options
% 1.96/0.98  
% 1.96/0.98  --superposition_flag                    true
% 1.96/0.98  --sup_passive_queue_type                priority_queues
% 1.96/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.96/0.98  --sup_passive_queues_freq               [8;1;4]
% 1.96/0.98  --demod_completeness_check              fast
% 1.96/0.98  --demod_use_ground                      true
% 1.96/0.98  --sup_to_prop_solver                    passive
% 1.96/0.98  --sup_prop_simpl_new                    true
% 1.96/0.98  --sup_prop_simpl_given                  true
% 1.96/0.98  --sup_fun_splitting                     false
% 1.96/0.98  --sup_smt_interval                      50000
% 1.96/0.98  
% 1.96/0.98  ------ Superposition Simplification Setup
% 1.96/0.98  
% 1.96/0.98  --sup_indices_passive                   []
% 1.96/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.96/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 1.96/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_full_bw                           [BwDemod]
% 1.96/0.98  --sup_immed_triv                        [TrivRules]
% 1.96/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.96/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_immed_bw_main                     []
% 1.96/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 1.96/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.96/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.96/0.98  
% 1.96/0.98  ------ Combination Options
% 1.96/0.98  
% 1.96/0.98  --comb_res_mult                         3
% 1.96/0.98  --comb_sup_mult                         2
% 1.96/0.98  --comb_inst_mult                        10
% 1.96/0.98  
% 1.96/0.98  ------ Debug Options
% 1.96/0.98  
% 1.96/0.98  --dbg_backtrace                         false
% 1.96/0.98  --dbg_dump_prop_clauses                 false
% 1.96/0.98  --dbg_dump_prop_clauses_file            -
% 1.96/0.98  --dbg_out_stat                          false
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  ------ Proving...
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  % SZS status Theorem for theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  fof(f5,axiom,(
% 1.96/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f16,plain,(
% 1.96/0.98    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f5])).
% 1.96/0.98  
% 1.96/0.98  fof(f17,plain,(
% 1.96/0.98    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f16])).
% 1.96/0.98  
% 1.96/0.98  fof(f53,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f17])).
% 1.96/0.98  
% 1.96/0.98  fof(f3,axiom,(
% 1.96/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f12,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f3])).
% 1.96/0.98  
% 1.96/0.98  fof(f13,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f12])).
% 1.96/0.98  
% 1.96/0.98  fof(f25,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(nnf_transformation,[],[f13])).
% 1.96/0.98  
% 1.96/0.98  fof(f26,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f25])).
% 1.96/0.98  
% 1.96/0.98  fof(f27,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(rectify,[],[f26])).
% 1.96/0.98  
% 1.96/0.98  fof(f28,plain,(
% 1.96/0.98    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK1(X0,X1,X2)))) != sK1(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f29,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK1(X0,X1,X2)))) != sK1(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X2) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f27,f28])).
% 1.96/0.98  
% 1.96/0.98  fof(f43,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f29])).
% 1.96/0.98  
% 1.96/0.98  fof(f66,plain,(
% 1.96/0.98    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f43])).
% 1.96/0.98  
% 1.96/0.98  fof(f54,plain,(
% 1.96/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f17])).
% 1.96/0.98  
% 1.96/0.98  fof(f8,conjecture,(
% 1.96/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f9,negated_conjecture,(
% 1.96/0.98    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 1.96/0.98    inference(negated_conjecture,[],[f8])).
% 1.96/0.98  
% 1.96/0.98  fof(f21,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f9])).
% 1.96/0.98  
% 1.96/0.98  fof(f22,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f21])).
% 1.96/0.98  
% 1.96/0.98  fof(f37,plain,(
% 1.96/0.98    ( ! [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) => (k1_xboole_0 = k3_tarski(k4_orders_2(X0,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(X0))))) )),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f36,plain,(
% 1.96/0.98    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f38,plain,(
% 1.96/0.98    (k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) & m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f22,f37,f36])).
% 1.96/0.98  
% 1.96/0.98  fof(f63,plain,(
% 1.96/0.98    l1_orders_2(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f59,plain,(
% 1.96/0.98    ~v2_struct_0(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f60,plain,(
% 1.96/0.98    v3_orders_2(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f61,plain,(
% 1.96/0.98    v4_orders_2(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f62,plain,(
% 1.96/0.98    v5_orders_2(sK4)),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f2,axiom,(
% 1.96/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f11,plain,(
% 1.96/0.98    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 1.96/0.98    inference(ennf_transformation,[],[f2])).
% 1.96/0.98  
% 1.96/0.98  fof(f23,plain,(
% 1.96/0.98    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f24,plain,(
% 1.96/0.98    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK0(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK0(X0),X0)) | k1_xboole_0 = X0)),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f11,f23])).
% 1.96/0.98  
% 1.96/0.98  fof(f40,plain,(
% 1.96/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.96/0.98    inference(cnf_transformation,[],[f24])).
% 1.96/0.98  
% 1.96/0.98  fof(f65,plain,(
% 1.96/0.98    k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5))),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f7,axiom,(
% 1.96/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1)))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f10,plain,(
% 1.96/0.98    ! [X0] : (~(! [X1] : ~(r2_hidden(X1,X0) & k1_xboole_0 != X1) & k1_xboole_0 != k3_tarski(X0)) & ~(k1_xboole_0 = k3_tarski(X0) & ? [X2] : (r2_hidden(X2,X0) & k1_xboole_0 != X2)))),
% 1.96/0.98    inference(rectify,[],[f7])).
% 1.96/0.98  
% 1.96/0.98  fof(f20,plain,(
% 1.96/0.98    ! [X0] : ((? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.96/0.98    inference(ennf_transformation,[],[f10])).
% 1.96/0.98  
% 1.96/0.98  fof(f34,plain,(
% 1.96/0.98    ! [X0] : (? [X1] : (r2_hidden(X1,X0) & k1_xboole_0 != X1) => (r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f35,plain,(
% 1.96/0.98    ! [X0] : (((r2_hidden(sK3(X0),X0) & k1_xboole_0 != sK3(X0)) | k1_xboole_0 = k3_tarski(X0)) & (k1_xboole_0 != k3_tarski(X0) | ! [X2] : (~r2_hidden(X2,X0) | k1_xboole_0 = X2)))),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f34])).
% 1.96/0.98  
% 1.96/0.98  fof(f56,plain,(
% 1.96/0.98    ( ! [X2,X0] : (k1_xboole_0 != k3_tarski(X0) | ~r2_hidden(X2,X0) | k1_xboole_0 = X2) )),
% 1.96/0.98    inference(cnf_transformation,[],[f35])).
% 1.96/0.98  
% 1.96/0.98  fof(f64,plain,(
% 1.96/0.98    m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))),
% 1.96/0.98    inference(cnf_transformation,[],[f38])).
% 1.96/0.98  
% 1.96/0.98  fof(f1,axiom,(
% 1.96/0.98    v1_xboole_0(k1_xboole_0)),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f39,plain,(
% 1.96/0.98    v1_xboole_0(k1_xboole_0)),
% 1.96/0.98    inference(cnf_transformation,[],[f1])).
% 1.96/0.98  
% 1.96/0.98  fof(f6,axiom,(
% 1.96/0.98    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f18,plain,(
% 1.96/0.98    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f6])).
% 1.96/0.98  
% 1.96/0.98  fof(f19,plain,(
% 1.96/0.98    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f18])).
% 1.96/0.98  
% 1.96/0.98  fof(f55,plain,(
% 1.96/0.98    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f19])).
% 1.96/0.98  
% 1.96/0.98  fof(f4,axiom,(
% 1.96/0.98    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 1.96/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.96/0.98  
% 1.96/0.98  fof(f14,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.96/0.98    inference(ennf_transformation,[],[f4])).
% 1.96/0.98  
% 1.96/0.98  fof(f15,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(flattening,[],[f14])).
% 1.96/0.98  
% 1.96/0.98  fof(f30,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~m2_orders_2(X3,X0,X1)) & (m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(nnf_transformation,[],[f15])).
% 1.96/0.98  
% 1.96/0.98  fof(f31,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(rectify,[],[f30])).
% 1.96/0.98  
% 1.96/0.98  fof(f32,plain,(
% 1.96/0.98    ! [X2,X1,X0] : (? [X3] : ((~m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2)) & (m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2))) => ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.96/0.98    introduced(choice_axiom,[])).
% 1.96/0.98  
% 1.96/0.98  fof(f33,plain,(
% 1.96/0.98    ! [X0] : (! [X1] : (! [X2] : ((k4_orders_2(X0,X1) = X2 | ((~m2_orders_2(sK2(X0,X1,X2),X0,X1) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (m2_orders_2(sK2(X0,X1,X2),X0,X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~m2_orders_2(X4,X0,X1)) & (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2))) | k4_orders_2(X0,X1) != X2)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.96/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 1.96/0.98  
% 1.96/0.98  fof(f49,plain,(
% 1.96/0.98    ( ! [X4,X2,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,X2) | k4_orders_2(X0,X1) != X2 | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(cnf_transformation,[],[f33])).
% 1.96/0.98  
% 1.96/0.98  fof(f68,plain,(
% 1.96/0.98    ( ! [X4,X0,X1] : (m2_orders_2(X4,X0,X1) | ~r2_hidden(X4,k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.96/0.98    inference(equality_resolution,[],[f49])).
% 1.96/0.98  
% 1.96/0.98  cnf(c_15,plain,
% 1.96/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | v6_orders_2(X0,X1)
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X1) ),
% 1.96/0.98      inference(cnf_transformation,[],[f53]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_9,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ v6_orders_2(k1_xboole_0,X0)
% 1.96/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.98      | v2_struct_0(X0)
% 1.96/0.98      | ~ v3_orders_2(X0)
% 1.96/0.98      | ~ v4_orders_2(X0)
% 1.96/0.98      | ~ v5_orders_2(X0)
% 1.96/0.98      | ~ l1_orders_2(X0) ),
% 1.96/0.98      inference(cnf_transformation,[],[f66]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_452,plain,
% 1.96/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,X3,X4)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | ~ m1_orders_1(X4,k1_orders_1(u1_struct_0(X3)))
% 1.96/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X3)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | v2_struct_0(X3)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v3_orders_2(X3)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X3)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X3)
% 1.96/0.98      | ~ l1_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X3)
% 1.96/0.98      | X3 != X1
% 1.96/0.98      | k1_xboole_0 != X0 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_15,c_9]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_453,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.96/0.98      | v2_struct_0(X0)
% 1.96/0.98      | ~ v3_orders_2(X0)
% 1.96/0.98      | ~ v4_orders_2(X0)
% 1.96/0.98      | ~ v5_orders_2(X0)
% 1.96/0.98      | ~ l1_orders_2(X0) ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_452]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_14,plain,
% 1.96/0.98      ( ~ m2_orders_2(X0,X1,X2)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X1) ),
% 1.96/0.98      inference(cnf_transformation,[],[f54]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_477,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | v2_struct_0(X0)
% 1.96/0.98      | ~ v3_orders_2(X0)
% 1.96/0.98      | ~ v4_orders_2(X0)
% 1.96/0.98      | ~ v5_orders_2(X0)
% 1.96/0.98      | ~ l1_orders_2(X0) ),
% 1.96/0.98      inference(forward_subsumption_resolution,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_453,c_14]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_22,negated_conjecture,
% 1.96/0.98      ( l1_orders_2(sK4) ),
% 1.96/0.98      inference(cnf_transformation,[],[f63]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_805,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,X0,X2)
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
% 1.96/0.98      | v2_struct_0(X0)
% 1.96/0.98      | ~ v3_orders_2(X0)
% 1.96/0.98      | ~ v4_orders_2(X0)
% 1.96/0.98      | ~ v5_orders_2(X0)
% 1.96/0.98      | sK4 != X0 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_477,c_22]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_806,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X1)
% 1.96/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | v2_struct_0(sK4)
% 1.96/0.98      | ~ v3_orders_2(sK4)
% 1.96/0.98      | ~ v4_orders_2(sK4)
% 1.96/0.98      | ~ v5_orders_2(sK4) ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_805]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_26,negated_conjecture,
% 1.96/0.98      ( ~ v2_struct_0(sK4) ),
% 1.96/0.98      inference(cnf_transformation,[],[f59]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_25,negated_conjecture,
% 1.96/0.98      ( v3_orders_2(sK4) ),
% 1.96/0.98      inference(cnf_transformation,[],[f60]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_24,negated_conjecture,
% 1.96/0.98      ( v4_orders_2(sK4) ),
% 1.96/0.98      inference(cnf_transformation,[],[f61]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_23,negated_conjecture,
% 1.96/0.98      ( v5_orders_2(sK4) ),
% 1.96/0.98      inference(cnf_transformation,[],[f62]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_810,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X1)
% 1.96/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_806,c_26,c_25,c_24,c_23]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2489,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.96/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ sP0_iProver_split ),
% 1.96/0.98      inference(splitting,
% 1.96/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.96/0.98                [c_810]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2490,plain,
% 1.96/0.98      ( sP0_iProver_split ),
% 1.96/0.98      inference(splitting,
% 1.96/0.98                [splitting(split),new_symbols(definition,[])],
% 1.96/0.98                [c_810]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2574,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ m2_orders_2(k1_xboole_0,sK4,X0) ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_2489,c_2490]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2575,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,X0)
% 1.96/0.98      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4))) ),
% 1.96/0.98      inference(renaming,[status(thm)],[c_2574]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3803,plain,
% 1.96/0.98      ( ~ m2_orders_2(k1_xboole_0,sK4,sK5)
% 1.96/0.98      | ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.96/0.98      inference(instantiation,[status(thm)],[c_2575]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3,plain,
% 1.96/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.96/0.98      inference(cnf_transformation,[],[f40]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2855,plain,
% 1.96/0.98      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_20,negated_conjecture,
% 1.96/0.98      ( k1_xboole_0 = k3_tarski(k4_orders_2(sK4,sK5)) ),
% 1.96/0.98      inference(cnf_transformation,[],[f65]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_19,plain,
% 1.96/0.98      ( ~ r2_hidden(X0,X1)
% 1.96/0.98      | k3_tarski(X1) != k1_xboole_0
% 1.96/0.98      | k1_xboole_0 = X0 ),
% 1.96/0.98      inference(cnf_transformation,[],[f56]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2853,plain,
% 1.96/0.98      ( k3_tarski(X0) != k1_xboole_0
% 1.96/0.98      | k1_xboole_0 = X1
% 1.96/0.98      | r2_hidden(X1,X0) != iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3347,plain,
% 1.96/0.98      ( k1_xboole_0 = X0
% 1.96/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.96/0.98      inference(superposition,[status(thm)],[c_20,c_2853]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3352,plain,
% 1.96/0.98      ( k4_orders_2(sK4,sK5) = k1_xboole_0
% 1.96/0.98      | sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
% 1.96/0.98      inference(superposition,[status(thm)],[c_2855,c_3347]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_21,negated_conjecture,
% 1.96/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) ),
% 1.96/0.98      inference(cnf_transformation,[],[f64]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_0,plain,
% 1.96/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 1.96/0.98      inference(cnf_transformation,[],[f39]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_16,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X1)
% 1.96/0.98      | ~ v1_xboole_0(k4_orders_2(X1,X0)) ),
% 1.96/0.98      inference(cnf_transformation,[],[f55]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_295,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X1)
% 1.96/0.98      | k4_orders_2(X1,X0) != k1_xboole_0 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_697,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | k4_orders_2(X1,X0) != k1_xboole_0
% 1.96/0.98      | sK4 != X1 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_295,c_22]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_698,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | v2_struct_0(sK4)
% 1.96/0.98      | ~ v3_orders_2(sK4)
% 1.96/0.98      | ~ v4_orders_2(sK4)
% 1.96/0.98      | ~ v5_orders_2(sK4)
% 1.96/0.98      | k4_orders_2(sK4,X0) != k1_xboole_0 ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_697]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_702,plain,
% 1.96/0.98      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | k4_orders_2(sK4,X0) != k1_xboole_0 ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_698,c_26,c_25,c_24,c_23]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3023,plain,
% 1.96/0.98      ( ~ m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | k4_orders_2(sK4,sK5) != k1_xboole_0 ),
% 1.96/0.98      inference(instantiation,[status(thm)],[c_702]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3632,plain,
% 1.96/0.98      ( sK0(k4_orders_2(sK4,sK5)) = k1_xboole_0 ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_3352,c_21,c_3023]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3635,plain,
% 1.96/0.98      ( k4_orders_2(sK4,sK5) = k1_xboole_0
% 1.96/0.98      | r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5)) = iProver_top ),
% 1.96/0.98      inference(superposition,[status(thm)],[c_3632,c_2855]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3636,plain,
% 1.96/0.98      ( r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5))
% 1.96/0.98      | k4_orders_2(sK4,sK5) = k1_xboole_0 ),
% 1.96/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3635]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2852,plain,
% 1.96/0.98      ( m1_orders_1(sK5,k1_orders_1(u1_struct_0(sK4))) = iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_13,plain,
% 1.96/0.98      ( m2_orders_2(X0,X1,X2)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | ~ l1_orders_2(X1) ),
% 1.96/0.98      inference(cnf_transformation,[],[f68]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_763,plain,
% 1.96/0.98      ( m2_orders_2(X0,X1,X2)
% 1.96/0.98      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 1.96/0.98      | ~ r2_hidden(X0,k4_orders_2(X1,X2))
% 1.96/0.98      | v2_struct_0(X1)
% 1.96/0.98      | ~ v3_orders_2(X1)
% 1.96/0.98      | ~ v4_orders_2(X1)
% 1.96/0.98      | ~ v5_orders_2(X1)
% 1.96/0.98      | sK4 != X1 ),
% 1.96/0.98      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_764,plain,
% 1.96/0.98      ( m2_orders_2(X0,sK4,X1)
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ r2_hidden(X0,k4_orders_2(sK4,X1))
% 1.96/0.98      | v2_struct_0(sK4)
% 1.96/0.98      | ~ v3_orders_2(sK4)
% 1.96/0.98      | ~ v4_orders_2(sK4)
% 1.96/0.98      | ~ v5_orders_2(sK4) ),
% 1.96/0.98      inference(unflattening,[status(thm)],[c_763]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_768,plain,
% 1.96/0.98      ( m2_orders_2(X0,sK4,X1)
% 1.96/0.98      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4)))
% 1.96/0.98      | ~ r2_hidden(X0,k4_orders_2(sK4,X1)) ),
% 1.96/0.98      inference(global_propositional_subsumption,
% 1.96/0.98                [status(thm)],
% 1.96/0.98                [c_764,c_26,c_25,c_24,c_23]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_2845,plain,
% 1.96/0.98      ( m2_orders_2(X0,sK4,X1) = iProver_top
% 1.96/0.98      | m1_orders_1(X1,k1_orders_1(u1_struct_0(sK4))) != iProver_top
% 1.96/0.98      | r2_hidden(X0,k4_orders_2(sK4,X1)) != iProver_top ),
% 1.96/0.98      inference(predicate_to_equality,[status(thm)],[c_768]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3080,plain,
% 1.96/0.98      ( m2_orders_2(X0,sK4,sK5) = iProver_top
% 1.96/0.98      | r2_hidden(X0,k4_orders_2(sK4,sK5)) != iProver_top ),
% 1.96/0.98      inference(superposition,[status(thm)],[c_2852,c_2845]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3081,plain,
% 1.96/0.98      ( m2_orders_2(X0,sK4,sK5) | ~ r2_hidden(X0,k4_orders_2(sK4,sK5)) ),
% 1.96/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_3080]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(c_3083,plain,
% 1.96/0.98      ( m2_orders_2(k1_xboole_0,sK4,sK5)
% 1.96/0.98      | ~ r2_hidden(k1_xboole_0,k4_orders_2(sK4,sK5)) ),
% 1.96/0.98      inference(instantiation,[status(thm)],[c_3081]) ).
% 1.96/0.98  
% 1.96/0.98  cnf(contradiction,plain,
% 1.96/0.98      ( $false ),
% 1.96/0.98      inference(minisat,[status(thm)],[c_3803,c_3636,c_3083,c_3023,c_21]) ).
% 1.96/0.98  
% 1.96/0.98  
% 1.96/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 1.96/0.98  
% 1.96/0.98  ------                               Statistics
% 1.96/0.98  
% 1.96/0.98  ------ General
% 1.96/0.98  
% 1.96/0.98  abstr_ref_over_cycles:                  0
% 1.96/0.98  abstr_ref_under_cycles:                 0
% 1.96/0.98  gc_basic_clause_elim:                   0
% 1.96/0.98  forced_gc_time:                         0
% 1.96/0.98  parsing_time:                           0.011
% 1.96/0.98  unif_index_cands_time:                  0.
% 1.96/0.98  unif_index_add_time:                    0.
% 1.96/0.98  orderings_time:                         0.
% 1.96/0.98  out_proof_time:                         0.008
% 1.96/0.98  total_time:                             0.164
% 1.96/0.98  num_of_symbols:                         61
% 1.96/0.98  num_of_terms:                           2759
% 1.96/0.98  
% 1.96/0.98  ------ Preprocessing
% 1.96/0.98  
% 1.96/0.98  num_of_splits:                          2
% 1.96/0.98  num_of_split_atoms:                     1
% 1.96/0.98  num_of_reused_defs:                     1
% 1.96/0.98  num_eq_ax_congr_red:                    41
% 1.96/0.98  num_of_sem_filtered_clauses:            2
% 1.96/0.98  num_of_subtypes:                        0
% 1.96/0.98  monotx_restored_types:                  0
% 1.96/0.98  sat_num_of_epr_types:                   0
% 1.96/0.98  sat_num_of_non_cyclic_types:            0
% 1.96/0.98  sat_guarded_non_collapsed_types:        0
% 1.96/0.98  num_pure_diseq_elim:                    0
% 1.96/0.98  simp_replaced_by:                       0
% 1.96/0.98  res_preprocessed:                       118
% 1.96/0.98  prep_upred:                             0
% 1.96/0.98  prep_unflattend:                        125
% 1.96/0.98  smt_new_axioms:                         0
% 1.96/0.98  pred_elim_cands:                        4
% 1.96/0.98  pred_elim:                              8
% 1.96/0.98  pred_elim_cl:                           8
% 1.96/0.98  pred_elim_cycles:                       13
% 1.96/0.98  merged_defs:                            0
% 1.96/0.98  merged_defs_ncl:                        0
% 1.96/0.98  bin_hyper_res:                          0
% 1.96/0.98  prep_cycles:                            4
% 1.96/0.98  pred_elim_time:                         0.046
% 1.96/0.98  splitting_time:                         0.
% 1.96/0.98  sem_filter_time:                        0.
% 1.96/0.98  monotx_time:                            0.
% 1.96/0.98  subtype_inf_time:                       0.
% 1.96/0.98  
% 1.96/0.98  ------ Problem properties
% 1.96/0.98  
% 1.96/0.98  clauses:                                21
% 1.96/0.98  conjectures:                            2
% 1.96/0.98  epr:                                    1
% 1.96/0.98  horn:                                   15
% 1.96/0.98  ground:                                 3
% 1.96/0.98  unary:                                  3
% 1.96/0.98  binary:                                 4
% 1.96/0.98  lits:                                   66
% 1.96/0.98  lits_eq:                                19
% 1.96/0.98  fd_pure:                                0
% 1.96/0.98  fd_pseudo:                              0
% 1.96/0.98  fd_cond:                                7
% 1.96/0.98  fd_pseudo_cond:                         2
% 1.96/0.98  ac_symbols:                             0
% 1.96/0.98  
% 1.96/0.98  ------ Propositional Solver
% 1.96/0.98  
% 1.96/0.98  prop_solver_calls:                      27
% 1.96/0.98  prop_fast_solver_calls:                 1481
% 1.96/0.98  smt_solver_calls:                       0
% 1.96/0.98  smt_fast_solver_calls:                  0
% 1.96/0.98  prop_num_of_clauses:                    686
% 1.96/0.98  prop_preprocess_simplified:             4085
% 1.96/0.98  prop_fo_subsumed:                       57
% 1.96/0.98  prop_solver_time:                       0.
% 1.96/0.98  smt_solver_time:                        0.
% 1.96/0.98  smt_fast_solver_time:                   0.
% 1.96/0.98  prop_fast_solver_time:                  0.
% 1.96/0.98  prop_unsat_core_time:                   0.
% 1.96/0.98  
% 1.96/0.98  ------ QBF
% 1.96/0.98  
% 1.96/0.98  qbf_q_res:                              0
% 1.96/0.98  qbf_num_tautologies:                    0
% 1.96/0.98  qbf_prep_cycles:                        0
% 1.96/0.99  
% 1.96/0.99  ------ BMC1
% 1.96/0.99  
% 1.96/0.99  bmc1_current_bound:                     -1
% 1.96/0.99  bmc1_last_solved_bound:                 -1
% 1.96/0.99  bmc1_unsat_core_size:                   -1
% 1.96/0.99  bmc1_unsat_core_parents_size:           -1
% 1.96/0.99  bmc1_merge_next_fun:                    0
% 1.96/0.99  bmc1_unsat_core_clauses_time:           0.
% 1.96/0.99  
% 1.96/0.99  ------ Instantiation
% 1.96/0.99  
% 1.96/0.99  inst_num_of_clauses:                    169
% 1.96/0.99  inst_num_in_passive:                    75
% 1.96/0.99  inst_num_in_active:                     77
% 1.96/0.99  inst_num_in_unprocessed:                16
% 1.96/0.99  inst_num_of_loops:                      112
% 1.96/0.99  inst_num_of_learning_restarts:          0
% 1.96/0.99  inst_num_moves_active_passive:          31
% 1.96/0.99  inst_lit_activity:                      0
% 1.96/0.99  inst_lit_activity_moves:                0
% 1.96/0.99  inst_num_tautologies:                   0
% 1.96/0.99  inst_num_prop_implied:                  0
% 1.96/0.99  inst_num_existing_simplified:           0
% 1.96/0.99  inst_num_eq_res_simplified:             0
% 1.96/0.99  inst_num_child_elim:                    0
% 1.96/0.99  inst_num_of_dismatching_blockings:      12
% 1.96/0.99  inst_num_of_non_proper_insts:           88
% 1.96/0.99  inst_num_of_duplicates:                 0
% 1.96/0.99  inst_inst_num_from_inst_to_res:         0
% 1.96/0.99  inst_dismatching_checking_time:         0.
% 1.96/0.99  
% 1.96/0.99  ------ Resolution
% 1.96/0.99  
% 1.96/0.99  res_num_of_clauses:                     0
% 1.96/0.99  res_num_in_passive:                     0
% 1.96/0.99  res_num_in_active:                      0
% 1.96/0.99  res_num_of_loops:                       122
% 1.96/0.99  res_forward_subset_subsumed:            12
% 1.96/0.99  res_backward_subset_subsumed:           0
% 1.96/0.99  res_forward_subsumed:                   0
% 1.96/0.99  res_backward_subsumed:                  0
% 1.96/0.99  res_forward_subsumption_resolution:     3
% 1.96/0.99  res_backward_subsumption_resolution:    0
% 1.96/0.99  res_clause_to_clause_subsumption:       76
% 1.96/0.99  res_orphan_elimination:                 0
% 1.96/0.99  res_tautology_del:                      10
% 1.96/0.99  res_num_eq_res_simplified:              0
% 1.96/0.99  res_num_sel_changes:                    0
% 1.96/0.99  res_moves_from_active_to_pass:          0
% 1.96/0.99  
% 1.96/0.99  ------ Superposition
% 1.96/0.99  
% 1.96/0.99  sup_time_total:                         0.
% 1.96/0.99  sup_time_generating:                    0.
% 1.96/0.99  sup_time_sim_full:                      0.
% 1.96/0.99  sup_time_sim_immed:                     0.
% 1.96/0.99  
% 1.96/0.99  sup_num_of_clauses:                     34
% 1.96/0.99  sup_num_in_active:                      22
% 1.96/0.99  sup_num_in_passive:                     12
% 1.96/0.99  sup_num_of_loops:                       22
% 1.96/0.99  sup_fw_superposition:                   10
% 1.96/0.99  sup_bw_superposition:                   8
% 1.96/0.99  sup_immediate_simplified:               3
% 1.96/0.99  sup_given_eliminated:                   0
% 1.96/0.99  comparisons_done:                       0
% 1.96/0.99  comparisons_avoided:                    0
% 1.96/0.99  
% 1.96/0.99  ------ Simplifications
% 1.96/0.99  
% 1.96/0.99  
% 1.96/0.99  sim_fw_subset_subsumed:                 1
% 1.96/0.99  sim_bw_subset_subsumed:                 0
% 1.96/0.99  sim_fw_subsumed:                        1
% 1.96/0.99  sim_bw_subsumed:                        0
% 1.96/0.99  sim_fw_subsumption_res:                 1
% 1.96/0.99  sim_bw_subsumption_res:                 0
% 1.96/0.99  sim_tautology_del:                      1
% 1.96/0.99  sim_eq_tautology_del:                   2
% 1.96/0.99  sim_eq_res_simp:                        0
% 1.96/0.99  sim_fw_demodulated:                     2
% 1.96/0.99  sim_bw_demodulated:                     0
% 1.96/0.99  sim_light_normalised:                   0
% 1.96/0.99  sim_joinable_taut:                      0
% 1.96/0.99  sim_joinable_simp:                      0
% 1.96/0.99  sim_ac_normalised:                      0
% 1.96/0.99  sim_smt_subsumption:                    0
% 1.96/0.99  
%------------------------------------------------------------------------------
