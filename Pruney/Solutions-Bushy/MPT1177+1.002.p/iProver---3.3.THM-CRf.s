%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1177+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:05 EST 2020

% Result     : Theorem 11.55s
% Output     : CNFRefutation 11.55s
% Verified   : 
% Statistics : Number of formulae       :  326 (1831697 expanded)
%              Number of clauses        :  243 (324881 expanded)
%              Number of leaves         :   25 (601021 expanded)
%              Depth                    :   49
%              Number of atoms          : 1602 (18539572 expanded)
%              Number of equality atoms :  548 (544163 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_orders_2(X2,X0,X3)
            | ~ r2_xboole_0(X2,X3) )
          & ( m1_orders_2(X2,X0,X3)
            | r2_xboole_0(X2,X3) )
          & m2_orders_2(X3,X0,X1) )
     => ( ( ~ m1_orders_2(X2,X0,sK5)
          | ~ r2_xboole_0(X2,sK5) )
        & ( m1_orders_2(X2,X0,sK5)
          | r2_xboole_0(X2,sK5) )
        & m2_orders_2(sK5,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,X0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,X0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,X0,X1) )
          & m2_orders_2(X2,X0,X1) )
     => ( ? [X3] :
            ( ( ~ m1_orders_2(sK4,X0,X3)
              | ~ r2_xboole_0(sK4,X3) )
            & ( m1_orders_2(sK4,X0,X3)
              | r2_xboole_0(sK4,X3) )
            & m2_orders_2(X3,X0,X1) )
        & m2_orders_2(sK4,X0,X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,X0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,X0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,X0,sK3) )
            & m2_orders_2(X2,X0,sK3) )
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK2,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK2,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK2,X1) )
              & m2_orders_2(X2,sK2,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ m1_orders_2(sK4,sK2,sK5)
      | ~ r2_xboole_0(sK4,sK5) )
    & ( m1_orders_2(sK4,sK2,sK5)
      | r2_xboole_0(sK4,sK5) )
    & m2_orders_2(sK5,sK2,sK3)
    & m2_orders_2(sK4,sK2,sK3)
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f50,f54,f53,f52,f51])).

fof(f94,plain,
    ( m1_orders_2(sK4,sK2,sK5)
    | r2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f89,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f21,plain,(
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,(
    m2_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f93,plain,(
    m2_orders_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_orders_2(X2,X0,X3)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,X2) = k9_subset_1(u1_struct_0(X0),k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK1(X0,X1,X2)))) != sK1(X0,X1,X2)
        & r2_hidden(sK1(X0,X1,X2),X2)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f42,f43])).

fof(f65,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
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
    inference(equality_resolution,[],[f65])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f61,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
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

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_2(X1,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f39])).

fof(f99,plain,(
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
    inference(equality_resolution,[],[f62])).

fof(f95,plain,
    ( ~ m1_orders_2(sK4,sK2,sK5)
    | ~ r2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_31,negated_conjecture,
    ( m1_orders_2(sK4,sK2,sK5)
    | r2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2932,plain,
    ( m1_orders_2(sK4,sK2,sK5) = iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_34,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2929,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_19,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_35,negated_conjecture,
    ( l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1275,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_1276,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_1275])).

cnf(c_39,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_38,negated_conjecture,
    ( v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_37,negated_conjecture,
    ( v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_36,negated_conjecture,
    ( v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1280,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1276,c_39,c_38,c_37,c_36])).

cnf(c_2917,plain,
    ( m2_orders_2(X0,sK2,X1) != iProver_top
    | m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1280])).

cnf(c_3697,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_2917])).

cnf(c_8,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_18,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_238,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_18])).

cnf(c_239,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_238])).

cnf(c_1143,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_239,c_35])).

cnf(c_1144,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X1,X0),u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_1143])).

cnf(c_1148,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X1,X0),u1_struct_0(sK2))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1144,c_39,c_38,c_37,c_36])).

cnf(c_2922,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0,X1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1148])).

cnf(c_33,negated_conjecture,
    ( m2_orders_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2930,plain,
    ( m2_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( m2_orders_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2931,plain,
    ( m2_orders_2(sK5,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | X3 = X0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1224,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m2_orders_2(X3,X1,X2)
    | m1_orders_2(X3,X1,X0)
    | m1_orders_2(X0,X1,X3)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | X3 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_35])).

cnf(c_1225,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m2_orders_2(X2,sK2,X1)
    | m1_orders_2(X0,sK2,X2)
    | m1_orders_2(X2,sK2,X0)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | X2 = X0 ),
    inference(unflattening,[status(thm)],[c_1224])).

cnf(c_1229,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m2_orders_2(X2,sK2,X1)
    | m1_orders_2(X0,sK2,X2)
    | m1_orders_2(X2,sK2,X0)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | X2 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1225,c_39,c_38,c_37,c_36])).

cnf(c_2919,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK2,X2) != iProver_top
    | m2_orders_2(X0,sK2,X2) != iProver_top
    | m1_orders_2(X1,sK2,X0) = iProver_top
    | m1_orders_2(X0,sK2,X1) = iProver_top
    | m1_orders_1(X2,k1_orders_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1229])).

cnf(c_4368,plain,
    ( X0 = X1
    | m2_orders_2(X1,sK2,sK3) != iProver_top
    | m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_orders_2(X1,sK2,X0) = iProver_top
    | m1_orders_2(X0,sK2,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_2919])).

cnf(c_4719,plain,
    ( sK5 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_orders_2(X0,sK2,sK5) = iProver_top
    | m1_orders_2(sK5,sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2931,c_4368])).

cnf(c_4725,plain,
    ( sK5 = sK4
    | m1_orders_2(sK5,sK2,sK4) = iProver_top
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_4719])).

cnf(c_1296,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_1297,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_1296])).

cnf(c_1299,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1297,c_39,c_38,c_37,c_36])).

cnf(c_2916,plain,
    ( m1_orders_2(X0,sK2,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1299])).

cnf(c_3700,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_2916])).

cnf(c_5157,plain,
    ( sK5 = sK4
    | m2_orders_2(sK4,sK2,sK3) != iProver_top
    | m1_orders_2(sK4,sK2,sK5) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_3700])).

cnf(c_45,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_47,plain,
    ( m2_orders_2(sK5,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3010,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_3036,plain,
    ( ~ m2_orders_2(sK5,sK2,sK3)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_3037,plain,
    ( m2_orders_2(sK5,sK2,sK3) != iProver_top
    | m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3036])).

cnf(c_6294,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5157,c_45,c_47,c_3037])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X0) = k3_orders_2(X1,X0,X2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1332,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k9_subset_1(u1_struct_0(X1),k2_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)),X0) = k3_orders_2(X1,X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_35])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X0) = k3_orders_2(sK2,X0,X1) ),
    inference(unflattening,[status(thm)],[c_1332])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)),X0) = k3_orders_2(sK2,X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1333,c_39,c_38,c_37,c_36])).

cnf(c_2914,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),X1) = k3_orders_2(sK2,X1,X0)
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1337])).

cnf(c_6299,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK5) = k3_orders_2(sK2,sK5,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6294,c_2914])).

cnf(c_6495,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2922,c_6299])).

cnf(c_25,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2934,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3933,plain,
    ( m2_orders_2(X0,sK2,sK3) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_2934])).

cnf(c_5211,plain,
    ( r1_tarski(sK5,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2931,c_3933])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_303,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_387,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_22,c_303])).

cnf(c_2928,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_6805,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_5211,c_2928])).

cnf(c_8921,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6495,c_6805])).

cnf(c_8926,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_orders_2(X1,sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_8921])).

cnf(c_9684,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4))
    | sK5 = k1_xboole_0
    | m2_orders_2(sK5,sK2,sK3) != iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_8926])).

cnf(c_2138,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2177,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2139,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3374,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3375,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3374])).

cnf(c_20,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | v6_orders_2(X0,X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_14,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ v6_orders_2(k1_xboole_0,X0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_737,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_14])).

cnf(c_738,plain,
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
    inference(unflattening,[status(thm)],[c_737])).

cnf(c_762,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_738,c_19])).

cnf(c_1353,plain,
    ( ~ m2_orders_2(k1_xboole_0,X0,X1)
    | ~ m2_orders_2(k1_xboole_0,X0,X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_762,c_35])).

cnf(c_1354,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK2,X0)
    | ~ m2_orders_2(k1_xboole_0,sK2,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2) ),
    inference(unflattening,[status(thm)],[c_1353])).

cnf(c_1358,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK2,X0)
    | ~ m2_orders_2(k1_xboole_0,sK2,X1)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2)))
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1354,c_39,c_38,c_37,c_36])).

cnf(c_2135,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK2,X0)
    | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1358])).

cnf(c_2912,plain,
    ( m2_orders_2(k1_xboole_0,sK2,X0) != iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_2136,plain,
    ( sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1358])).

cnf(c_2180,plain,
    ( sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2136])).

cnf(c_2181,plain,
    ( m2_orders_2(k1_xboole_0,sK2,X0) != iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2135])).

cnf(c_3501,plain,
    ( m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | m2_orders_2(k1_xboole_0,sK2,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2912,c_2180,c_2181])).

cnf(c_3502,plain,
    ( m2_orders_2(k1_xboole_0,sK2,X0) != iProver_top
    | m1_orders_1(X0,k1_orders_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3501])).

cnf(c_3505,plain,
    ( m2_orders_2(k1_xboole_0,sK2,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2929,c_3502])).

cnf(c_3506,plain,
    ( ~ m2_orders_2(k1_xboole_0,sK2,sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3505])).

cnf(c_3717,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_3722,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2151,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3042,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | m2_orders_2(X3,sK2,sK3)
    | X3 != X0
    | sK3 != X2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_3263,plain,
    ( ~ m2_orders_2(X0,X1,sK3)
    | m2_orders_2(X2,sK2,sK3)
    | X2 != X0
    | sK3 != sK3
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_3042])).

cnf(c_4334,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | m2_orders_2(X1,sK2,sK3)
    | X1 != X0
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_3263])).

cnf(c_5702,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | ~ m2_orders_2(sK5,sK2,sK3)
    | X0 != sK5
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4334])).

cnf(c_5704,plain,
    ( ~ m2_orders_2(sK5,sK2,sK3)
    | m2_orders_2(k1_xboole_0,sK2,sK3)
    | sK3 != sK3
    | sK2 != sK2
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_5702])).

cnf(c_9691,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4))
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9684,c_32,c_47,c_2177,c_3375,c_3506,c_3717,c_3722,c_5704])).

cnf(c_17,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2937,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9696,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4))
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_9691,c_2937])).

cnf(c_9839,plain,
    ( k9_subset_1(sK5,X0,sK4) = k3_xboole_0(X0,sK4)
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_9696,c_2928])).

cnf(c_3126,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2140,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3485,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(X2,sK5)
    | X2 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_4173,plain,
    ( ~ r2_xboole_0(X0,sK5)
    | r2_xboole_0(X1,sK5)
    | X1 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3485])).

cnf(c_6727,plain,
    ( r2_xboole_0(X0,sK5)
    | ~ r2_xboole_0(sK4,sK5)
    | X0 != sK4
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_4173])).

cnf(c_14048,plain,
    ( r2_xboole_0(sK5,sK5)
    | ~ r2_xboole_0(sK4,sK5)
    | sK5 != sK5
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_6727])).

cnf(c_14049,plain,
    ( sK5 != sK5
    | sK5 != sK4
    | r2_xboole_0(sK5,sK5) = iProver_top
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14048])).

cnf(c_0,plain,
    ( ~ r2_xboole_0(X0,X1)
    | ~ r2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27880,plain,
    ( ~ r2_xboole_0(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_27881,plain,
    ( r2_xboole_0(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27880])).

cnf(c_5156,plain,
    ( m2_orders_2(sK5,sK2,sK3) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_3700])).

cnf(c_46,plain,
    ( m2_orders_2(sK4,sK2,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3039,plain,
    ( ~ m2_orders_2(sK4,sK2,sK3)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_3010])).

cnf(c_3040,plain,
    ( m2_orders_2(sK4,sK2,sK3) != iProver_top
    | m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3039])).

cnf(c_5247,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5156,c_45,c_46,c_3040])).

cnf(c_5252,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X0)),sK4) = k3_orders_2(sK2,sK4,X0)
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5247,c_2914])).

cnf(c_5569,plain,
    ( k9_subset_1(u1_struct_0(sK2),k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2922,c_5252])).

cnf(c_5212,plain,
    ( r1_tarski(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2930,c_3933])).

cnf(c_6806,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK4) = k3_xboole_0(X0,sK4) ),
    inference(superposition,[status(thm)],[c_5212,c_2928])).

cnf(c_7518,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5569,c_6806])).

cnf(c_7523,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,X0,X1))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,X0,X1))
    | k1_xboole_0 = X0
    | m2_orders_2(X0,sK2,sK3) != iProver_top
    | m1_orders_2(X1,sK2,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_7518])).

cnf(c_8558,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK5,sK4))
    | sK5 = k1_xboole_0
    | m2_orders_2(sK5,sK2,sK3) != iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_7523])).

cnf(c_8606,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK5,sK4))
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8558,c_32,c_47,c_2177,c_3375,c_3506,c_3717,c_3722,c_5704])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f61])).

cnf(c_248,plain,
    ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X0,X1,X2)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_18])).

cnf(c_249,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_1095,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK2 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_249,c_35])).

cnf(c_1096,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k3_orders_2(sK2,X1,sK0(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_1095])).

cnf(c_1100,plain,
    ( ~ m1_orders_2(X0,sK2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,X1,sK0(sK2,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_39,c_38,c_37,c_36])).

cnf(c_2924,plain,
    ( k3_orders_2(sK2,X0,sK0(sK2,X0,X1)) = X1
    | k1_xboole_0 = X0
    | m1_orders_2(X1,sK2,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1100])).

cnf(c_5254,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0)) = X0
    | sK4 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5247,c_2924])).

cnf(c_4115,plain,
    ( ~ m1_orders_2(X0,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0)) = X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_4126,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0)) = X0
    | k1_xboole_0 = sK4
    | m1_orders_2(X0,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4115])).

cnf(c_5707,plain,
    ( m2_orders_2(X0,sK2,sK3)
    | ~ m2_orders_2(sK4,sK2,sK3)
    | X0 != sK4
    | sK3 != sK3
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4334])).

cnf(c_5709,plain,
    ( ~ m2_orders_2(sK4,sK2,sK3)
    | m2_orders_2(k1_xboole_0,sK2,sK3)
    | sK3 != sK3
    | sK2 != sK2
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_5707])).

cnf(c_5820,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0)) = X0
    | m1_orders_2(X0,sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5254,c_45,c_33,c_46,c_3040,c_3506,c_3717,c_3722,c_4126,c_5709])).

cnf(c_5826,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | sK5 = sK4
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_5820])).

cnf(c_6301,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,X0)) = X0
    | sK5 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6294,c_2924])).

cnf(c_3899,plain,
    ( ~ m1_orders_2(X0,sK2,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,sK5,sK0(sK2,sK5,X0)) = X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1100])).

cnf(c_3910,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,X0)) = X0
    | k1_xboole_0 = sK5
    | m1_orders_2(X0,sK2,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3899])).

cnf(c_6930,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,X0)) = X0
    | m1_orders_2(X0,sK2,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6301,c_45,c_32,c_47,c_3037,c_3506,c_3717,c_3722,c_3910,c_5704])).

cnf(c_6936,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_5826,c_6930])).

cnf(c_27,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1254,plain,
    ( ~ m1_orders_2(X0,X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK2 != X1
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_1255,plain,
    ( ~ m1_orders_2(X0,sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1254])).

cnf(c_1259,plain,
    ( ~ m1_orders_2(X0,sK2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1255,c_39,c_38,c_37,c_36])).

cnf(c_4100,plain,
    ( ~ m1_orders_2(sK4,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_4158,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m2_orders_2(sK4,sK2,X1)
    | m1_orders_2(X0,sK2,sK4)
    | m1_orders_2(sK4,sK2,X0)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_5443,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | ~ m2_orders_2(sK4,sK2,sK3)
    | m1_orders_2(X0,sK2,sK4)
    | m1_orders_2(sK4,sK2,X0)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4158])).

cnf(c_6489,plain,
    ( ~ m2_orders_2(sK4,sK2,sK3)
    | m1_orders_2(sK4,sK2,sK4)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_5443])).

cnf(c_6937,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_6930])).

cnf(c_6938,plain,
    ( r2_xboole_0(sK4,sK5)
    | k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6937])).

cnf(c_2940,plain,
    ( r2_xboole_0(X0,X1) != iProver_top
    | r2_xboole_0(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7053,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | r2_xboole_0(sK5,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6937,c_2940])).

cnf(c_7056,plain,
    ( ~ r2_xboole_0(sK5,sK4)
    | k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7053])).

cnf(c_5432,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_7165,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_5432])).

cnf(c_8738,plain,
    ( sK5 != sK4
    | sK4 = sK5
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_7165])).

cnf(c_3507,plain,
    ( ~ r2_xboole_0(X0,X1)
    | r2_xboole_0(sK5,X2)
    | X2 != X1
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_2140])).

cnf(c_6767,plain,
    ( r2_xboole_0(sK5,X0)
    | ~ r2_xboole_0(sK4,X1)
    | X0 != X1
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_3507])).

cnf(c_13973,plain,
    ( r2_xboole_0(sK5,X0)
    | ~ r2_xboole_0(sK4,sK5)
    | X0 != sK5
    | sK5 != sK4 ),
    inference(instantiation,[status(thm)],[c_6767])).

cnf(c_25066,plain,
    ( r2_xboole_0(sK5,sK4)
    | ~ r2_xboole_0(sK4,sK5)
    | sK5 != sK4
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_13973])).

cnf(c_25076,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6936,c_34,c_33,c_3039,c_3506,c_3717,c_3722,c_4100,c_5709,c_6489,c_6938,c_7056,c_8738,c_25066])).

cnf(c_25077,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5 ),
    inference(renaming,[status(thm)],[c_25076])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f99])).

cnf(c_1377,plain,
    ( m1_orders_2(k3_orders_2(X0,X1,X2),X0,X1)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK2 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_35])).

cnf(c_1378,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v3_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_1377])).

cnf(c_1382,plain,
    ( m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0)
    | ~ r2_hidden(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,u1_struct_0(sK2))
    | ~ m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1378,c_39,c_38,c_37,c_36])).

cnf(c_2910,plain,
    ( k1_xboole_0 = X0
    | m1_orders_2(k3_orders_2(sK2,X0,X1),sK2,X0) = iProver_top
    | r2_hidden(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k3_orders_2(sK2,X0,X1),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_25082,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | sK5 = k1_xboole_0
    | m1_orders_2(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK2,sK5) = iProver_top
    | r2_hidden(sK0(sK2,sK5,sK4),sK5) != iProver_top
    | m1_subset_1(sK0(sK2,sK5,sK4),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25077,c_2910])).

cnf(c_48,plain,
    ( m1_orders_2(sK4,sK2,sK5) = iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3362,plain,
    ( ~ m2_orders_2(X0,sK2,X1)
    | ~ m2_orders_2(sK5,sK2,X1)
    | m1_orders_2(X0,sK2,sK5)
    | m1_orders_2(sK5,sK2,X0)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK2)))
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1229])).

cnf(c_3970,plain,
    ( ~ m2_orders_2(X0,sK2,sK3)
    | ~ m2_orders_2(sK5,sK2,sK3)
    | m1_orders_2(X0,sK2,sK5)
    | m1_orders_2(sK5,sK2,X0)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_4802,plain,
    ( ~ m2_orders_2(sK5,sK2,sK3)
    | ~ m2_orders_2(sK4,sK2,sK3)
    | m1_orders_2(sK5,sK2,sK4)
    | m1_orders_2(sK4,sK2,sK5)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2)))
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_3970])).

cnf(c_4803,plain,
    ( sK4 = sK5
    | m2_orders_2(sK5,sK2,sK3) != iProver_top
    | m2_orders_2(sK4,sK2,sK3) != iProver_top
    | m1_orders_2(sK5,sK2,sK4) = iProver_top
    | m1_orders_2(sK4,sK2,sK5) = iProver_top
    | m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4802])).

cnf(c_6735,plain,
    ( ~ r2_xboole_0(sK5,sK4)
    | ~ r2_xboole_0(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_6736,plain,
    ( r2_xboole_0(sK5,sK4) != iProver_top
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6735])).

cnf(c_6740,plain,
    ( ~ m1_orders_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_4115])).

cnf(c_6750,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | k1_xboole_0 = sK4
    | m1_orders_2(sK5,sK2,sK4) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6740])).

cnf(c_2148,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_3335,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | m1_orders_2(X3,sK2,sK5)
    | X3 != X0
    | sK5 != X2
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_2148])).

cnf(c_4186,plain,
    ( ~ m1_orders_2(X0,X1,sK5)
    | m1_orders_2(X2,sK2,sK5)
    | X2 != X0
    | sK5 != sK5
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_3335])).

cnf(c_5766,plain,
    ( ~ m1_orders_2(X0,sK2,sK5)
    | m1_orders_2(X1,sK2,sK5)
    | X1 != X0
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_4186])).

cnf(c_8505,plain,
    ( m1_orders_2(X0,sK2,sK5)
    | ~ m1_orders_2(sK4,sK2,sK5)
    | X0 != sK4
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_5766])).

cnf(c_13197,plain,
    ( m1_orders_2(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK2,sK5)
    | ~ m1_orders_2(sK4,sK2,sK5)
    | k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) != sK4
    | sK5 != sK5
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8505])).

cnf(c_13198,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) != sK4
    | sK5 != sK5
    | sK2 != sK2
    | m1_orders_2(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK2,sK5) = iProver_top
    | m1_orders_2(sK4,sK2,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13197])).

cnf(c_25067,plain,
    ( sK5 != sK4
    | sK4 != sK5
    | r2_xboole_0(sK5,sK4) = iProver_top
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25066])).

cnf(c_26649,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | m1_orders_2(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25082,c_34,c_45,c_33,c_46,c_47,c_48,c_3039,c_3040,c_3126,c_3506,c_3717,c_3722,c_4100,c_4803,c_5709,c_5826,c_6489,c_6736,c_6750,c_6936,c_6938,c_7056,c_8738,c_13198,c_25066,c_25067])).

cnf(c_26653,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_25077,c_26649])).

cnf(c_30,negated_conjecture,
    ( ~ m1_orders_2(sK4,sK2,sK5)
    | ~ r2_xboole_0(sK4,sK5) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2933,plain,
    ( m1_orders_2(sK4,sK2,sK5) != iProver_top
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_26794,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_26653,c_2933])).

cnf(c_26834,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_8606,c_26794])).

cnf(c_1,plain,
    ( k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2936,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3452,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1,c_2936])).

cnf(c_27092,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | r1_tarski(k3_orders_2(sK2,sK4,sK0(sK2,sK5,sK4)),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_26834,c_3452])).

cnf(c_3346,plain,
    ( ~ m1_orders_2(sK5,sK2,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1259])).

cnf(c_3347,plain,
    ( k1_xboole_0 = sK5
    | m1_orders_2(sK5,sK2,sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3346])).

cnf(c_13193,plain,
    ( m1_orders_2(sK5,sK2,sK5)
    | ~ m1_orders_2(sK4,sK2,sK5)
    | sK5 != sK5
    | sK5 != sK4
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_8505])).

cnf(c_13194,plain,
    ( sK5 != sK5
    | sK5 != sK4
    | sK2 != sK2
    | m1_orders_2(sK5,sK2,sK5) = iProver_top
    | m1_orders_2(sK4,sK2,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13193])).

cnf(c_3063,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_3166,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_3063])).

cnf(c_13860,plain,
    ( sK5 != sK5
    | sK5 = sK4
    | sK4 != sK5 ),
    inference(instantiation,[status(thm)],[c_3166])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,X1)
    | r2_xboole_0(X0,X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3368,plain,
    ( ~ r1_tarski(X0,sK5)
    | r2_xboole_0(X0,sK5)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14022,plain,
    ( ~ r1_tarski(sK4,sK5)
    | r2_xboole_0(sK4,sK5)
    | sK4 = sK5 ),
    inference(instantiation,[status(thm)],[c_3368])).

cnf(c_14023,plain,
    ( sK4 = sK5
    | r1_tarski(sK4,sK5) != iProver_top
    | r2_xboole_0(sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14022])).

cnf(c_26833,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) ),
    inference(superposition,[status(thm)],[c_9691,c_26794])).

cnf(c_26901,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | r1_tarski(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_26833,c_3452])).

cnf(c_28720,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_25077,c_26901])).

cnf(c_28728,plain,
    ( k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27092,c_45,c_32,c_47,c_3037,c_3126,c_3347,c_3506,c_3717,c_3722,c_5704,c_13194,c_13860,c_14023,c_26653,c_26794,c_28720])).

cnf(c_7525,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,X0))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0))
    | sK4 = k1_xboole_0
    | m1_orders_2(X0,sK2,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5247,c_7518])).

cnf(c_4139,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_4140,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4139])).

cnf(c_7537,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,X0))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK4,X0))
    | m1_orders_2(X0,sK2,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7525,c_33,c_2177,c_3506,c_3717,c_3722,c_4140,c_5709])).

cnf(c_7543,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5))
    | sK5 = sK4
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_4725,c_7537])).

cnf(c_7626,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = k3_orders_2(sK2,sK4,sK0(sK2,sK4,sK5))
    | sK5 = sK4
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7543,c_2933])).

cnf(c_28748,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | sK5 = sK4
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28728,c_7626])).

cnf(c_30135,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28748,c_3126,c_14049,c_27881])).

cnf(c_30141,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4))
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_9691,c_30135])).

cnf(c_32748,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | r1_tarski(k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_30141,c_3452])).

cnf(c_30143,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_6937,c_30135])).

cnf(c_30379,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | r1_tarski(sK5,k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5)))) = iProver_top ),
    inference(superposition,[status(thm)],[c_30143,c_2936])).

cnf(c_30378,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | r1_tarski(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_30143,c_3452])).

cnf(c_2939,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r2_xboole_0(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_33256,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4
    | sK5 = sK4
    | r2_xboole_0(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_30378,c_2939])).

cnf(c_34896,plain,
    ( k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_30379,c_3126,c_6937,c_7053,c_14049,c_27881,c_33256])).

cnf(c_37769,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | r1_tarski(sK4,sK5) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_32748,c_34896])).

cnf(c_28749,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | sK5 = sK4
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28728,c_7543])).

cnf(c_37385,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5
    | m1_orders_2(sK4,sK2,sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_28749,c_48,c_3126,c_14049,c_27881,c_28748])).

cnf(c_37771,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37769,c_45,c_32,c_47,c_3037,c_3126,c_3347,c_3506,c_3717,c_3722,c_5704,c_13194,c_13860,c_14023,c_30135,c_37385])).

cnf(c_4503,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_xboole_0(k3_xboole_0(X0,X1),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3452,c_2939])).

cnf(c_4626,plain,
    ( k3_xboole_0(X0,X1) = X1
    | r2_xboole_0(X1,k3_xboole_0(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4503,c_2940])).

cnf(c_37815,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK4,sK5))),sK4) = sK4
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_37771,c_4626])).

cnf(c_37944,plain,
    ( sK5 = sK4
    | r2_xboole_0(sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_37815,c_37771])).

cnf(c_39499,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = k3_orders_2(sK2,sK5,sK0(sK2,sK5,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9839,c_32,c_47,c_2177,c_3126,c_3375,c_3506,c_3717,c_3722,c_5704,c_9684,c_14049,c_27881,c_37944])).

cnf(c_39501,plain,
    ( k3_xboole_0(k2_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK0(sK2,sK5,sK4))),sK5) = sK4 ),
    inference(light_normalisation,[status(thm)],[c_39499,c_34896])).

cnf(c_39554,plain,
    ( r1_tarski(sK4,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_39501,c_3452])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_39554,c_37944,c_27881,c_14049,c_14023,c_13860,c_13194,c_5704,c_3722,c_3717,c_3506,c_3347,c_3126,c_3037,c_48,c_47,c_32,c_45])).


%------------------------------------------------------------------------------
