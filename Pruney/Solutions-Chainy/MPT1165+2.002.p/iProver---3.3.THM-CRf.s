%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:38 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 945 expanded)
%              Number of clauses        :   89 ( 235 expanded)
%              Number of leaves         :   12 ( 262 expanded)
%              Depth                    :   20
%              Number of atoms          :  759 (8258 expanded)
%              Number of equality atoms :  183 (1812 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,conjecture,(
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

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f27,plain,(
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

fof(f26,plain,
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

fof(f28,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f27,f26])).

fof(f50,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
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

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f20,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f21,plain,(
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
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f32,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
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

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f45,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f42,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f44,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f35,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
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
    inference(equality_resolution,[],[f35])).

fof(f52,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

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

fof(f24,plain,(
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f38,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f31,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f30,plain,(
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
    inference(cnf_transformation,[],[f23])).

cnf(c_12,negated_conjecture,
    ( m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1204,negated_conjecture,
    ( m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1592,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1202,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1594,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1202])).

cnf(c_4,plain,
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
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_131,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7])).

cnf(c_17,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_454,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_131,c_17])).

cnf(c_455,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_20,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_18,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_459,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_455,c_21,c_20,c_19,c_18])).

cnf(c_1198,plain,
    ( ~ m1_orders_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,X1_44,sK0(sK1,X1_44,X0_44)) = X0_44
    | k1_xboole_0 = X1_44 ),
    inference(subtyping,[status(esa)],[c_459])).

cnf(c_1600,plain,
    ( k3_orders_2(sK1,X0_44,sK0(sK1,X0_44,X1_44)) = X1_44
    | k1_xboole_0 = X0_44
    | m1_orders_2(X1_44,sK1,X0_44) != iProver_top
    | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1198])).

cnf(c_2380,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
    | sK2 = k1_xboole_0
    | m1_orders_2(X0_44,sK1,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1600])).

cnf(c_15,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_30,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_416,plain,
    ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_17])).

cnf(c_417,plain,
    ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_21,c_20,c_19,c_18])).

cnf(c_1210,plain,
    ( X0_44 = X0_44 ),
    theory(equality)).

cnf(c_1221,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1225,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_1203,negated_conjecture,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | k1_xboole_0 != sK2 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1226,plain,
    ( k1_xboole_0 != sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(c_1211,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1777,plain,
    ( sK2 != X0_44
    | k1_xboole_0 != X0_44
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1778,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1777])).

cnf(c_1212,plain,
    ( ~ m1_subset_1(X0_44,X0_46)
    | m1_subset_1(X1_44,X0_46)
    | X1_44 != X0_44 ),
    theory(equality)).

cnf(c_1779,plain,
    ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | X0_44 != sK2 ),
    inference(instantiation,[status(thm)],[c_1212])).

cnf(c_1781,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1779])).

cnf(c_1821,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1210])).

cnf(c_1803,plain,
    ( X0_44 != X1_44
    | sK2 != X1_44
    | sK2 = X0_44 ),
    inference(instantiation,[status(thm)],[c_1211])).

cnf(c_1879,plain,
    ( X0_44 != sK2
    | sK2 = X0_44
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1803])).

cnf(c_1880,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1879])).

cnf(c_1214,plain,
    ( ~ m1_orders_2(X0_44,X0_45,X1_44)
    | m1_orders_2(X2_44,X0_45,X3_44)
    | X2_44 != X0_44
    | X3_44 != X1_44 ),
    theory(equality)).

cnf(c_1883,plain,
    ( ~ m1_orders_2(X0_44,sK1,X1_44)
    | m1_orders_2(sK2,sK1,sK2)
    | sK2 != X0_44
    | sK2 != X1_44 ),
    inference(instantiation,[status(thm)],[c_1214])).

cnf(c_1885,plain,
    ( m1_orders_2(sK2,sK1,sK2)
    | ~ m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1883])).

cnf(c_2497,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
    | m1_orders_2(X0_44,sK1,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2380,c_16,c_15,c_30,c_419,c_1221,c_1225,c_1226,c_1778,c_1781,c_1821,c_1880,c_1885])).

cnf(c_2505,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1592,c_2497])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1759,plain,
    ( ~ m1_orders_2(X0_44,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_1825,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1759])).

cnf(c_1826,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
    | k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1825])).

cnf(c_2506,plain,
    ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2505,c_16,c_27,c_15,c_30,c_419,c_1225,c_1226,c_1781,c_1821,c_1826,c_1880,c_1885])).

cnf(c_8,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_11,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_340,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X3))
    | ~ m1_subset_1(X4,u1_struct_0(X5))
    | ~ m1_subset_1(X6,u1_struct_0(X5))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X5)
    | ~ l1_orders_2(X1)
    | X1 != X5
    | X0 != X6
    | X3 != X6 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_11])).

cnf(c_341,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_430,plain,
    ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
    | ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_341,c_17])).

cnf(c_431,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_435,plain,
    ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_431,c_21,c_20,c_19,c_18])).

cnf(c_1199,plain,
    ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
    | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1207,plain,
    ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_1199])).

cnf(c_1598,plain,
    ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_1208,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_1199])).

cnf(c_1206,plain,
    ( ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_1199])).

cnf(c_1272,plain,
    ( ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_1208,c_1206])).

cnf(c_1273,plain,
    ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
    | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_1272])).

cnf(c_1274,plain,
    ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1273])).

cnf(c_1863,plain,
    ( m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1598,c_1274])).

cnf(c_1864,plain,
    ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
    | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1863])).

cnf(c_2511,plain,
    ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2506,c_1864])).

cnf(c_5,plain,
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
    inference(cnf_transformation,[],[f31])).

cnf(c_126,plain,
    ( r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5,c_7])).

cnf(c_127,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_126])).

cnf(c_478,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | r2_hidden(sK0(X1,X2,X0),X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_127,c_17])).

cnf(c_479,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_483,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | r2_hidden(sK0(sK1,X1,X0),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_21,c_20,c_19,c_18])).

cnf(c_1197,plain,
    ( ~ m1_orders_2(X0_44,sK1,X1_44)
    | r2_hidden(sK0(sK1,X1_44,X0_44),X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = X1_44 ),
    inference(subtyping,[status(esa)],[c_483])).

cnf(c_1754,plain,
    ( ~ m1_orders_2(X0_44,sK1,sK2)
    | r2_hidden(sK0(sK1,sK2,X0_44),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1197])).

cnf(c_1799,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | r2_hidden(sK0(sK1,sK2,sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1754])).

cnf(c_1800,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1799])).

cnf(c_6,plain,
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
    inference(cnf_transformation,[],[f30])).

cnf(c_121,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6,c_7])).

cnf(c_502,plain,
    ( ~ m1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_121,c_17])).

cnf(c_503,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_507,plain,
    ( ~ m1_orders_2(X0,sK1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_21,c_20,c_19,c_18])).

cnf(c_1196,plain,
    ( ~ m1_orders_2(X0_44,sK1,X1_44)
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(sK0(sK1,X1_44,X0_44),u1_struct_0(sK1))
    | k1_xboole_0 = X1_44 ),
    inference(subtyping,[status(esa)],[c_507])).

cnf(c_1749,plain,
    ( ~ m1_orders_2(X0_44,sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,X0_44),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1196])).

cnf(c_1796,plain,
    ( ~ m1_orders_2(sK2,sK1,sK2)
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_1797,plain,
    ( k1_xboole_0 = sK2
    | m1_orders_2(sK2,sK1,sK2) != iProver_top
    | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1796])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2511,c_1885,c_1880,c_1821,c_1800,c_1797,c_1781,c_1226,c_1225,c_419,c_30,c_15,c_27,c_16])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:08:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.46/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.46/1.03  
% 1.46/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.46/1.03  
% 1.46/1.03  ------  iProver source info
% 1.46/1.03  
% 1.46/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.46/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.46/1.03  git: non_committed_changes: false
% 1.46/1.03  git: last_make_outside_of_git: false
% 1.46/1.03  
% 1.46/1.03  ------ 
% 1.46/1.03  
% 1.46/1.03  ------ Input Options
% 1.46/1.03  
% 1.46/1.03  --out_options                           all
% 1.46/1.03  --tptp_safe_out                         true
% 1.46/1.03  --problem_path                          ""
% 1.46/1.03  --include_path                          ""
% 1.46/1.03  --clausifier                            res/vclausify_rel
% 1.46/1.03  --clausifier_options                    --mode clausify
% 1.46/1.03  --stdin                                 false
% 1.46/1.03  --stats_out                             all
% 1.46/1.03  
% 1.46/1.03  ------ General Options
% 1.46/1.03  
% 1.46/1.03  --fof                                   false
% 1.46/1.03  --time_out_real                         305.
% 1.46/1.03  --time_out_virtual                      -1.
% 1.46/1.03  --symbol_type_check                     false
% 1.46/1.03  --clausify_out                          false
% 1.46/1.03  --sig_cnt_out                           false
% 1.46/1.03  --trig_cnt_out                          false
% 1.46/1.03  --trig_cnt_out_tolerance                1.
% 1.46/1.03  --trig_cnt_out_sk_spl                   false
% 1.46/1.03  --abstr_cl_out                          false
% 1.46/1.03  
% 1.46/1.03  ------ Global Options
% 1.46/1.03  
% 1.46/1.03  --schedule                              default
% 1.46/1.03  --add_important_lit                     false
% 1.46/1.03  --prop_solver_per_cl                    1000
% 1.46/1.03  --min_unsat_core                        false
% 1.46/1.03  --soft_assumptions                      false
% 1.46/1.03  --soft_lemma_size                       3
% 1.46/1.03  --prop_impl_unit_size                   0
% 1.46/1.03  --prop_impl_unit                        []
% 1.46/1.03  --share_sel_clauses                     true
% 1.46/1.03  --reset_solvers                         false
% 1.46/1.03  --bc_imp_inh                            [conj_cone]
% 1.46/1.03  --conj_cone_tolerance                   3.
% 1.46/1.03  --extra_neg_conj                        none
% 1.46/1.03  --large_theory_mode                     true
% 1.46/1.03  --prolific_symb_bound                   200
% 1.46/1.03  --lt_threshold                          2000
% 1.46/1.03  --clause_weak_htbl                      true
% 1.46/1.03  --gc_record_bc_elim                     false
% 1.46/1.03  
% 1.46/1.03  ------ Preprocessing Options
% 1.46/1.03  
% 1.46/1.03  --preprocessing_flag                    true
% 1.46/1.03  --time_out_prep_mult                    0.1
% 1.46/1.03  --splitting_mode                        input
% 1.46/1.03  --splitting_grd                         true
% 1.46/1.03  --splitting_cvd                         false
% 1.46/1.03  --splitting_cvd_svl                     false
% 1.46/1.03  --splitting_nvd                         32
% 1.46/1.03  --sub_typing                            true
% 1.46/1.03  --prep_gs_sim                           true
% 1.46/1.03  --prep_unflatten                        true
% 1.46/1.03  --prep_res_sim                          true
% 1.46/1.03  --prep_upred                            true
% 1.46/1.03  --prep_sem_filter                       exhaustive
% 1.46/1.03  --prep_sem_filter_out                   false
% 1.46/1.03  --pred_elim                             true
% 1.46/1.03  --res_sim_input                         true
% 1.46/1.03  --eq_ax_congr_red                       true
% 1.46/1.03  --pure_diseq_elim                       true
% 1.46/1.03  --brand_transform                       false
% 1.46/1.03  --non_eq_to_eq                          false
% 1.46/1.03  --prep_def_merge                        true
% 1.46/1.03  --prep_def_merge_prop_impl              false
% 1.57/1.03  --prep_def_merge_mbd                    true
% 1.57/1.03  --prep_def_merge_tr_red                 false
% 1.57/1.03  --prep_def_merge_tr_cl                  false
% 1.57/1.03  --smt_preprocessing                     true
% 1.57/1.03  --smt_ac_axioms                         fast
% 1.57/1.03  --preprocessed_out                      false
% 1.57/1.03  --preprocessed_stats                    false
% 1.57/1.03  
% 1.57/1.03  ------ Abstraction refinement Options
% 1.57/1.03  
% 1.57/1.03  --abstr_ref                             []
% 1.57/1.03  --abstr_ref_prep                        false
% 1.57/1.03  --abstr_ref_until_sat                   false
% 1.57/1.03  --abstr_ref_sig_restrict                funpre
% 1.57/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.57/1.03  --abstr_ref_under                       []
% 1.57/1.03  
% 1.57/1.03  ------ SAT Options
% 1.57/1.03  
% 1.57/1.03  --sat_mode                              false
% 1.57/1.03  --sat_fm_restart_options                ""
% 1.57/1.03  --sat_gr_def                            false
% 1.57/1.03  --sat_epr_types                         true
% 1.57/1.03  --sat_non_cyclic_types                  false
% 1.57/1.03  --sat_finite_models                     false
% 1.57/1.03  --sat_fm_lemmas                         false
% 1.57/1.03  --sat_fm_prep                           false
% 1.57/1.03  --sat_fm_uc_incr                        true
% 1.57/1.03  --sat_out_model                         small
% 1.57/1.03  --sat_out_clauses                       false
% 1.57/1.03  
% 1.57/1.03  ------ QBF Options
% 1.57/1.03  
% 1.57/1.03  --qbf_mode                              false
% 1.57/1.03  --qbf_elim_univ                         false
% 1.57/1.03  --qbf_dom_inst                          none
% 1.57/1.03  --qbf_dom_pre_inst                      false
% 1.57/1.03  --qbf_sk_in                             false
% 1.57/1.03  --qbf_pred_elim                         true
% 1.57/1.03  --qbf_split                             512
% 1.57/1.03  
% 1.57/1.03  ------ BMC1 Options
% 1.57/1.03  
% 1.57/1.03  --bmc1_incremental                      false
% 1.57/1.03  --bmc1_axioms                           reachable_all
% 1.57/1.03  --bmc1_min_bound                        0
% 1.57/1.03  --bmc1_max_bound                        -1
% 1.57/1.03  --bmc1_max_bound_default                -1
% 1.57/1.03  --bmc1_symbol_reachability              true
% 1.57/1.03  --bmc1_property_lemmas                  false
% 1.57/1.03  --bmc1_k_induction                      false
% 1.57/1.03  --bmc1_non_equiv_states                 false
% 1.57/1.03  --bmc1_deadlock                         false
% 1.57/1.03  --bmc1_ucm                              false
% 1.57/1.03  --bmc1_add_unsat_core                   none
% 1.57/1.03  --bmc1_unsat_core_children              false
% 1.57/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.57/1.03  --bmc1_out_stat                         full
% 1.57/1.03  --bmc1_ground_init                      false
% 1.57/1.03  --bmc1_pre_inst_next_state              false
% 1.57/1.03  --bmc1_pre_inst_state                   false
% 1.57/1.03  --bmc1_pre_inst_reach_state             false
% 1.57/1.03  --bmc1_out_unsat_core                   false
% 1.57/1.03  --bmc1_aig_witness_out                  false
% 1.57/1.03  --bmc1_verbose                          false
% 1.57/1.03  --bmc1_dump_clauses_tptp                false
% 1.57/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.57/1.03  --bmc1_dump_file                        -
% 1.57/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.57/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.57/1.03  --bmc1_ucm_extend_mode                  1
% 1.57/1.03  --bmc1_ucm_init_mode                    2
% 1.57/1.03  --bmc1_ucm_cone_mode                    none
% 1.57/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.57/1.03  --bmc1_ucm_relax_model                  4
% 1.57/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.57/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.57/1.03  --bmc1_ucm_layered_model                none
% 1.57/1.03  --bmc1_ucm_max_lemma_size               10
% 1.57/1.03  
% 1.57/1.03  ------ AIG Options
% 1.57/1.03  
% 1.57/1.03  --aig_mode                              false
% 1.57/1.03  
% 1.57/1.03  ------ Instantiation Options
% 1.57/1.03  
% 1.57/1.03  --instantiation_flag                    true
% 1.57/1.03  --inst_sos_flag                         false
% 1.57/1.03  --inst_sos_phase                        true
% 1.57/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.57/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.57/1.03  --inst_lit_sel_side                     num_symb
% 1.57/1.03  --inst_solver_per_active                1400
% 1.57/1.03  --inst_solver_calls_frac                1.
% 1.57/1.03  --inst_passive_queue_type               priority_queues
% 1.57/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.57/1.03  --inst_passive_queues_freq              [25;2]
% 1.57/1.03  --inst_dismatching                      true
% 1.57/1.03  --inst_eager_unprocessed_to_passive     true
% 1.57/1.03  --inst_prop_sim_given                   true
% 1.57/1.03  --inst_prop_sim_new                     false
% 1.57/1.03  --inst_subs_new                         false
% 1.57/1.03  --inst_eq_res_simp                      false
% 1.57/1.03  --inst_subs_given                       false
% 1.57/1.03  --inst_orphan_elimination               true
% 1.57/1.03  --inst_learning_loop_flag               true
% 1.57/1.03  --inst_learning_start                   3000
% 1.57/1.03  --inst_learning_factor                  2
% 1.57/1.03  --inst_start_prop_sim_after_learn       3
% 1.57/1.03  --inst_sel_renew                        solver
% 1.57/1.03  --inst_lit_activity_flag                true
% 1.57/1.03  --inst_restr_to_given                   false
% 1.57/1.03  --inst_activity_threshold               500
% 1.57/1.03  --inst_out_proof                        true
% 1.57/1.03  
% 1.57/1.03  ------ Resolution Options
% 1.57/1.03  
% 1.57/1.03  --resolution_flag                       true
% 1.57/1.03  --res_lit_sel                           adaptive
% 1.57/1.03  --res_lit_sel_side                      none
% 1.57/1.03  --res_ordering                          kbo
% 1.57/1.03  --res_to_prop_solver                    active
% 1.57/1.03  --res_prop_simpl_new                    false
% 1.57/1.03  --res_prop_simpl_given                  true
% 1.57/1.03  --res_passive_queue_type                priority_queues
% 1.57/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.57/1.03  --res_passive_queues_freq               [15;5]
% 1.57/1.03  --res_forward_subs                      full
% 1.57/1.03  --res_backward_subs                     full
% 1.57/1.03  --res_forward_subs_resolution           true
% 1.57/1.03  --res_backward_subs_resolution          true
% 1.57/1.03  --res_orphan_elimination                true
% 1.57/1.03  --res_time_limit                        2.
% 1.57/1.03  --res_out_proof                         true
% 1.57/1.03  
% 1.57/1.03  ------ Superposition Options
% 1.57/1.03  
% 1.57/1.03  --superposition_flag                    true
% 1.57/1.03  --sup_passive_queue_type                priority_queues
% 1.57/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.57/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.57/1.03  --demod_completeness_check              fast
% 1.57/1.03  --demod_use_ground                      true
% 1.57/1.03  --sup_to_prop_solver                    passive
% 1.57/1.03  --sup_prop_simpl_new                    true
% 1.57/1.03  --sup_prop_simpl_given                  true
% 1.57/1.03  --sup_fun_splitting                     false
% 1.57/1.03  --sup_smt_interval                      50000
% 1.57/1.03  
% 1.57/1.03  ------ Superposition Simplification Setup
% 1.57/1.03  
% 1.57/1.03  --sup_indices_passive                   []
% 1.57/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.57/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_full_bw                           [BwDemod]
% 1.57/1.03  --sup_immed_triv                        [TrivRules]
% 1.57/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.57/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_immed_bw_main                     []
% 1.57/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.57/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/1.03  
% 1.57/1.03  ------ Combination Options
% 1.57/1.03  
% 1.57/1.03  --comb_res_mult                         3
% 1.57/1.03  --comb_sup_mult                         2
% 1.57/1.03  --comb_inst_mult                        10
% 1.57/1.03  
% 1.57/1.03  ------ Debug Options
% 1.57/1.03  
% 1.57/1.03  --dbg_backtrace                         false
% 1.57/1.03  --dbg_dump_prop_clauses                 false
% 1.57/1.03  --dbg_dump_prop_clauses_file            -
% 1.57/1.03  --dbg_out_stat                          false
% 1.57/1.03  ------ Parsing...
% 1.57/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.57/1.03  
% 1.57/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.57/1.03  
% 1.57/1.03  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.57/1.03  
% 1.57/1.03  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.57/1.03  ------ Proving...
% 1.57/1.03  ------ Problem Properties 
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  clauses                                 16
% 1.57/1.03  conjectures                             3
% 1.57/1.03  EPR                                     3
% 1.57/1.03  Horn                                    10
% 1.57/1.03  unary                                   1
% 1.57/1.03  binary                                  5
% 1.57/1.03  lits                                    52
% 1.57/1.03  lits eq                                 8
% 1.57/1.03  fd_pure                                 0
% 1.57/1.03  fd_pseudo                               0
% 1.57/1.03  fd_cond                                 4
% 1.57/1.03  fd_pseudo_cond                          0
% 1.57/1.03  AC symbols                              0
% 1.57/1.03  
% 1.57/1.03  ------ Schedule dynamic 5 is on 
% 1.57/1.03  
% 1.57/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  ------ 
% 1.57/1.03  Current options:
% 1.57/1.03  ------ 
% 1.57/1.03  
% 1.57/1.03  ------ Input Options
% 1.57/1.03  
% 1.57/1.03  --out_options                           all
% 1.57/1.03  --tptp_safe_out                         true
% 1.57/1.03  --problem_path                          ""
% 1.57/1.03  --include_path                          ""
% 1.57/1.03  --clausifier                            res/vclausify_rel
% 1.57/1.03  --clausifier_options                    --mode clausify
% 1.57/1.03  --stdin                                 false
% 1.57/1.03  --stats_out                             all
% 1.57/1.03  
% 1.57/1.03  ------ General Options
% 1.57/1.03  
% 1.57/1.03  --fof                                   false
% 1.57/1.03  --time_out_real                         305.
% 1.57/1.03  --time_out_virtual                      -1.
% 1.57/1.03  --symbol_type_check                     false
% 1.57/1.03  --clausify_out                          false
% 1.57/1.03  --sig_cnt_out                           false
% 1.57/1.03  --trig_cnt_out                          false
% 1.57/1.03  --trig_cnt_out_tolerance                1.
% 1.57/1.03  --trig_cnt_out_sk_spl                   false
% 1.57/1.03  --abstr_cl_out                          false
% 1.57/1.03  
% 1.57/1.03  ------ Global Options
% 1.57/1.03  
% 1.57/1.03  --schedule                              default
% 1.57/1.03  --add_important_lit                     false
% 1.57/1.03  --prop_solver_per_cl                    1000
% 1.57/1.03  --min_unsat_core                        false
% 1.57/1.03  --soft_assumptions                      false
% 1.57/1.03  --soft_lemma_size                       3
% 1.57/1.03  --prop_impl_unit_size                   0
% 1.57/1.03  --prop_impl_unit                        []
% 1.57/1.03  --share_sel_clauses                     true
% 1.57/1.03  --reset_solvers                         false
% 1.57/1.03  --bc_imp_inh                            [conj_cone]
% 1.57/1.03  --conj_cone_tolerance                   3.
% 1.57/1.03  --extra_neg_conj                        none
% 1.57/1.03  --large_theory_mode                     true
% 1.57/1.03  --prolific_symb_bound                   200
% 1.57/1.03  --lt_threshold                          2000
% 1.57/1.03  --clause_weak_htbl                      true
% 1.57/1.03  --gc_record_bc_elim                     false
% 1.57/1.03  
% 1.57/1.03  ------ Preprocessing Options
% 1.57/1.03  
% 1.57/1.03  --preprocessing_flag                    true
% 1.57/1.03  --time_out_prep_mult                    0.1
% 1.57/1.03  --splitting_mode                        input
% 1.57/1.03  --splitting_grd                         true
% 1.57/1.03  --splitting_cvd                         false
% 1.57/1.03  --splitting_cvd_svl                     false
% 1.57/1.03  --splitting_nvd                         32
% 1.57/1.03  --sub_typing                            true
% 1.57/1.03  --prep_gs_sim                           true
% 1.57/1.03  --prep_unflatten                        true
% 1.57/1.03  --prep_res_sim                          true
% 1.57/1.03  --prep_upred                            true
% 1.57/1.03  --prep_sem_filter                       exhaustive
% 1.57/1.03  --prep_sem_filter_out                   false
% 1.57/1.03  --pred_elim                             true
% 1.57/1.03  --res_sim_input                         true
% 1.57/1.03  --eq_ax_congr_red                       true
% 1.57/1.03  --pure_diseq_elim                       true
% 1.57/1.03  --brand_transform                       false
% 1.57/1.03  --non_eq_to_eq                          false
% 1.57/1.03  --prep_def_merge                        true
% 1.57/1.03  --prep_def_merge_prop_impl              false
% 1.57/1.03  --prep_def_merge_mbd                    true
% 1.57/1.03  --prep_def_merge_tr_red                 false
% 1.57/1.03  --prep_def_merge_tr_cl                  false
% 1.57/1.03  --smt_preprocessing                     true
% 1.57/1.03  --smt_ac_axioms                         fast
% 1.57/1.03  --preprocessed_out                      false
% 1.57/1.03  --preprocessed_stats                    false
% 1.57/1.03  
% 1.57/1.03  ------ Abstraction refinement Options
% 1.57/1.03  
% 1.57/1.03  --abstr_ref                             []
% 1.57/1.03  --abstr_ref_prep                        false
% 1.57/1.03  --abstr_ref_until_sat                   false
% 1.57/1.03  --abstr_ref_sig_restrict                funpre
% 1.57/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.57/1.03  --abstr_ref_under                       []
% 1.57/1.03  
% 1.57/1.03  ------ SAT Options
% 1.57/1.03  
% 1.57/1.03  --sat_mode                              false
% 1.57/1.03  --sat_fm_restart_options                ""
% 1.57/1.03  --sat_gr_def                            false
% 1.57/1.03  --sat_epr_types                         true
% 1.57/1.03  --sat_non_cyclic_types                  false
% 1.57/1.03  --sat_finite_models                     false
% 1.57/1.03  --sat_fm_lemmas                         false
% 1.57/1.03  --sat_fm_prep                           false
% 1.57/1.03  --sat_fm_uc_incr                        true
% 1.57/1.03  --sat_out_model                         small
% 1.57/1.03  --sat_out_clauses                       false
% 1.57/1.03  
% 1.57/1.03  ------ QBF Options
% 1.57/1.03  
% 1.57/1.03  --qbf_mode                              false
% 1.57/1.03  --qbf_elim_univ                         false
% 1.57/1.03  --qbf_dom_inst                          none
% 1.57/1.03  --qbf_dom_pre_inst                      false
% 1.57/1.03  --qbf_sk_in                             false
% 1.57/1.03  --qbf_pred_elim                         true
% 1.57/1.03  --qbf_split                             512
% 1.57/1.03  
% 1.57/1.03  ------ BMC1 Options
% 1.57/1.03  
% 1.57/1.03  --bmc1_incremental                      false
% 1.57/1.03  --bmc1_axioms                           reachable_all
% 1.57/1.03  --bmc1_min_bound                        0
% 1.57/1.03  --bmc1_max_bound                        -1
% 1.57/1.03  --bmc1_max_bound_default                -1
% 1.57/1.03  --bmc1_symbol_reachability              true
% 1.57/1.03  --bmc1_property_lemmas                  false
% 1.57/1.03  --bmc1_k_induction                      false
% 1.57/1.03  --bmc1_non_equiv_states                 false
% 1.57/1.03  --bmc1_deadlock                         false
% 1.57/1.03  --bmc1_ucm                              false
% 1.57/1.03  --bmc1_add_unsat_core                   none
% 1.57/1.03  --bmc1_unsat_core_children              false
% 1.57/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.57/1.03  --bmc1_out_stat                         full
% 1.57/1.03  --bmc1_ground_init                      false
% 1.57/1.03  --bmc1_pre_inst_next_state              false
% 1.57/1.03  --bmc1_pre_inst_state                   false
% 1.57/1.03  --bmc1_pre_inst_reach_state             false
% 1.57/1.03  --bmc1_out_unsat_core                   false
% 1.57/1.03  --bmc1_aig_witness_out                  false
% 1.57/1.03  --bmc1_verbose                          false
% 1.57/1.03  --bmc1_dump_clauses_tptp                false
% 1.57/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.57/1.03  --bmc1_dump_file                        -
% 1.57/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.57/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.57/1.03  --bmc1_ucm_extend_mode                  1
% 1.57/1.03  --bmc1_ucm_init_mode                    2
% 1.57/1.03  --bmc1_ucm_cone_mode                    none
% 1.57/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.57/1.03  --bmc1_ucm_relax_model                  4
% 1.57/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.57/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.57/1.03  --bmc1_ucm_layered_model                none
% 1.57/1.03  --bmc1_ucm_max_lemma_size               10
% 1.57/1.03  
% 1.57/1.03  ------ AIG Options
% 1.57/1.03  
% 1.57/1.03  --aig_mode                              false
% 1.57/1.03  
% 1.57/1.03  ------ Instantiation Options
% 1.57/1.03  
% 1.57/1.03  --instantiation_flag                    true
% 1.57/1.03  --inst_sos_flag                         false
% 1.57/1.03  --inst_sos_phase                        true
% 1.57/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.57/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.57/1.03  --inst_lit_sel_side                     none
% 1.57/1.03  --inst_solver_per_active                1400
% 1.57/1.03  --inst_solver_calls_frac                1.
% 1.57/1.03  --inst_passive_queue_type               priority_queues
% 1.57/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.57/1.03  --inst_passive_queues_freq              [25;2]
% 1.57/1.03  --inst_dismatching                      true
% 1.57/1.03  --inst_eager_unprocessed_to_passive     true
% 1.57/1.03  --inst_prop_sim_given                   true
% 1.57/1.03  --inst_prop_sim_new                     false
% 1.57/1.03  --inst_subs_new                         false
% 1.57/1.03  --inst_eq_res_simp                      false
% 1.57/1.03  --inst_subs_given                       false
% 1.57/1.03  --inst_orphan_elimination               true
% 1.57/1.03  --inst_learning_loop_flag               true
% 1.57/1.03  --inst_learning_start                   3000
% 1.57/1.03  --inst_learning_factor                  2
% 1.57/1.03  --inst_start_prop_sim_after_learn       3
% 1.57/1.03  --inst_sel_renew                        solver
% 1.57/1.03  --inst_lit_activity_flag                true
% 1.57/1.03  --inst_restr_to_given                   false
% 1.57/1.03  --inst_activity_threshold               500
% 1.57/1.03  --inst_out_proof                        true
% 1.57/1.03  
% 1.57/1.03  ------ Resolution Options
% 1.57/1.03  
% 1.57/1.03  --resolution_flag                       false
% 1.57/1.03  --res_lit_sel                           adaptive
% 1.57/1.03  --res_lit_sel_side                      none
% 1.57/1.03  --res_ordering                          kbo
% 1.57/1.03  --res_to_prop_solver                    active
% 1.57/1.03  --res_prop_simpl_new                    false
% 1.57/1.03  --res_prop_simpl_given                  true
% 1.57/1.03  --res_passive_queue_type                priority_queues
% 1.57/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.57/1.03  --res_passive_queues_freq               [15;5]
% 1.57/1.03  --res_forward_subs                      full
% 1.57/1.03  --res_backward_subs                     full
% 1.57/1.03  --res_forward_subs_resolution           true
% 1.57/1.03  --res_backward_subs_resolution          true
% 1.57/1.03  --res_orphan_elimination                true
% 1.57/1.03  --res_time_limit                        2.
% 1.57/1.03  --res_out_proof                         true
% 1.57/1.03  
% 1.57/1.03  ------ Superposition Options
% 1.57/1.03  
% 1.57/1.03  --superposition_flag                    true
% 1.57/1.03  --sup_passive_queue_type                priority_queues
% 1.57/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.57/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.57/1.03  --demod_completeness_check              fast
% 1.57/1.03  --demod_use_ground                      true
% 1.57/1.03  --sup_to_prop_solver                    passive
% 1.57/1.03  --sup_prop_simpl_new                    true
% 1.57/1.03  --sup_prop_simpl_given                  true
% 1.57/1.03  --sup_fun_splitting                     false
% 1.57/1.03  --sup_smt_interval                      50000
% 1.57/1.03  
% 1.57/1.03  ------ Superposition Simplification Setup
% 1.57/1.03  
% 1.57/1.03  --sup_indices_passive                   []
% 1.57/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.57/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.57/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_full_bw                           [BwDemod]
% 1.57/1.03  --sup_immed_triv                        [TrivRules]
% 1.57/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.57/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_immed_bw_main                     []
% 1.57/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.57/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.57/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.57/1.03  
% 1.57/1.03  ------ Combination Options
% 1.57/1.03  
% 1.57/1.03  --comb_res_mult                         3
% 1.57/1.03  --comb_sup_mult                         2
% 1.57/1.03  --comb_inst_mult                        10
% 1.57/1.03  
% 1.57/1.03  ------ Debug Options
% 1.57/1.03  
% 1.57/1.03  --dbg_backtrace                         false
% 1.57/1.03  --dbg_dump_prop_clauses                 false
% 1.57/1.03  --dbg_dump_prop_clauses_file            -
% 1.57/1.03  --dbg_out_stat                          false
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  ------ Proving...
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  % SZS status Theorem for theBenchmark.p
% 1.57/1.03  
% 1.57/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.57/1.03  
% 1.57/1.03  fof(f6,conjecture,(
% 1.57/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.57/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/1.03  
% 1.57/1.03  fof(f7,negated_conjecture,(
% 1.57/1.03    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.57/1.03    inference(negated_conjecture,[],[f6])).
% 1.57/1.03  
% 1.57/1.03  fof(f18,plain,(
% 1.57/1.03    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.57/1.03    inference(ennf_transformation,[],[f7])).
% 1.57/1.03  
% 1.57/1.03  fof(f19,plain,(
% 1.57/1.03    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.57/1.03    inference(flattening,[],[f18])).
% 1.57/1.03  
% 1.57/1.03  fof(f27,plain,(
% 1.57/1.03    ( ! [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (((k1_xboole_0 = sK2 & ~m1_orders_2(sK2,X0,sK2)) | (m1_orders_2(sK2,X0,sK2) & k1_xboole_0 != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.57/1.03    introduced(choice_axiom,[])).
% 1.57/1.03  
% 1.57/1.03  fof(f26,plain,(
% 1.57/1.03    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK1,X1)) | (m1_orders_2(X1,sK1,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.57/1.03    introduced(choice_axiom,[])).
% 1.57/1.03  
% 1.57/1.03  fof(f28,plain,(
% 1.57/1.03    (((k1_xboole_0 = sK2 & ~m1_orders_2(sK2,sK1,sK2)) | (m1_orders_2(sK2,sK1,sK2) & k1_xboole_0 != sK2)) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.57/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f19,f27,f26])).
% 1.57/1.03  
% 1.57/1.03  fof(f50,plain,(
% 1.57/1.03    k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f46,plain,(
% 1.57/1.03    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f2,axiom,(
% 1.57/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 1.57/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/1.03  
% 1.57/1.03  fof(f10,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.57/1.03    inference(ennf_transformation,[],[f2])).
% 1.57/1.03  
% 1.57/1.03  fof(f11,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(flattening,[],[f10])).
% 1.57/1.03  
% 1.57/1.03  fof(f20,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(nnf_transformation,[],[f11])).
% 1.57/1.03  
% 1.57/1.03  fof(f21,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(rectify,[],[f20])).
% 1.57/1.03  
% 1.57/1.03  fof(f22,plain,(
% 1.57/1.03    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))))),
% 1.57/1.03    introduced(choice_axiom,[])).
% 1.57/1.03  
% 1.57/1.03  fof(f23,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 1.57/1.03  
% 1.57/1.03  fof(f32,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK0(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f23])).
% 1.57/1.03  
% 1.57/1.03  fof(f3,axiom,(
% 1.57/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.57/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/1.03  
% 1.57/1.03  fof(f12,plain,(
% 1.57/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.57/1.03    inference(ennf_transformation,[],[f3])).
% 1.57/1.03  
% 1.57/1.03  fof(f13,plain,(
% 1.57/1.03    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(flattening,[],[f12])).
% 1.57/1.03  
% 1.57/1.03  fof(f36,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f13])).
% 1.57/1.03  
% 1.57/1.03  fof(f45,plain,(
% 1.57/1.03    l1_orders_2(sK1)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f41,plain,(
% 1.57/1.03    ~v2_struct_0(sK1)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f42,plain,(
% 1.57/1.03    v3_orders_2(sK1)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f43,plain,(
% 1.57/1.03    v4_orders_2(sK1)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f44,plain,(
% 1.57/1.03    v5_orders_2(sK1)),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f47,plain,(
% 1.57/1.03    ~m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2),
% 1.57/1.03    inference(cnf_transformation,[],[f28])).
% 1.57/1.03  
% 1.57/1.03  fof(f35,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f23])).
% 1.57/1.03  
% 1.57/1.03  fof(f51,plain,(
% 1.57/1.03    ( ! [X0,X1] : (m1_orders_2(k1_xboole_0,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(equality_resolution,[],[f35])).
% 1.57/1.03  
% 1.57/1.03  fof(f52,plain,(
% 1.57/1.03    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(equality_resolution,[],[f51])).
% 1.57/1.03  
% 1.57/1.03  fof(f4,axiom,(
% 1.57/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0)) => ~r2_orders_2(X0,X1,X1))),
% 1.57/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/1.03  
% 1.57/1.03  fof(f14,plain,(
% 1.57/1.03    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)))),
% 1.57/1.03    inference(ennf_transformation,[],[f4])).
% 1.57/1.03  
% 1.57/1.03  fof(f15,plain,(
% 1.57/1.03    ! [X0,X1,X2] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.57/1.03    inference(flattening,[],[f14])).
% 1.57/1.03  
% 1.57/1.03  fof(f37,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (~r2_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f15])).
% 1.57/1.03  
% 1.57/1.03  fof(f5,axiom,(
% 1.57/1.03    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 1.57/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 1.57/1.03  
% 1.57/1.03  fof(f16,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.57/1.03    inference(ennf_transformation,[],[f5])).
% 1.57/1.03  
% 1.57/1.03  fof(f17,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(flattening,[],[f16])).
% 1.57/1.03  
% 1.57/1.03  fof(f24,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(nnf_transformation,[],[f17])).
% 1.57/1.03  
% 1.57/1.03  fof(f25,plain,(
% 1.57/1.03    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.57/1.03    inference(flattening,[],[f24])).
% 1.57/1.03  
% 1.57/1.03  fof(f38,plain,(
% 1.57/1.03    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f25])).
% 1.57/1.03  
% 1.57/1.03  fof(f31,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f23])).
% 1.57/1.03  
% 1.57/1.03  fof(f30,plain,(
% 1.57/1.03    ( ! [X2,X0,X1] : (m1_subset_1(sK0(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.57/1.03    inference(cnf_transformation,[],[f23])).
% 1.57/1.03  
% 1.57/1.03  cnf(c_12,negated_conjecture,
% 1.57/1.03      ( m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(cnf_transformation,[],[f50]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1204,negated_conjecture,
% 1.57/1.03      ( m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1592,plain,
% 1.57/1.03      ( k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_16,negated_conjecture,
% 1.57/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(cnf_transformation,[],[f46]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1202,negated_conjecture,
% 1.57/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1594,plain,
% 1.57/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1202]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_4,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(cnf_transformation,[],[f32]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_7,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f36]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_131,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(global_propositional_subsumption,[status(thm)],[c_4,c_7]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_17,negated_conjecture,
% 1.57/1.03      ( l1_orders_2(sK1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f45]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_454,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | k3_orders_2(X1,X2,sK0(X1,X2,X0)) = X0
% 1.57/1.03      | sK1 != X1
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_131,c_17]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_455,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | v2_struct_0(sK1)
% 1.57/1.03      | ~ v3_orders_2(sK1)
% 1.57/1.03      | ~ v4_orders_2(sK1)
% 1.57/1.03      | ~ v5_orders_2(sK1)
% 1.57/1.03      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_454]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_21,negated_conjecture,
% 1.57/1.03      ( ~ v2_struct_0(sK1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f41]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_20,negated_conjecture,
% 1.57/1.03      ( v3_orders_2(sK1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f42]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_19,negated_conjecture,
% 1.57/1.03      ( v4_orders_2(sK1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f43]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_18,negated_conjecture,
% 1.57/1.03      ( v5_orders_2(sK1) ),
% 1.57/1.03      inference(cnf_transformation,[],[f44]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_459,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k3_orders_2(sK1,X1,sK0(sK1,X1,X0)) = X0
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_455,c_21,c_20,c_19,c_18]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1198,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,X1_44)
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k3_orders_2(sK1,X1_44,sK0(sK1,X1_44,X0_44)) = X0_44
% 1.57/1.03      | k1_xboole_0 = X1_44 ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_459]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1600,plain,
% 1.57/1.03      ( k3_orders_2(sK1,X0_44,sK0(sK1,X0_44,X1_44)) = X1_44
% 1.57/1.03      | k1_xboole_0 = X0_44
% 1.57/1.03      | m1_orders_2(X1_44,sK1,X0_44) != iProver_top
% 1.57/1.03      | m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1198]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_2380,plain,
% 1.57/1.03      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
% 1.57/1.03      | sK2 = k1_xboole_0
% 1.57/1.03      | m1_orders_2(X0_44,sK1,sK2) != iProver_top ),
% 1.57/1.03      inference(superposition,[status(thm)],[c_1594,c_1600]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_15,negated_conjecture,
% 1.57/1.03      ( ~ m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2 ),
% 1.57/1.03      inference(cnf_transformation,[],[f47]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_30,plain,
% 1.57/1.03      ( k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1,plain,
% 1.57/1.03      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
% 1.57/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.57/1.03      | v2_struct_0(X0)
% 1.57/1.03      | ~ v3_orders_2(X0)
% 1.57/1.03      | ~ v4_orders_2(X0)
% 1.57/1.03      | ~ v5_orders_2(X0)
% 1.57/1.03      | ~ l1_orders_2(X0) ),
% 1.57/1.03      inference(cnf_transformation,[],[f52]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_416,plain,
% 1.57/1.03      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
% 1.57/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
% 1.57/1.03      | v2_struct_0(X0)
% 1.57/1.03      | ~ v3_orders_2(X0)
% 1.57/1.03      | ~ v4_orders_2(X0)
% 1.57/1.03      | ~ v5_orders_2(X0)
% 1.57/1.03      | sK1 != X0 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_17]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_417,plain,
% 1.57/1.03      ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.57/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | v2_struct_0(sK1)
% 1.57/1.03      | ~ v3_orders_2(sK1)
% 1.57/1.03      | ~ v4_orders_2(sK1)
% 1.57/1.03      | ~ v5_orders_2(sK1) ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_416]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_419,plain,
% 1.57/1.03      ( m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.57/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_417,c_21,c_20,c_19,c_18]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1210,plain,( X0_44 = X0_44 ),theory(equality) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1221,plain,
% 1.57/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1210]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1225,plain,
% 1.57/1.03      ( k1_xboole_0 = sK2 | m1_orders_2(sK2,sK1,sK2) = iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1203,negated_conjecture,
% 1.57/1.03      ( ~ m1_orders_2(sK2,sK1,sK2) | k1_xboole_0 != sK2 ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_15]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1226,plain,
% 1.57/1.03      ( k1_xboole_0 != sK2 | m1_orders_2(sK2,sK1,sK2) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1203]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1211,plain,
% 1.57/1.03      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 1.57/1.03      theory(equality) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1777,plain,
% 1.57/1.03      ( sK2 != X0_44 | k1_xboole_0 != X0_44 | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1211]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1778,plain,
% 1.57/1.03      ( sK2 != k1_xboole_0
% 1.57/1.03      | k1_xboole_0 = sK2
% 1.57/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1777]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1212,plain,
% 1.57/1.03      ( ~ m1_subset_1(X0_44,X0_46)
% 1.57/1.03      | m1_subset_1(X1_44,X0_46)
% 1.57/1.03      | X1_44 != X0_44 ),
% 1.57/1.03      theory(equality) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1779,plain,
% 1.57/1.03      ( m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | X0_44 != sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1212]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1781,plain,
% 1.57/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 != sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1779]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1821,plain,
% 1.57/1.03      ( sK2 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1210]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1803,plain,
% 1.57/1.03      ( X0_44 != X1_44 | sK2 != X1_44 | sK2 = X0_44 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1211]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1879,plain,
% 1.57/1.03      ( X0_44 != sK2 | sK2 = X0_44 | sK2 != sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1803]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1880,plain,
% 1.57/1.03      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1879]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1214,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,X0_45,X1_44)
% 1.57/1.03      | m1_orders_2(X2_44,X0_45,X3_44)
% 1.57/1.03      | X2_44 != X0_44
% 1.57/1.03      | X3_44 != X1_44 ),
% 1.57/1.03      theory(equality) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1883,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,X1_44)
% 1.57/1.03      | m1_orders_2(sK2,sK1,sK2)
% 1.57/1.03      | sK2 != X0_44
% 1.57/1.03      | sK2 != X1_44 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1214]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1885,plain,
% 1.57/1.03      ( m1_orders_2(sK2,sK1,sK2)
% 1.57/1.03      | ~ m1_orders_2(k1_xboole_0,sK1,k1_xboole_0)
% 1.57/1.03      | sK2 != k1_xboole_0 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1883]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_2497,plain,
% 1.57/1.03      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
% 1.57/1.03      | m1_orders_2(X0_44,sK1,sK2) != iProver_top ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_2380,c_16,c_15,c_30,c_419,c_1221,c_1225,c_1226,c_1778,
% 1.57/1.03                 c_1781,c_1821,c_1880,c_1885]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_2505,plain,
% 1.57/1.03      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 | sK2 = k1_xboole_0 ),
% 1.57/1.03      inference(superposition,[status(thm)],[c_1592,c_2497]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_27,plain,
% 1.57/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1759,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,sK2)
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,X0_44)) = X0_44
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1198]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1825,plain,
% 1.57/1.03      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1759]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1826,plain,
% 1.57/1.03      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2
% 1.57/1.03      | k1_xboole_0 = sK2
% 1.57/1.03      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.57/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1825]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_2506,plain,
% 1.57/1.03      ( k3_orders_2(sK1,sK2,sK0(sK1,sK2,sK2)) = sK2 ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_2505,c_16,c_27,c_15,c_30,c_419,c_1225,c_1226,c_1781,
% 1.57/1.03                 c_1821,c_1826,c_1880,c_1885]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_8,plain,
% 1.57/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 1.57/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.57/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.57/1.03      | ~ l1_orders_2(X0) ),
% 1.57/1.03      inference(cnf_transformation,[],[f37]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_11,plain,
% 1.57/1.03      ( r2_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 1.57/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 1.57/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 1.57/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 1.57/1.03      | v2_struct_0(X0)
% 1.57/1.03      | ~ v3_orders_2(X0)
% 1.57/1.03      | ~ v4_orders_2(X0)
% 1.57/1.03      | ~ v5_orders_2(X0)
% 1.57/1.03      | ~ l1_orders_2(X0) ),
% 1.57/1.03      inference(cnf_transformation,[],[f38]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_340,plain,
% 1.57/1.03      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X3))
% 1.57/1.03      | ~ m1_subset_1(X4,u1_struct_0(X5))
% 1.57/1.03      | ~ m1_subset_1(X6,u1_struct_0(X5))
% 1.57/1.03      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X5)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | X1 != X5
% 1.57/1.03      | X0 != X6
% 1.57/1.03      | X3 != X6 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_11]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_341,plain,
% 1.57/1.03      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
% 1.57/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1) ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_340]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_430,plain,
% 1.57/1.03      ( ~ r2_hidden(X0,k3_orders_2(X1,X2,X0))
% 1.57/1.03      | ~ m1_subset_1(X0,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X3,u1_struct_0(X1))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | sK1 != X1 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_341,c_17]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_431,plain,
% 1.57/1.03      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
% 1.57/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | v2_struct_0(sK1)
% 1.57/1.03      | ~ v3_orders_2(sK1)
% 1.57/1.03      | ~ v4_orders_2(sK1)
% 1.57/1.03      | ~ v5_orders_2(sK1) ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_430]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_435,plain,
% 1.57/1.03      ( ~ r2_hidden(X0,k3_orders_2(sK1,X1,X0))
% 1.57/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_431,c_21,c_20,c_19,c_18]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1199,plain,
% 1.57/1.03      ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
% 1.57/1.03      | ~ m1_subset_1(X2_44,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_435]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1207,plain,
% 1.57/1.03      ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
% 1.57/1.03      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | ~ sP1_iProver_split ),
% 1.57/1.03      inference(splitting,
% 1.57/1.03                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 1.57/1.03                [c_1199]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1598,plain,
% 1.57/1.03      ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
% 1.57/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.57/1.03      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.57/1.03      | sP1_iProver_split != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1208,plain,
% 1.57/1.03      ( sP1_iProver_split | sP0_iProver_split ),
% 1.57/1.03      inference(splitting,
% 1.57/1.03                [splitting(split),new_symbols(definition,[])],
% 1.57/1.03                [c_1199]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1206,plain,
% 1.57/1.03      ( ~ m1_subset_1(X0_44,u1_struct_0(sK1)) | ~ sP0_iProver_split ),
% 1.57/1.03      inference(splitting,
% 1.57/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.57/1.03                [c_1199]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1272,plain,
% 1.57/1.03      ( ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/1.03      | ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_1207,c_1208,c_1206]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1273,plain,
% 1.57/1.03      ( ~ r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44))
% 1.57/1.03      | ~ m1_subset_1(X0_44,u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 1.57/1.03      inference(renaming,[status(thm)],[c_1272]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1274,plain,
% 1.57/1.03      ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
% 1.57/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.57/1.03      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1273]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1863,plain,
% 1.57/1.03      ( m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 1.57/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.57/1.03      | r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_1598,c_1274]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1864,plain,
% 1.57/1.03      ( r2_hidden(X0_44,k3_orders_2(sK1,X1_44,X0_44)) != iProver_top
% 1.57/1.03      | m1_subset_1(X0_44,u1_struct_0(sK1)) != iProver_top
% 1.57/1.03      | m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(renaming,[status(thm)],[c_1863]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_2511,plain,
% 1.57/1.03      ( r2_hidden(sK0(sK1,sK2,sK2),sK2) != iProver_top
% 1.57/1.03      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) != iProver_top
% 1.57/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(superposition,[status(thm)],[c_2506,c_1864]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_5,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.57/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(cnf_transformation,[],[f31]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_126,plain,
% 1.57/1.03      ( r2_hidden(sK0(X1,X2,X0),X2)
% 1.57/1.03      | ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(global_propositional_subsumption,[status(thm)],[c_5,c_7]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_127,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(renaming,[status(thm)],[c_126]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_478,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | r2_hidden(sK0(X1,X2,X0),X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | sK1 != X1
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_127,c_17]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_479,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | v2_struct_0(sK1)
% 1.57/1.03      | ~ v3_orders_2(sK1)
% 1.57/1.03      | ~ v4_orders_2(sK1)
% 1.57/1.03      | ~ v5_orders_2(sK1)
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_478]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_483,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | r2_hidden(sK0(sK1,X1,X0),X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_479,c_21,c_20,c_19,c_18]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1197,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,X1_44)
% 1.57/1.03      | r2_hidden(sK0(sK1,X1_44,X0_44),X1_44)
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = X1_44 ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_483]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1754,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,sK2)
% 1.57/1.03      | r2_hidden(sK0(sK1,sK2,X0_44),sK2)
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1197]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1799,plain,
% 1.57/1.03      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.57/1.03      | r2_hidden(sK0(sK1,sK2,sK2),sK2)
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1754]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1800,plain,
% 1.57/1.03      ( k1_xboole_0 = sK2
% 1.57/1.03      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.57/1.03      | r2_hidden(sK0(sK1,sK2,sK2),sK2) = iProver_top
% 1.57/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1799]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_6,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(cnf_transformation,[],[f30]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_121,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | ~ l1_orders_2(X1)
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(global_propositional_subsumption,[status(thm)],[c_6,c_7]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_502,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,X1,X2)
% 1.57/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 1.57/1.03      | m1_subset_1(sK0(X1,X2,X0),u1_struct_0(X1))
% 1.57/1.03      | v2_struct_0(X1)
% 1.57/1.03      | ~ v3_orders_2(X1)
% 1.57/1.03      | ~ v4_orders_2(X1)
% 1.57/1.03      | ~ v5_orders_2(X1)
% 1.57/1.03      | sK1 != X1
% 1.57/1.03      | k1_xboole_0 = X2 ),
% 1.57/1.03      inference(resolution_lifted,[status(thm)],[c_121,c_17]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_503,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.57/1.03      | v2_struct_0(sK1)
% 1.57/1.03      | ~ v3_orders_2(sK1)
% 1.57/1.03      | ~ v4_orders_2(sK1)
% 1.57/1.03      | ~ v5_orders_2(sK1)
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(unflattening,[status(thm)],[c_502]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_507,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0,sK1,X1)
% 1.57/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | m1_subset_1(sK0(sK1,X1,X0),u1_struct_0(sK1))
% 1.57/1.03      | k1_xboole_0 = X1 ),
% 1.57/1.03      inference(global_propositional_subsumption,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_503,c_21,c_20,c_19,c_18]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1196,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,X1_44)
% 1.57/1.03      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | m1_subset_1(sK0(sK1,X1_44,X0_44),u1_struct_0(sK1))
% 1.57/1.03      | k1_xboole_0 = X1_44 ),
% 1.57/1.03      inference(subtyping,[status(esa)],[c_507]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1749,plain,
% 1.57/1.03      ( ~ m1_orders_2(X0_44,sK1,sK2)
% 1.57/1.03      | m1_subset_1(sK0(sK1,sK2,X0_44),u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1196]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1796,plain,
% 1.57/1.03      ( ~ m1_orders_2(sK2,sK1,sK2)
% 1.57/1.03      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1))
% 1.57/1.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
% 1.57/1.03      | k1_xboole_0 = sK2 ),
% 1.57/1.03      inference(instantiation,[status(thm)],[c_1749]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(c_1797,plain,
% 1.57/1.03      ( k1_xboole_0 = sK2
% 1.57/1.03      | m1_orders_2(sK2,sK1,sK2) != iProver_top
% 1.57/1.03      | m1_subset_1(sK0(sK1,sK2,sK2),u1_struct_0(sK1)) = iProver_top
% 1.57/1.03      | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 1.57/1.03      inference(predicate_to_equality,[status(thm)],[c_1796]) ).
% 1.57/1.03  
% 1.57/1.03  cnf(contradiction,plain,
% 1.57/1.03      ( $false ),
% 1.57/1.03      inference(minisat,
% 1.57/1.03                [status(thm)],
% 1.57/1.03                [c_2511,c_1885,c_1880,c_1821,c_1800,c_1797,c_1781,c_1226,
% 1.57/1.03                 c_1225,c_419,c_30,c_15,c_27,c_16]) ).
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 1.57/1.03  
% 1.57/1.03  ------                               Statistics
% 1.57/1.03  
% 1.57/1.03  ------ General
% 1.57/1.03  
% 1.57/1.03  abstr_ref_over_cycles:                  0
% 1.57/1.03  abstr_ref_under_cycles:                 0
% 1.57/1.03  gc_basic_clause_elim:                   0
% 1.57/1.03  forced_gc_time:                         0
% 1.57/1.03  parsing_time:                           0.006
% 1.57/1.03  unif_index_cands_time:                  0.
% 1.57/1.03  unif_index_add_time:                    0.
% 1.57/1.03  orderings_time:                         0.
% 1.57/1.03  out_proof_time:                         0.019
% 1.57/1.03  total_time:                             0.112
% 1.57/1.03  num_of_symbols:                         49
% 1.57/1.03  num_of_terms:                           1752
% 1.57/1.03  
% 1.57/1.03  ------ Preprocessing
% 1.57/1.03  
% 1.57/1.03  num_of_splits:                          2
% 1.57/1.03  num_of_split_atoms:                     2
% 1.57/1.03  num_of_reused_defs:                     0
% 1.57/1.03  num_eq_ax_congr_red:                    20
% 1.57/1.03  num_of_sem_filtered_clauses:            3
% 1.57/1.03  num_of_subtypes:                        3
% 1.57/1.03  monotx_restored_types:                  1
% 1.57/1.03  sat_num_of_epr_types:                   0
% 1.57/1.03  sat_num_of_non_cyclic_types:            0
% 1.57/1.03  sat_guarded_non_collapsed_types:        1
% 1.57/1.03  num_pure_diseq_elim:                    0
% 1.57/1.03  simp_replaced_by:                       0
% 1.57/1.03  res_preprocessed:                       77
% 1.57/1.03  prep_upred:                             0
% 1.57/1.03  prep_unflattend:                        71
% 1.57/1.03  smt_new_axioms:                         0
% 1.57/1.03  pred_elim_cands:                        3
% 1.57/1.03  pred_elim:                              6
% 1.57/1.03  pred_elim_cl:                           6
% 1.57/1.03  pred_elim_cycles:                       8
% 1.57/1.03  merged_defs:                            8
% 1.57/1.03  merged_defs_ncl:                        0
% 1.57/1.03  bin_hyper_res:                          8
% 1.57/1.03  prep_cycles:                            4
% 1.57/1.03  pred_elim_time:                         0.024
% 1.57/1.03  splitting_time:                         0.
% 1.57/1.03  sem_filter_time:                        0.
% 1.57/1.03  monotx_time:                            0.
% 1.57/1.03  subtype_inf_time:                       0.001
% 1.57/1.03  
% 1.57/1.03  ------ Problem properties
% 1.57/1.03  
% 1.57/1.03  clauses:                                16
% 1.57/1.03  conjectures:                            3
% 1.57/1.03  epr:                                    3
% 1.57/1.03  horn:                                   10
% 1.57/1.03  ground:                                 5
% 1.57/1.03  unary:                                  1
% 1.57/1.03  binary:                                 5
% 1.57/1.03  lits:                                   52
% 1.57/1.03  lits_eq:                                8
% 1.57/1.03  fd_pure:                                0
% 1.57/1.03  fd_pseudo:                              0
% 1.57/1.03  fd_cond:                                4
% 1.57/1.03  fd_pseudo_cond:                         0
% 1.57/1.03  ac_symbols:                             0
% 1.57/1.03  
% 1.57/1.03  ------ Propositional Solver
% 1.57/1.03  
% 1.57/1.03  prop_solver_calls:                      27
% 1.57/1.03  prop_fast_solver_calls:                 926
% 1.57/1.03  smt_solver_calls:                       0
% 1.57/1.03  smt_fast_solver_calls:                  0
% 1.57/1.03  prop_num_of_clauses:                    557
% 1.57/1.03  prop_preprocess_simplified:             2576
% 1.57/1.03  prop_fo_subsumed:                       55
% 1.57/1.03  prop_solver_time:                       0.
% 1.57/1.03  smt_solver_time:                        0.
% 1.57/1.03  smt_fast_solver_time:                   0.
% 1.57/1.03  prop_fast_solver_time:                  0.
% 1.57/1.03  prop_unsat_core_time:                   0.
% 1.57/1.03  
% 1.57/1.03  ------ QBF
% 1.57/1.03  
% 1.57/1.03  qbf_q_res:                              0
% 1.57/1.03  qbf_num_tautologies:                    0
% 1.57/1.03  qbf_prep_cycles:                        0
% 1.57/1.03  
% 1.57/1.03  ------ BMC1
% 1.57/1.03  
% 1.57/1.03  bmc1_current_bound:                     -1
% 1.57/1.03  bmc1_last_solved_bound:                 -1
% 1.57/1.03  bmc1_unsat_core_size:                   -1
% 1.57/1.03  bmc1_unsat_core_parents_size:           -1
% 1.57/1.03  bmc1_merge_next_fun:                    0
% 1.57/1.03  bmc1_unsat_core_clauses_time:           0.
% 1.57/1.03  
% 1.57/1.03  ------ Instantiation
% 1.57/1.03  
% 1.57/1.03  inst_num_of_clauses:                    124
% 1.57/1.03  inst_num_in_passive:                    10
% 1.57/1.03  inst_num_in_active:                     79
% 1.57/1.03  inst_num_in_unprocessed:                35
% 1.57/1.03  inst_num_of_loops:                      100
% 1.57/1.03  inst_num_of_learning_restarts:          0
% 1.57/1.03  inst_num_moves_active_passive:          16
% 1.57/1.03  inst_lit_activity:                      0
% 1.57/1.03  inst_lit_activity_moves:                0
% 1.57/1.03  inst_num_tautologies:                   0
% 1.57/1.03  inst_num_prop_implied:                  0
% 1.57/1.03  inst_num_existing_simplified:           0
% 1.57/1.03  inst_num_eq_res_simplified:             0
% 1.57/1.03  inst_num_child_elim:                    0
% 1.57/1.03  inst_num_of_dismatching_blockings:      4
% 1.57/1.03  inst_num_of_non_proper_insts:           116
% 1.57/1.03  inst_num_of_duplicates:                 0
% 1.57/1.03  inst_inst_num_from_inst_to_res:         0
% 1.57/1.03  inst_dismatching_checking_time:         0.
% 1.57/1.03  
% 1.57/1.03  ------ Resolution
% 1.57/1.03  
% 1.57/1.03  res_num_of_clauses:                     0
% 1.57/1.03  res_num_in_passive:                     0
% 1.57/1.03  res_num_in_active:                      0
% 1.57/1.03  res_num_of_loops:                       81
% 1.57/1.03  res_forward_subset_subsumed:            15
% 1.57/1.03  res_backward_subset_subsumed:           0
% 1.57/1.03  res_forward_subsumed:                   0
% 1.57/1.03  res_backward_subsumed:                  0
% 1.57/1.03  res_forward_subsumption_resolution:     3
% 1.57/1.03  res_backward_subsumption_resolution:    0
% 1.57/1.03  res_clause_to_clause_subsumption:       114
% 1.57/1.03  res_orphan_elimination:                 0
% 1.57/1.03  res_tautology_del:                      52
% 1.57/1.03  res_num_eq_res_simplified:              0
% 1.57/1.03  res_num_sel_changes:                    0
% 1.57/1.03  res_moves_from_active_to_pass:          0
% 1.57/1.03  
% 1.57/1.03  ------ Superposition
% 1.57/1.03  
% 1.57/1.03  sup_time_total:                         0.
% 1.57/1.03  sup_time_generating:                    0.
% 1.57/1.03  sup_time_sim_full:                      0.
% 1.57/1.03  sup_time_sim_immed:                     0.
% 1.57/1.03  
% 1.57/1.03  sup_num_of_clauses:                     31
% 1.57/1.03  sup_num_in_active:                      20
% 1.57/1.03  sup_num_in_passive:                     11
% 1.57/1.03  sup_num_of_loops:                       19
% 1.57/1.03  sup_fw_superposition:                   8
% 1.57/1.03  sup_bw_superposition:                   10
% 1.57/1.03  sup_immediate_simplified:               1
% 1.57/1.03  sup_given_eliminated:                   0
% 1.57/1.03  comparisons_done:                       0
% 1.57/1.03  comparisons_avoided:                    1
% 1.57/1.03  
% 1.57/1.03  ------ Simplifications
% 1.57/1.03  
% 1.57/1.03  
% 1.57/1.03  sim_fw_subset_subsumed:                 1
% 1.57/1.03  sim_bw_subset_subsumed:                 0
% 1.57/1.03  sim_fw_subsumed:                        0
% 1.57/1.03  sim_bw_subsumed:                        0
% 1.57/1.03  sim_fw_subsumption_res:                 0
% 1.57/1.03  sim_bw_subsumption_res:                 0
% 1.57/1.03  sim_tautology_del:                      1
% 1.57/1.03  sim_eq_tautology_del:                   0
% 1.57/1.03  sim_eq_res_simp:                        0
% 1.57/1.03  sim_fw_demodulated:                     0
% 1.57/1.03  sim_bw_demodulated:                     0
% 1.57/1.03  sim_light_normalised:                   1
% 1.57/1.03  sim_joinable_taut:                      0
% 1.57/1.03  sim_joinable_simp:                      0
% 1.57/1.03  sim_ac_normalised:                      0
% 1.57/1.03  sim_smt_subsumption:                    0
% 1.57/1.03  
%------------------------------------------------------------------------------
