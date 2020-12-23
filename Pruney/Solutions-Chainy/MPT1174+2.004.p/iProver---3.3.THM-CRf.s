%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:12:43 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 852 expanded)
%              Number of clauses        :   91 ( 166 expanded)
%              Number of leaves         :   15 ( 320 expanded)
%              Depth                    :   30
%              Number of atoms          :  873 (6904 expanded)
%              Number of equality atoms :  185 (1756 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal clause size      :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f32])).

fof(f45,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X2)
                 => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                   => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X2)
                   => ( k1_funct_1(X2,u1_struct_0(X0)) = X1
                     => k1_xboole_0 = k3_orders_2(X0,X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
          & k1_funct_1(X2,u1_struct_0(X0)) = X1
          & m2_orders_2(X3,X0,X2) )
     => ( k1_xboole_0 != k3_orders_2(X0,sK4,X1)
        & k1_funct_1(X2,u1_struct_0(X0)) = X1
        & m2_orders_2(sK4,X0,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
              & k1_funct_1(X2,u1_struct_0(X0)) = X1
              & m2_orders_2(X3,X0,X2) )
          & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
            & k1_funct_1(sK3,u1_struct_0(X0)) = X1
            & m2_orders_2(X3,X0,sK3) )
        & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(X0)) = X1
                  & m2_orders_2(X3,X0,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ? [X3] :
                ( k1_xboole_0 != k3_orders_2(X0,X3,sK2)
                & k1_funct_1(X2,u1_struct_0(X0)) = sK2
                & m2_orders_2(X3,X0,X2) )
            & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( k1_xboole_0 != k3_orders_2(X0,X3,X1)
                    & k1_funct_1(X2,u1_struct_0(X0)) = X1
                    & m2_orders_2(X3,X0,X2) )
                & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( k1_xboole_0 != k3_orders_2(sK1,X3,X1)
                  & k1_funct_1(X2,u1_struct_0(sK1)) = X1
                  & m2_orders_2(X3,sK1,X2) )
              & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)
    & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2
    & m2_orders_2(sK4,sK1,sK3)
    & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f42,f41,f40,f39])).

fof(f60,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f61,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f62,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f63,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f64,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
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
                  ( m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
                 => ! [X4] :
                      ( m2_orders_2(X4,X0,X3)
                     => ( ( k1_funct_1(X3,u1_struct_0(X0)) = X2
                          & r2_hidden(X1,X4) )
                       => r3_orders_2(X0,X2,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( r3_orders_2(X0,X2,X1)
                      | k1_funct_1(X3,u1_struct_0(X0)) != X2
                      | ~ r2_hidden(X1,X4)
                      | ~ m2_orders_2(X4,X0,X3) )
                  | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_orders_2(X0,X2,X1)
      | k1_funct_1(X3,u1_struct_0(X0)) != X2
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X4,X0,X3,X1] :
      ( r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1)
      | ~ r2_hidden(X1,X4)
      | ~ m2_orders_2(X4,X0,X3)
      | ~ m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f66,plain,(
    m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f65,plain,(
    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r2_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ( r1_orders_2(X0,X2,X3)
                        & r2_orders_2(X0,X1,X2) ) )
                   => r2_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r2_orders_2(X0,X1,X3)
                  | ( ( ~ r2_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X0,X1,X3)
      | ~ r2_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <=> ( X1 != X2
                  & r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_orders_2(X0,X1,X2)
                  | X1 = X2
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( ( X1 != X2
                    & r1_orders_2(X0,X1,X2) )
                  | ~ r2_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( X1 != X2
      | ~ r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    ! [X2,X0] :
      ( ~ r2_orders_2(X0,X2,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f68,plain,(
    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1047,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_404,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X0,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v2_struct_0(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_405,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_22,negated_conjecture,
    ( v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_409,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_24,c_22,c_21,c_20])).

cnf(c_410,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_409])).

cnf(c_1041,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_411,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_383,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_23])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_383])).

cnf(c_388,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_384,c_24,c_22,c_21,c_20])).

cnf(c_1042,plain,
    ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1048,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1528,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1042,c_1048])).

cnf(c_1923,plain,
    ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1041,c_411,c_1528])).

cnf(c_1924,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
    | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1923])).

cnf(c_1931,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1924])).

cnf(c_13,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_326,plain,
    ( r2_orders_2(X0,X1,X2)
    | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_327,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_24,c_22,c_21,c_20])).

cnf(c_332,plain,
    ( r2_orders_2(sK1,X0,X1)
    | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_1044,plain,
    ( r2_orders_2(sK1,X0,X1) = iProver_top
    | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1941,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1044])).

cnf(c_2094,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1528])).

cnf(c_2480,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_2094])).

cnf(c_2481,plain,
    ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
    | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2480])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1046,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( ~ r3_orders_2(X0,X1,X2)
    | r1_orders_2(X0,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_14,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m2_orders_2(X3,X0,X1)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_17,negated_conjecture,
    ( m2_orders_2(sK4,sK1,sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_265,plain,
    ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
    | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
    | ~ r2_hidden(X2,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK3 != X1
    | sK4 != X3
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_17])).

cnf(c_266,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_265])).

cnf(c_18,negated_conjecture,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_270,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_266,c_24,c_23,c_22,c_21,c_20,c_18])).

cnf(c_271,plain,
    ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_297,plain,
    ( r1_orders_2(X0,X1,X2)
    | ~ r2_hidden(X3,sK4)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(X0)
    | ~ v3_orders_2(X0)
    | ~ l1_orders_2(X0)
    | X3 != X2
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_271])).

cnf(c_298,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_302,plain,
    ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ r2_hidden(X0,sK4)
    | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_298,c_24,c_23,c_20])).

cnf(c_303,plain,
    ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_302])).

cnf(c_9,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X3)
    | r2_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ v5_orders_2(X0)
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_479,plain,
    ( ~ r1_orders_2(X0,X1,X2)
    | ~ r2_orders_2(X0,X2,X3)
    | r2_orders_2(X0,X1,X3)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ m1_subset_1(X2,u1_struct_0(X0))
    | ~ m1_subset_1(X3,u1_struct_0(X0))
    | ~ v4_orders_2(X0)
    | ~ l1_orders_2(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_480,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_482,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_22,c_20])).

cnf(c_483,plain,
    ( ~ r1_orders_2(sK1,X0,X1)
    | ~ r2_orders_2(sK1,X1,X2)
    | r2_orders_2(sK1,X0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_629,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,X2,X1)
    | ~ r2_hidden(X3,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X3,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
    | X0 != X3
    | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_303,c_483])).

cnf(c_630,plain,
    ( ~ r2_orders_2(sK1,X0,X1)
    | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1)
    | ~ r2_hidden(X0,sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK1))
    | ~ m1_subset_1(X1,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_1037,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_16,negated_conjecture,
    ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1144,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1037,c_16])).

cnf(c_1151,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1144,c_1046])).

cnf(c_6,plain,
    ( ~ m2_orders_2(X0,X1,X2)
    | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_254,plain,
    ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | sK3 != X0
    | sK4 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_17])).

cnf(c_255,plain,
    ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_struct_0(sK1)
    | ~ v3_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v5_orders_2(sK1)
    | ~ l1_orders_2(sK1) ),
    inference(unflattening,[status(thm)],[c_254])).

cnf(c_257,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_255,c_24,c_23,c_22,c_21,c_20,c_18])).

cnf(c_1045,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_257])).

cnf(c_1527,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1048])).

cnf(c_1630,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_orders_2(sK1,X0,X1) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1151,c_1527])).

cnf(c_1631,plain,
    ( r2_orders_2(sK1,X0,X1) != iProver_top
    | r2_orders_2(sK1,sK2,X1) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top
    | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1630])).

cnf(c_1638,plain,
    ( r2_orders_2(sK1,X0,sK2) != iProver_top
    | r2_orders_2(sK1,sK2,sK2) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1046,c_1631])).

cnf(c_30,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ l1_orders_2(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_537,plain,
    ( ~ r2_orders_2(X0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_20])).

cnf(c_538,plain,
    ( ~ r2_orders_2(sK1,X0,X0)
    | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_1190,plain,
    ( ~ r2_orders_2(sK1,sK2,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_538])).

cnf(c_1191,plain,
    ( r2_orders_2(sK1,sK2,sK2) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1190])).

cnf(c_1791,plain,
    ( r2_orders_2(sK1,X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_30,c_1191])).

cnf(c_2491,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2481,c_1791])).

cnf(c_2519,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | k3_orders_2(sK1,X0,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2491,c_30])).

cnf(c_2520,plain,
    ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
    | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2519])).

cnf(c_2528,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
    | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1931,c_2520])).

cnf(c_25,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_26,plain,
    ( v3_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_27,plain,
    ( v4_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_28,plain,
    ( v5_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_29,plain,
    ( l1_orders_2(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_31,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_256,plain,
    ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v3_orders_2(sK1) != iProver_top
    | v4_orders_2(sK1) != iProver_top
    | v5_orders_2(sK1) != iProver_top
    | l1_orders_2(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_255])).

cnf(c_3444,plain,
    ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2528,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_256])).

cnf(c_15,negated_conjecture,
    ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3447,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3444,c_15])).

cnf(c_3537,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_3447])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.53/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.53/1.02  
% 2.53/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.53/1.02  
% 2.53/1.02  ------  iProver source info
% 2.53/1.02  
% 2.53/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.53/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.53/1.02  git: non_committed_changes: false
% 2.53/1.02  git: last_make_outside_of_git: false
% 2.53/1.02  
% 2.53/1.02  ------ 
% 2.53/1.02  
% 2.53/1.02  ------ Input Options
% 2.53/1.02  
% 2.53/1.02  --out_options                           all
% 2.53/1.02  --tptp_safe_out                         true
% 2.53/1.02  --problem_path                          ""
% 2.53/1.02  --include_path                          ""
% 2.53/1.02  --clausifier                            res/vclausify_rel
% 2.53/1.02  --clausifier_options                    --mode clausify
% 2.53/1.02  --stdin                                 false
% 2.53/1.02  --stats_out                             all
% 2.53/1.02  
% 2.53/1.02  ------ General Options
% 2.53/1.02  
% 2.53/1.02  --fof                                   false
% 2.53/1.02  --time_out_real                         305.
% 2.53/1.02  --time_out_virtual                      -1.
% 2.53/1.02  --symbol_type_check                     false
% 2.53/1.02  --clausify_out                          false
% 2.53/1.02  --sig_cnt_out                           false
% 2.53/1.02  --trig_cnt_out                          false
% 2.53/1.02  --trig_cnt_out_tolerance                1.
% 2.53/1.02  --trig_cnt_out_sk_spl                   false
% 2.53/1.02  --abstr_cl_out                          false
% 2.53/1.02  
% 2.53/1.02  ------ Global Options
% 2.53/1.02  
% 2.53/1.02  --schedule                              default
% 2.53/1.02  --add_important_lit                     false
% 2.53/1.02  --prop_solver_per_cl                    1000
% 2.53/1.02  --min_unsat_core                        false
% 2.53/1.02  --soft_assumptions                      false
% 2.53/1.02  --soft_lemma_size                       3
% 2.53/1.02  --prop_impl_unit_size                   0
% 2.53/1.02  --prop_impl_unit                        []
% 2.53/1.02  --share_sel_clauses                     true
% 2.53/1.02  --reset_solvers                         false
% 2.53/1.02  --bc_imp_inh                            [conj_cone]
% 2.53/1.02  --conj_cone_tolerance                   3.
% 2.53/1.02  --extra_neg_conj                        none
% 2.53/1.02  --large_theory_mode                     true
% 2.53/1.02  --prolific_symb_bound                   200
% 2.53/1.02  --lt_threshold                          2000
% 2.53/1.02  --clause_weak_htbl                      true
% 2.53/1.02  --gc_record_bc_elim                     false
% 2.53/1.02  
% 2.53/1.02  ------ Preprocessing Options
% 2.53/1.02  
% 2.53/1.02  --preprocessing_flag                    true
% 2.53/1.02  --time_out_prep_mult                    0.1
% 2.53/1.02  --splitting_mode                        input
% 2.53/1.02  --splitting_grd                         true
% 2.53/1.02  --splitting_cvd                         false
% 2.53/1.02  --splitting_cvd_svl                     false
% 2.53/1.02  --splitting_nvd                         32
% 2.53/1.02  --sub_typing                            true
% 2.53/1.02  --prep_gs_sim                           true
% 2.53/1.02  --prep_unflatten                        true
% 2.53/1.02  --prep_res_sim                          true
% 2.53/1.02  --prep_upred                            true
% 2.53/1.02  --prep_sem_filter                       exhaustive
% 2.53/1.02  --prep_sem_filter_out                   false
% 2.53/1.02  --pred_elim                             true
% 2.53/1.02  --res_sim_input                         true
% 2.53/1.02  --eq_ax_congr_red                       true
% 2.53/1.02  --pure_diseq_elim                       true
% 2.53/1.02  --brand_transform                       false
% 2.53/1.02  --non_eq_to_eq                          false
% 2.53/1.02  --prep_def_merge                        true
% 2.53/1.02  --prep_def_merge_prop_impl              false
% 2.53/1.02  --prep_def_merge_mbd                    true
% 2.53/1.02  --prep_def_merge_tr_red                 false
% 2.53/1.02  --prep_def_merge_tr_cl                  false
% 2.53/1.02  --smt_preprocessing                     true
% 2.53/1.02  --smt_ac_axioms                         fast
% 2.53/1.02  --preprocessed_out                      false
% 2.53/1.02  --preprocessed_stats                    false
% 2.53/1.02  
% 2.53/1.02  ------ Abstraction refinement Options
% 2.53/1.02  
% 2.53/1.02  --abstr_ref                             []
% 2.53/1.02  --abstr_ref_prep                        false
% 2.53/1.02  --abstr_ref_until_sat                   false
% 2.53/1.02  --abstr_ref_sig_restrict                funpre
% 2.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.02  --abstr_ref_under                       []
% 2.53/1.02  
% 2.53/1.02  ------ SAT Options
% 2.53/1.02  
% 2.53/1.02  --sat_mode                              false
% 2.53/1.02  --sat_fm_restart_options                ""
% 2.53/1.02  --sat_gr_def                            false
% 2.53/1.02  --sat_epr_types                         true
% 2.53/1.02  --sat_non_cyclic_types                  false
% 2.53/1.02  --sat_finite_models                     false
% 2.53/1.02  --sat_fm_lemmas                         false
% 2.53/1.02  --sat_fm_prep                           false
% 2.53/1.02  --sat_fm_uc_incr                        true
% 2.53/1.02  --sat_out_model                         small
% 2.53/1.02  --sat_out_clauses                       false
% 2.53/1.02  
% 2.53/1.02  ------ QBF Options
% 2.53/1.02  
% 2.53/1.02  --qbf_mode                              false
% 2.53/1.02  --qbf_elim_univ                         false
% 2.53/1.02  --qbf_dom_inst                          none
% 2.53/1.02  --qbf_dom_pre_inst                      false
% 2.53/1.02  --qbf_sk_in                             false
% 2.53/1.02  --qbf_pred_elim                         true
% 2.53/1.02  --qbf_split                             512
% 2.53/1.02  
% 2.53/1.02  ------ BMC1 Options
% 2.53/1.02  
% 2.53/1.02  --bmc1_incremental                      false
% 2.53/1.02  --bmc1_axioms                           reachable_all
% 2.53/1.02  --bmc1_min_bound                        0
% 2.53/1.02  --bmc1_max_bound                        -1
% 2.53/1.02  --bmc1_max_bound_default                -1
% 2.53/1.02  --bmc1_symbol_reachability              true
% 2.53/1.02  --bmc1_property_lemmas                  false
% 2.53/1.02  --bmc1_k_induction                      false
% 2.53/1.02  --bmc1_non_equiv_states                 false
% 2.53/1.02  --bmc1_deadlock                         false
% 2.53/1.02  --bmc1_ucm                              false
% 2.53/1.02  --bmc1_add_unsat_core                   none
% 2.53/1.02  --bmc1_unsat_core_children              false
% 2.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.02  --bmc1_out_stat                         full
% 2.53/1.02  --bmc1_ground_init                      false
% 2.53/1.02  --bmc1_pre_inst_next_state              false
% 2.53/1.02  --bmc1_pre_inst_state                   false
% 2.53/1.02  --bmc1_pre_inst_reach_state             false
% 2.53/1.02  --bmc1_out_unsat_core                   false
% 2.53/1.02  --bmc1_aig_witness_out                  false
% 2.53/1.02  --bmc1_verbose                          false
% 2.53/1.02  --bmc1_dump_clauses_tptp                false
% 2.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.02  --bmc1_dump_file                        -
% 2.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.02  --bmc1_ucm_extend_mode                  1
% 2.53/1.02  --bmc1_ucm_init_mode                    2
% 2.53/1.02  --bmc1_ucm_cone_mode                    none
% 2.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.02  --bmc1_ucm_relax_model                  4
% 2.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.02  --bmc1_ucm_layered_model                none
% 2.53/1.02  --bmc1_ucm_max_lemma_size               10
% 2.53/1.02  
% 2.53/1.02  ------ AIG Options
% 2.53/1.02  
% 2.53/1.02  --aig_mode                              false
% 2.53/1.02  
% 2.53/1.02  ------ Instantiation Options
% 2.53/1.02  
% 2.53/1.02  --instantiation_flag                    true
% 2.53/1.02  --inst_sos_flag                         false
% 2.53/1.02  --inst_sos_phase                        true
% 2.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.02  --inst_lit_sel_side                     num_symb
% 2.53/1.02  --inst_solver_per_active                1400
% 2.53/1.02  --inst_solver_calls_frac                1.
% 2.53/1.02  --inst_passive_queue_type               priority_queues
% 2.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.02  --inst_passive_queues_freq              [25;2]
% 2.53/1.02  --inst_dismatching                      true
% 2.53/1.02  --inst_eager_unprocessed_to_passive     true
% 2.53/1.02  --inst_prop_sim_given                   true
% 2.53/1.02  --inst_prop_sim_new                     false
% 2.53/1.02  --inst_subs_new                         false
% 2.53/1.02  --inst_eq_res_simp                      false
% 2.53/1.02  --inst_subs_given                       false
% 2.53/1.02  --inst_orphan_elimination               true
% 2.53/1.02  --inst_learning_loop_flag               true
% 2.53/1.02  --inst_learning_start                   3000
% 2.53/1.02  --inst_learning_factor                  2
% 2.53/1.02  --inst_start_prop_sim_after_learn       3
% 2.53/1.02  --inst_sel_renew                        solver
% 2.53/1.02  --inst_lit_activity_flag                true
% 2.53/1.02  --inst_restr_to_given                   false
% 2.53/1.02  --inst_activity_threshold               500
% 2.53/1.02  --inst_out_proof                        true
% 2.53/1.02  
% 2.53/1.02  ------ Resolution Options
% 2.53/1.02  
% 2.53/1.02  --resolution_flag                       true
% 2.53/1.02  --res_lit_sel                           adaptive
% 2.53/1.02  --res_lit_sel_side                      none
% 2.53/1.02  --res_ordering                          kbo
% 2.53/1.02  --res_to_prop_solver                    active
% 2.53/1.02  --res_prop_simpl_new                    false
% 2.53/1.02  --res_prop_simpl_given                  true
% 2.53/1.02  --res_passive_queue_type                priority_queues
% 2.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.02  --res_passive_queues_freq               [15;5]
% 2.53/1.02  --res_forward_subs                      full
% 2.53/1.02  --res_backward_subs                     full
% 2.53/1.02  --res_forward_subs_resolution           true
% 2.53/1.02  --res_backward_subs_resolution          true
% 2.53/1.02  --res_orphan_elimination                true
% 2.53/1.02  --res_time_limit                        2.
% 2.53/1.02  --res_out_proof                         true
% 2.53/1.02  
% 2.53/1.02  ------ Superposition Options
% 2.53/1.02  
% 2.53/1.02  --superposition_flag                    true
% 2.53/1.02  --sup_passive_queue_type                priority_queues
% 2.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.02  --demod_completeness_check              fast
% 2.53/1.02  --demod_use_ground                      true
% 2.53/1.02  --sup_to_prop_solver                    passive
% 2.53/1.02  --sup_prop_simpl_new                    true
% 2.53/1.02  --sup_prop_simpl_given                  true
% 2.53/1.02  --sup_fun_splitting                     false
% 2.53/1.02  --sup_smt_interval                      50000
% 2.53/1.02  
% 2.53/1.02  ------ Superposition Simplification Setup
% 2.53/1.02  
% 2.53/1.02  --sup_indices_passive                   []
% 2.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_full_bw                           [BwDemod]
% 2.53/1.02  --sup_immed_triv                        [TrivRules]
% 2.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_immed_bw_main                     []
% 2.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.02  
% 2.53/1.02  ------ Combination Options
% 2.53/1.02  
% 2.53/1.02  --comb_res_mult                         3
% 2.53/1.02  --comb_sup_mult                         2
% 2.53/1.02  --comb_inst_mult                        10
% 2.53/1.02  
% 2.53/1.02  ------ Debug Options
% 2.53/1.02  
% 2.53/1.02  --dbg_backtrace                         false
% 2.53/1.02  --dbg_dump_prop_clauses                 false
% 2.53/1.02  --dbg_dump_prop_clauses_file            -
% 2.53/1.02  --dbg_out_stat                          false
% 2.53/1.02  ------ Parsing...
% 2.53/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.53/1.02  
% 2.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 9 0s  sf_e  pe_s  pe_e 
% 2.53/1.02  
% 2.53/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.53/1.02  
% 2.53/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.53/1.02  ------ Proving...
% 2.53/1.02  ------ Problem Properties 
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  clauses                                 15
% 2.53/1.02  conjectures                             3
% 2.53/1.02  EPR                                     0
% 2.53/1.02  Horn                                    13
% 2.53/1.02  unary                                   4
% 2.53/1.02  binary                                  2
% 2.53/1.02  lits                                    52
% 2.53/1.02  lits eq                                 4
% 2.53/1.02  fd_pure                                 0
% 2.53/1.02  fd_pseudo                               0
% 2.53/1.02  fd_cond                                 2
% 2.53/1.02  fd_pseudo_cond                          0
% 2.53/1.02  AC symbols                              0
% 2.53/1.02  
% 2.53/1.02  ------ Schedule dynamic 5 is on 
% 2.53/1.02  
% 2.53/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  ------ 
% 2.53/1.02  Current options:
% 2.53/1.02  ------ 
% 2.53/1.02  
% 2.53/1.02  ------ Input Options
% 2.53/1.02  
% 2.53/1.02  --out_options                           all
% 2.53/1.02  --tptp_safe_out                         true
% 2.53/1.02  --problem_path                          ""
% 2.53/1.02  --include_path                          ""
% 2.53/1.02  --clausifier                            res/vclausify_rel
% 2.53/1.02  --clausifier_options                    --mode clausify
% 2.53/1.02  --stdin                                 false
% 2.53/1.02  --stats_out                             all
% 2.53/1.02  
% 2.53/1.02  ------ General Options
% 2.53/1.02  
% 2.53/1.02  --fof                                   false
% 2.53/1.02  --time_out_real                         305.
% 2.53/1.02  --time_out_virtual                      -1.
% 2.53/1.02  --symbol_type_check                     false
% 2.53/1.02  --clausify_out                          false
% 2.53/1.02  --sig_cnt_out                           false
% 2.53/1.02  --trig_cnt_out                          false
% 2.53/1.02  --trig_cnt_out_tolerance                1.
% 2.53/1.02  --trig_cnt_out_sk_spl                   false
% 2.53/1.02  --abstr_cl_out                          false
% 2.53/1.02  
% 2.53/1.02  ------ Global Options
% 2.53/1.02  
% 2.53/1.02  --schedule                              default
% 2.53/1.02  --add_important_lit                     false
% 2.53/1.02  --prop_solver_per_cl                    1000
% 2.53/1.02  --min_unsat_core                        false
% 2.53/1.02  --soft_assumptions                      false
% 2.53/1.02  --soft_lemma_size                       3
% 2.53/1.02  --prop_impl_unit_size                   0
% 2.53/1.02  --prop_impl_unit                        []
% 2.53/1.02  --share_sel_clauses                     true
% 2.53/1.02  --reset_solvers                         false
% 2.53/1.02  --bc_imp_inh                            [conj_cone]
% 2.53/1.02  --conj_cone_tolerance                   3.
% 2.53/1.02  --extra_neg_conj                        none
% 2.53/1.02  --large_theory_mode                     true
% 2.53/1.02  --prolific_symb_bound                   200
% 2.53/1.02  --lt_threshold                          2000
% 2.53/1.02  --clause_weak_htbl                      true
% 2.53/1.02  --gc_record_bc_elim                     false
% 2.53/1.02  
% 2.53/1.02  ------ Preprocessing Options
% 2.53/1.02  
% 2.53/1.02  --preprocessing_flag                    true
% 2.53/1.02  --time_out_prep_mult                    0.1
% 2.53/1.02  --splitting_mode                        input
% 2.53/1.02  --splitting_grd                         true
% 2.53/1.02  --splitting_cvd                         false
% 2.53/1.02  --splitting_cvd_svl                     false
% 2.53/1.02  --splitting_nvd                         32
% 2.53/1.02  --sub_typing                            true
% 2.53/1.02  --prep_gs_sim                           true
% 2.53/1.02  --prep_unflatten                        true
% 2.53/1.02  --prep_res_sim                          true
% 2.53/1.02  --prep_upred                            true
% 2.53/1.02  --prep_sem_filter                       exhaustive
% 2.53/1.02  --prep_sem_filter_out                   false
% 2.53/1.02  --pred_elim                             true
% 2.53/1.02  --res_sim_input                         true
% 2.53/1.02  --eq_ax_congr_red                       true
% 2.53/1.02  --pure_diseq_elim                       true
% 2.53/1.02  --brand_transform                       false
% 2.53/1.02  --non_eq_to_eq                          false
% 2.53/1.02  --prep_def_merge                        true
% 2.53/1.02  --prep_def_merge_prop_impl              false
% 2.53/1.02  --prep_def_merge_mbd                    true
% 2.53/1.02  --prep_def_merge_tr_red                 false
% 2.53/1.02  --prep_def_merge_tr_cl                  false
% 2.53/1.02  --smt_preprocessing                     true
% 2.53/1.02  --smt_ac_axioms                         fast
% 2.53/1.02  --preprocessed_out                      false
% 2.53/1.02  --preprocessed_stats                    false
% 2.53/1.02  
% 2.53/1.02  ------ Abstraction refinement Options
% 2.53/1.02  
% 2.53/1.02  --abstr_ref                             []
% 2.53/1.02  --abstr_ref_prep                        false
% 2.53/1.02  --abstr_ref_until_sat                   false
% 2.53/1.02  --abstr_ref_sig_restrict                funpre
% 2.53/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.53/1.02  --abstr_ref_under                       []
% 2.53/1.02  
% 2.53/1.02  ------ SAT Options
% 2.53/1.02  
% 2.53/1.02  --sat_mode                              false
% 2.53/1.02  --sat_fm_restart_options                ""
% 2.53/1.02  --sat_gr_def                            false
% 2.53/1.02  --sat_epr_types                         true
% 2.53/1.02  --sat_non_cyclic_types                  false
% 2.53/1.02  --sat_finite_models                     false
% 2.53/1.02  --sat_fm_lemmas                         false
% 2.53/1.02  --sat_fm_prep                           false
% 2.53/1.02  --sat_fm_uc_incr                        true
% 2.53/1.02  --sat_out_model                         small
% 2.53/1.02  --sat_out_clauses                       false
% 2.53/1.02  
% 2.53/1.02  ------ QBF Options
% 2.53/1.02  
% 2.53/1.02  --qbf_mode                              false
% 2.53/1.02  --qbf_elim_univ                         false
% 2.53/1.02  --qbf_dom_inst                          none
% 2.53/1.02  --qbf_dom_pre_inst                      false
% 2.53/1.02  --qbf_sk_in                             false
% 2.53/1.02  --qbf_pred_elim                         true
% 2.53/1.02  --qbf_split                             512
% 2.53/1.02  
% 2.53/1.02  ------ BMC1 Options
% 2.53/1.02  
% 2.53/1.02  --bmc1_incremental                      false
% 2.53/1.02  --bmc1_axioms                           reachable_all
% 2.53/1.02  --bmc1_min_bound                        0
% 2.53/1.02  --bmc1_max_bound                        -1
% 2.53/1.02  --bmc1_max_bound_default                -1
% 2.53/1.02  --bmc1_symbol_reachability              true
% 2.53/1.02  --bmc1_property_lemmas                  false
% 2.53/1.02  --bmc1_k_induction                      false
% 2.53/1.02  --bmc1_non_equiv_states                 false
% 2.53/1.02  --bmc1_deadlock                         false
% 2.53/1.02  --bmc1_ucm                              false
% 2.53/1.02  --bmc1_add_unsat_core                   none
% 2.53/1.02  --bmc1_unsat_core_children              false
% 2.53/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.53/1.02  --bmc1_out_stat                         full
% 2.53/1.02  --bmc1_ground_init                      false
% 2.53/1.02  --bmc1_pre_inst_next_state              false
% 2.53/1.02  --bmc1_pre_inst_state                   false
% 2.53/1.02  --bmc1_pre_inst_reach_state             false
% 2.53/1.02  --bmc1_out_unsat_core                   false
% 2.53/1.02  --bmc1_aig_witness_out                  false
% 2.53/1.02  --bmc1_verbose                          false
% 2.53/1.02  --bmc1_dump_clauses_tptp                false
% 2.53/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.53/1.02  --bmc1_dump_file                        -
% 2.53/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.53/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.53/1.02  --bmc1_ucm_extend_mode                  1
% 2.53/1.02  --bmc1_ucm_init_mode                    2
% 2.53/1.02  --bmc1_ucm_cone_mode                    none
% 2.53/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.53/1.02  --bmc1_ucm_relax_model                  4
% 2.53/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.53/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.53/1.02  --bmc1_ucm_layered_model                none
% 2.53/1.02  --bmc1_ucm_max_lemma_size               10
% 2.53/1.02  
% 2.53/1.02  ------ AIG Options
% 2.53/1.02  
% 2.53/1.02  --aig_mode                              false
% 2.53/1.02  
% 2.53/1.02  ------ Instantiation Options
% 2.53/1.02  
% 2.53/1.02  --instantiation_flag                    true
% 2.53/1.02  --inst_sos_flag                         false
% 2.53/1.02  --inst_sos_phase                        true
% 2.53/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.53/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.53/1.02  --inst_lit_sel_side                     none
% 2.53/1.02  --inst_solver_per_active                1400
% 2.53/1.02  --inst_solver_calls_frac                1.
% 2.53/1.02  --inst_passive_queue_type               priority_queues
% 2.53/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.53/1.02  --inst_passive_queues_freq              [25;2]
% 2.53/1.02  --inst_dismatching                      true
% 2.53/1.02  --inst_eager_unprocessed_to_passive     true
% 2.53/1.02  --inst_prop_sim_given                   true
% 2.53/1.02  --inst_prop_sim_new                     false
% 2.53/1.02  --inst_subs_new                         false
% 2.53/1.02  --inst_eq_res_simp                      false
% 2.53/1.02  --inst_subs_given                       false
% 2.53/1.02  --inst_orphan_elimination               true
% 2.53/1.02  --inst_learning_loop_flag               true
% 2.53/1.02  --inst_learning_start                   3000
% 2.53/1.02  --inst_learning_factor                  2
% 2.53/1.02  --inst_start_prop_sim_after_learn       3
% 2.53/1.02  --inst_sel_renew                        solver
% 2.53/1.02  --inst_lit_activity_flag                true
% 2.53/1.02  --inst_restr_to_given                   false
% 2.53/1.02  --inst_activity_threshold               500
% 2.53/1.02  --inst_out_proof                        true
% 2.53/1.02  
% 2.53/1.02  ------ Resolution Options
% 2.53/1.02  
% 2.53/1.02  --resolution_flag                       false
% 2.53/1.02  --res_lit_sel                           adaptive
% 2.53/1.02  --res_lit_sel_side                      none
% 2.53/1.02  --res_ordering                          kbo
% 2.53/1.02  --res_to_prop_solver                    active
% 2.53/1.02  --res_prop_simpl_new                    false
% 2.53/1.02  --res_prop_simpl_given                  true
% 2.53/1.02  --res_passive_queue_type                priority_queues
% 2.53/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.53/1.02  --res_passive_queues_freq               [15;5]
% 2.53/1.02  --res_forward_subs                      full
% 2.53/1.02  --res_backward_subs                     full
% 2.53/1.02  --res_forward_subs_resolution           true
% 2.53/1.02  --res_backward_subs_resolution          true
% 2.53/1.02  --res_orphan_elimination                true
% 2.53/1.02  --res_time_limit                        2.
% 2.53/1.02  --res_out_proof                         true
% 2.53/1.02  
% 2.53/1.02  ------ Superposition Options
% 2.53/1.02  
% 2.53/1.02  --superposition_flag                    true
% 2.53/1.02  --sup_passive_queue_type                priority_queues
% 2.53/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.53/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.53/1.02  --demod_completeness_check              fast
% 2.53/1.02  --demod_use_ground                      true
% 2.53/1.02  --sup_to_prop_solver                    passive
% 2.53/1.02  --sup_prop_simpl_new                    true
% 2.53/1.02  --sup_prop_simpl_given                  true
% 2.53/1.02  --sup_fun_splitting                     false
% 2.53/1.02  --sup_smt_interval                      50000
% 2.53/1.02  
% 2.53/1.02  ------ Superposition Simplification Setup
% 2.53/1.02  
% 2.53/1.02  --sup_indices_passive                   []
% 2.53/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.53/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.53/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_full_bw                           [BwDemod]
% 2.53/1.02  --sup_immed_triv                        [TrivRules]
% 2.53/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.53/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_immed_bw_main                     []
% 2.53/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.53/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.53/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.53/1.02  
% 2.53/1.02  ------ Combination Options
% 2.53/1.02  
% 2.53/1.02  --comb_res_mult                         3
% 2.53/1.02  --comb_sup_mult                         2
% 2.53/1.02  --comb_inst_mult                        10
% 2.53/1.02  
% 2.53/1.02  ------ Debug Options
% 2.53/1.02  
% 2.53/1.02  --dbg_backtrace                         false
% 2.53/1.02  --dbg_dump_prop_clauses                 false
% 2.53/1.02  --dbg_dump_prop_clauses_file            -
% 2.53/1.02  --dbg_out_stat                          false
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  ------ Proving...
% 2.53/1.02  
% 2.53/1.02  
% 2.53/1.02  % SZS status Theorem for theBenchmark.p
% 2.53/1.02  
% 2.53/1.02   Resolution empty clause
% 2.53/1.02  
% 2.53/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.53/1.02  
% 2.53/1.02  fof(f2,axiom,(
% 2.53/1.02    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f13,plain,(
% 2.53/1.02    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.53/1.02    inference(pure_predicate_removal,[],[f2])).
% 2.53/1.02  
% 2.53/1.02  fof(f16,plain,(
% 2.53/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.53/1.02    inference(ennf_transformation,[],[f13])).
% 2.53/1.02  
% 2.53/1.02  fof(f32,plain,(
% 2.53/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.53/1.02    introduced(choice_axiom,[])).
% 2.53/1.02  
% 2.53/1.02  fof(f33,plain,(
% 2.53/1.02    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f32])).
% 2.53/1.02  
% 2.53/1.02  fof(f45,plain,(
% 2.53/1.02    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.53/1.02    inference(cnf_transformation,[],[f33])).
% 2.53/1.02  
% 2.53/1.02  fof(f8,axiom,(
% 2.53/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f26,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f8])).
% 2.53/1.02  
% 2.53/1.02  fof(f27,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f26])).
% 2.53/1.02  
% 2.53/1.02  fof(f37,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(nnf_transformation,[],[f27])).
% 2.53/1.02  
% 2.53/1.02  fof(f38,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f37])).
% 2.53/1.02  
% 2.53/1.02  fof(f56,plain,(
% 2.53/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f38])).
% 2.53/1.02  
% 2.53/1.02  fof(f10,conjecture,(
% 2.53/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f11,negated_conjecture,(
% 2.53/1.02    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_orders_1(X2,k1_orders_1(u1_struct_0(X0))) => ! [X3] : (m2_orders_2(X3,X0,X2) => (k1_funct_1(X2,u1_struct_0(X0)) = X1 => k1_xboole_0 = k3_orders_2(X0,X3,X1))))))),
% 2.53/1.02    inference(negated_conjecture,[],[f10])).
% 2.53/1.02  
% 2.53/1.02  fof(f30,plain,(
% 2.53/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1) & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f11])).
% 2.53/1.02  
% 2.53/1.02  fof(f31,plain,(
% 2.53/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f30])).
% 2.53/1.02  
% 2.53/1.02  fof(f42,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) => (k1_xboole_0 != k3_orders_2(X0,sK4,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(sK4,X0,X2))) )),
% 2.53/1.02    introduced(choice_axiom,[])).
% 2.53/1.02  
% 2.53/1.02  fof(f41,plain,(
% 2.53/1.02    ( ! [X0,X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) => (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(sK3,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(X0))))) )),
% 2.53/1.02    introduced(choice_axiom,[])).
% 2.53/1.02  
% 2.53/1.02  fof(f40,plain,(
% 2.53/1.02    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,sK2) & k1_funct_1(X2,u1_struct_0(X0)) = sK2 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 2.53/1.02    introduced(choice_axiom,[])).
% 2.53/1.02  
% 2.53/1.02  fof(f39,plain,(
% 2.53/1.02    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(X0,X3,X1) & k1_funct_1(X2,u1_struct_0(X0)) = X1 & m2_orders_2(X3,X0,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (k1_xboole_0 != k3_orders_2(sK1,X3,X1) & k1_funct_1(X2,u1_struct_0(sK1)) = X1 & m2_orders_2(X3,sK1,X2)) & m1_orders_1(X2,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 2.53/1.02    introduced(choice_axiom,[])).
% 2.53/1.02  
% 2.53/1.02  fof(f43,plain,(
% 2.53/1.02    (((k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) & k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 & m2_orders_2(sK4,sK1,sK3)) & m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 2.53/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f31,f42,f41,f40,f39])).
% 2.53/1.02  
% 2.53/1.02  fof(f60,plain,(
% 2.53/1.02    v3_orders_2(sK1)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f59,plain,(
% 2.53/1.02    ~v2_struct_0(sK1)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f61,plain,(
% 2.53/1.02    v4_orders_2(sK1)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f62,plain,(
% 2.53/1.02    v5_orders_2(sK1)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f63,plain,(
% 2.53/1.02    l1_orders_2(sK1)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f4,axiom,(
% 2.53/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f18,plain,(
% 2.53/1.02    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f4])).
% 2.53/1.02  
% 2.53/1.02  fof(f19,plain,(
% 2.53/1.02    ! [X0,X1,X2] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f18])).
% 2.53/1.02  
% 2.53/1.02  fof(f49,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k3_orders_2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f19])).
% 2.53/1.02  
% 2.53/1.02  fof(f1,axiom,(
% 2.53/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f14,plain,(
% 2.53/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.53/1.02    inference(ennf_transformation,[],[f1])).
% 2.53/1.02  
% 2.53/1.02  fof(f15,plain,(
% 2.53/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.53/1.02    inference(flattening,[],[f14])).
% 2.53/1.02  
% 2.53/1.02  fof(f44,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f15])).
% 2.53/1.02  
% 2.53/1.02  fof(f55,plain,(
% 2.53/1.02    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X2) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f38])).
% 2.53/1.02  
% 2.53/1.02  fof(f64,plain,(
% 2.53/1.02    m1_subset_1(sK2,u1_struct_0(sK1))),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f6,axiom,(
% 2.53/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f22,plain,(
% 2.53/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f6])).
% 2.53/1.02  
% 2.53/1.02  fof(f23,plain,(
% 2.53/1.02    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f22])).
% 2.53/1.02  
% 2.53/1.02  fof(f36,plain,(
% 2.53/1.02    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(nnf_transformation,[],[f23])).
% 2.53/1.02  
% 2.53/1.02  fof(f51,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f36])).
% 2.53/1.02  
% 2.53/1.02  fof(f9,axiom,(
% 2.53/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) => ! [X4] : (m2_orders_2(X4,X0,X3) => ((k1_funct_1(X3,u1_struct_0(X0)) = X2 & r2_hidden(X1,X4)) => r3_orders_2(X0,X2,X1)))))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f28,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r3_orders_2(X0,X2,X1) | (k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4))) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f9])).
% 2.53/1.02  
% 2.53/1.02  fof(f29,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3)) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f28])).
% 2.53/1.02  
% 2.53/1.02  fof(f58,plain,(
% 2.53/1.02    ( ! [X4,X2,X0,X3,X1] : (r3_orders_2(X0,X2,X1) | k1_funct_1(X3,u1_struct_0(X0)) != X2 | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f29])).
% 2.53/1.02  
% 2.53/1.02  fof(f70,plain,(
% 2.53/1.02    ( ! [X4,X0,X3,X1] : (r3_orders_2(X0,k1_funct_1(X3,u1_struct_0(X0)),X1) | ~r2_hidden(X1,X4) | ~m2_orders_2(X4,X0,X3) | ~m1_orders_1(X3,k1_orders_1(u1_struct_0(X0))) | ~m1_subset_1(k1_funct_1(X3,u1_struct_0(X0)),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(equality_resolution,[],[f58])).
% 2.53/1.02  
% 2.53/1.02  fof(f66,plain,(
% 2.53/1.02    m2_orders_2(sK4,sK1,sK3)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f65,plain,(
% 2.53/1.02    m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f7,axiom,(
% 2.53/1.02    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (((r2_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) | (r1_orders_2(X0,X2,X3) & r2_orders_2(X0,X1,X2))) => r2_orders_2(X0,X1,X3))))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f24,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2)))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f7])).
% 2.53/1.02  
% 2.53/1.02  fof(f25,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r2_orders_2(X0,X1,X3) | ((~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2)) & (~r1_orders_2(X0,X2,X3) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0))),
% 2.53/1.02    inference(flattening,[],[f24])).
% 2.53/1.02  
% 2.53/1.02  fof(f54,plain,(
% 2.53/1.02    ( ! [X2,X0,X3,X1] : (r2_orders_2(X0,X1,X3) | ~r2_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f25])).
% 2.53/1.02  
% 2.53/1.02  fof(f67,plain,(
% 2.53/1.02    k1_funct_1(sK3,u1_struct_0(sK1)) = sK2),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  fof(f5,axiom,(
% 2.53/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f12,plain,(
% 2.53/1.02    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.53/1.02    inference(pure_predicate_removal,[],[f5])).
% 2.53/1.02  
% 2.53/1.02  fof(f20,plain,(
% 2.53/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 2.53/1.02    inference(ennf_transformation,[],[f12])).
% 2.53/1.02  
% 2.53/1.02  fof(f21,plain,(
% 2.53/1.02    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 2.53/1.02    inference(flattening,[],[f20])).
% 2.53/1.02  
% 2.53/1.02  fof(f50,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f21])).
% 2.53/1.02  
% 2.53/1.02  fof(f3,axiom,(
% 2.53/1.02    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))))))),
% 2.53/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.53/1.02  
% 2.53/1.02  fof(f17,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : ((r2_orders_2(X0,X1,X2) <=> (X1 != X2 & r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.53/1.02    inference(ennf_transformation,[],[f3])).
% 2.53/1.02  
% 2.53/1.02  fof(f34,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | (X1 = X2 | ~r1_orders_2(X0,X1,X2))) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.53/1.02    inference(nnf_transformation,[],[f17])).
% 2.53/1.02  
% 2.53/1.02  fof(f35,plain,(
% 2.53/1.02    ! [X0] : (! [X1] : (! [X2] : (((r2_orders_2(X0,X1,X2) | X1 = X2 | ~r1_orders_2(X0,X1,X2)) & ((X1 != X2 & r1_orders_2(X0,X1,X2)) | ~r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 2.53/1.02    inference(flattening,[],[f34])).
% 2.53/1.02  
% 2.53/1.02  fof(f47,plain,(
% 2.53/1.02    ( ! [X2,X0,X1] : (X1 != X2 | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.53/1.02    inference(cnf_transformation,[],[f35])).
% 2.53/1.02  
% 2.53/1.02  fof(f69,plain,(
% 2.53/1.02    ( ! [X2,X0] : (~r2_orders_2(X0,X2,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 2.53/1.02    inference(equality_resolution,[],[f47])).
% 2.53/1.02  
% 2.53/1.02  fof(f68,plain,(
% 2.53/1.02    k1_xboole_0 != k3_orders_2(sK1,sK4,sK2)),
% 2.53/1.02    inference(cnf_transformation,[],[f43])).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1,plain,
% 2.53/1.02      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.53/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1047,plain,
% 2.53/1.02      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_12,plain,
% 2.53/1.02      ( r2_hidden(X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.53/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.02      | v2_struct_0(X2)
% 2.53/1.02      | ~ v3_orders_2(X2)
% 2.53/1.02      | ~ v4_orders_2(X2)
% 2.53/1.02      | ~ v5_orders_2(X2)
% 2.53/1.02      | ~ l1_orders_2(X2) ),
% 2.53/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_23,negated_conjecture,
% 2.53/1.02      ( v3_orders_2(sK1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_404,plain,
% 2.53/1.02      ( r2_hidden(X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(X2,X1,X3))
% 2.53/1.02      | ~ m1_subset_1(X3,u1_struct_0(X2))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(X2))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.53/1.02      | v2_struct_0(X2)
% 2.53/1.02      | ~ v4_orders_2(X2)
% 2.53/1.02      | ~ v5_orders_2(X2)
% 2.53/1.02      | ~ l1_orders_2(X2)
% 2.53/1.02      | sK1 != X2 ),
% 2.53/1.02      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_405,plain,
% 2.53/1.02      ( r2_hidden(X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.02      | v2_struct_0(sK1)
% 2.53/1.02      | ~ v4_orders_2(sK1)
% 2.53/1.02      | ~ v5_orders_2(sK1)
% 2.53/1.02      | ~ l1_orders_2(sK1) ),
% 2.53/1.02      inference(unflattening,[status(thm)],[c_404]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_24,negated_conjecture,
% 2.53/1.02      ( ~ v2_struct_0(sK1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_22,negated_conjecture,
% 2.53/1.02      ( v4_orders_2(sK1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_21,negated_conjecture,
% 2.53/1.02      ( v5_orders_2(sK1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_20,negated_conjecture,
% 2.53/1.02      ( l1_orders_2(sK1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_409,plain,
% 2.53/1.02      ( r2_hidden(X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.02      inference(global_propositional_subsumption,
% 2.53/1.02                [status(thm)],
% 2.53/1.02                [c_405,c_24,c_22,c_21,c_20]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_410,plain,
% 2.53/1.02      ( r2_hidden(X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X1,X2))
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.02      inference(renaming,[status(thm)],[c_409]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1041,plain,
% 2.53/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.53/1.02      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_411,plain,
% 2.53/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.53/1.02      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_5,plain,
% 2.53/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.02      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.02      | v2_struct_0(X1)
% 2.53/1.02      | ~ v3_orders_2(X1)
% 2.53/1.02      | ~ v4_orders_2(X1)
% 2.53/1.02      | ~ v5_orders_2(X1)
% 2.53/1.02      | ~ l1_orders_2(X1) ),
% 2.53/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_383,plain,
% 2.53/1.02      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.02      | m1_subset_1(k3_orders_2(X1,X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.02      | v2_struct_0(X1)
% 2.53/1.02      | ~ v4_orders_2(X1)
% 2.53/1.02      | ~ v5_orders_2(X1)
% 2.53/1.02      | ~ l1_orders_2(X1)
% 2.53/1.02      | sK1 != X1 ),
% 2.53/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_23]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_384,plain,
% 2.53/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.02      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.02      | v2_struct_0(sK1)
% 2.53/1.02      | ~ v4_orders_2(sK1)
% 2.53/1.02      | ~ v5_orders_2(sK1)
% 2.53/1.02      | ~ l1_orders_2(sK1) ),
% 2.53/1.02      inference(unflattening,[status(thm)],[c_383]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_388,plain,
% 2.53/1.02      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.02      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.02      inference(global_propositional_subsumption,
% 2.53/1.02                [status(thm)],
% 2.53/1.02                [c_384,c_24,c_22,c_21,c_20]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1042,plain,
% 2.53/1.02      ( m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.02      | m1_subset_1(k3_orders_2(sK1,X1,X0),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_0,plain,
% 2.53/1.02      ( ~ r2_hidden(X0,X1)
% 2.53/1.02      | m1_subset_1(X0,X2)
% 2.53/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.53/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1048,plain,
% 2.53/1.02      ( r2_hidden(X0,X1) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,X2) = iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1528,plain,
% 2.53/1.02      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.53/1.02      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(superposition,[status(thm)],[c_1042,c_1048]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1923,plain,
% 2.53/1.02      ( r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.53/1.02      | r2_hidden(X0,X1) = iProver_top
% 2.53/1.02      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(global_propositional_subsumption,
% 2.53/1.02                [status(thm)],
% 2.53/1.02                [c_1041,c_411,c_1528]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1924,plain,
% 2.53/1.02      ( r2_hidden(X0,X1) = iProver_top
% 2.53/1.02      | r2_hidden(X0,k3_orders_2(sK1,X1,X2)) != iProver_top
% 2.53/1.02      | m1_subset_1(X2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(renaming,[status(thm)],[c_1923]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1931,plain,
% 2.53/1.02      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.53/1.02      | r2_hidden(sK0(k3_orders_2(sK1,X0,X1)),X0) = iProver_top
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(superposition,[status(thm)],[c_1047,c_1924]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_13,plain,
% 2.53/1.02      ( r2_orders_2(X0,X1,X2)
% 2.53/1.02      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.02      | v2_struct_0(X0)
% 2.53/1.02      | ~ v3_orders_2(X0)
% 2.53/1.02      | ~ v4_orders_2(X0)
% 2.53/1.02      | ~ v5_orders_2(X0)
% 2.53/1.02      | ~ l1_orders_2(X0) ),
% 2.53/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_326,plain,
% 2.53/1.02      ( r2_orders_2(X0,X1,X2)
% 2.53/1.02      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
% 2.53/1.02      | v2_struct_0(X0)
% 2.53/1.02      | ~ v4_orders_2(X0)
% 2.53/1.02      | ~ v5_orders_2(X0)
% 2.53/1.02      | ~ l1_orders_2(X0)
% 2.53/1.02      | sK1 != X0 ),
% 2.53/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_327,plain,
% 2.53/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.02      | v2_struct_0(sK1)
% 2.53/1.02      | ~ v4_orders_2(sK1)
% 2.53/1.02      | ~ v5_orders_2(sK1)
% 2.53/1.02      | ~ l1_orders_2(sK1) ),
% 2.53/1.02      inference(unflattening,[status(thm)],[c_326]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_331,plain,
% 2.53/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.02      inference(global_propositional_subsumption,
% 2.53/1.02                [status(thm)],
% 2.53/1.02                [c_327,c_24,c_22,c_21,c_20]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_332,plain,
% 2.53/1.02      ( r2_orders_2(sK1,X0,X1)
% 2.53/1.02      | ~ r2_hidden(X0,k3_orders_2(sK1,X2,X1))
% 2.53/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.02      inference(renaming,[status(thm)],[c_331]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1044,plain,
% 2.53/1.02      ( r2_orders_2(sK1,X0,X1) = iProver_top
% 2.53/1.02      | r2_hidden(X0,k3_orders_2(sK1,X2,X1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1941,plain,
% 2.53/1.02      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.53/1.02      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.02      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.02      inference(superposition,[status(thm)],[c_1047,c_1044]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_2094,plain,
% 2.53/1.02      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.02      | m1_subset_1(sK0(k3_orders_2(sK1,X0,X1)),u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.02      inference(superposition,[status(thm)],[c_1047,c_1528]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_2480,plain,
% 2.53/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.53/1.02      | k3_orders_2(sK1,X0,X1) = k1_xboole_0 ),
% 2.53/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1941,c_2094]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_2481,plain,
% 2.53/1.02      ( k3_orders_2(sK1,X0,X1) = k1_xboole_0
% 2.53/1.02      | r2_orders_2(sK1,sK0(k3_orders_2(sK1,X0,X1)),X1) = iProver_top
% 2.53/1.02      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.02      inference(renaming,[status(thm)],[c_2480]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_19,negated_conjecture,
% 2.53/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.53/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_1046,plain,
% 2.53/1.02      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.02      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_8,plain,
% 2.53/1.02      ( ~ r3_orders_2(X0,X1,X2)
% 2.53/1.02      | r1_orders_2(X0,X1,X2)
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.02      | v2_struct_0(X0)
% 2.53/1.02      | ~ v3_orders_2(X0)
% 2.53/1.02      | ~ l1_orders_2(X0) ),
% 2.53/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.53/1.02  
% 2.53/1.02  cnf(c_14,plain,
% 2.53/1.02      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.53/1.02      | ~ m2_orders_2(X3,X0,X1)
% 2.53/1.02      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.53/1.02      | ~ r2_hidden(X2,X3)
% 2.53/1.02      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.02      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.53/1.02      | v2_struct_0(X0)
% 2.53/1.02      | ~ v3_orders_2(X0)
% 2.53/1.02      | ~ v4_orders_2(X0)
% 2.53/1.02      | ~ v5_orders_2(X0)
% 2.53/1.03      | ~ l1_orders_2(X0) ),
% 2.53/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_17,negated_conjecture,
% 2.53/1.03      ( m2_orders_2(sK4,sK1,sK3) ),
% 2.53/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_265,plain,
% 2.53/1.03      ( r3_orders_2(X0,k1_funct_1(X1,u1_struct_0(X0)),X2)
% 2.53/1.03      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
% 2.53/1.03      | ~ r2_hidden(X2,X3)
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(X1,u1_struct_0(X0)),u1_struct_0(X0))
% 2.53/1.03      | v2_struct_0(X0)
% 2.53/1.03      | ~ v3_orders_2(X0)
% 2.53/1.03      | ~ v4_orders_2(X0)
% 2.53/1.03      | ~ v5_orders_2(X0)
% 2.53/1.03      | ~ l1_orders_2(X0)
% 2.53/1.03      | sK3 != X1
% 2.53/1.03      | sK4 != X3
% 2.53/1.03      | sK1 != X0 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_17]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_266,plain,
% 2.53/1.03      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.53/1.03      | ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | v2_struct_0(sK1)
% 2.53/1.03      | ~ v3_orders_2(sK1)
% 2.53/1.03      | ~ v4_orders_2(sK1)
% 2.53/1.03      | ~ v5_orders_2(sK1)
% 2.53/1.03      | ~ l1_orders_2(sK1) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_265]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_18,negated_conjecture,
% 2.53/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) ),
% 2.53/1.03      inference(cnf_transformation,[],[f65]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_270,plain,
% 2.53/1.03      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_266,c_24,c_23,c_22,c_21,c_20,c_18]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_271,plain,
% 2.53/1.03      ( r3_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.53/1.03      inference(renaming,[status(thm)],[c_270]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_297,plain,
% 2.53/1.03      ( r1_orders_2(X0,X1,X2)
% 2.53/1.03      | ~ r2_hidden(X3,sK4)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | v2_struct_0(X0)
% 2.53/1.03      | ~ v3_orders_2(X0)
% 2.53/1.03      | ~ l1_orders_2(X0)
% 2.53/1.03      | X3 != X2
% 2.53/1.03      | k1_funct_1(sK3,u1_struct_0(sK1)) != X1
% 2.53/1.03      | sK1 != X0 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_271]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_298,plain,
% 2.53/1.03      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | v2_struct_0(sK1)
% 2.53/1.03      | ~ v3_orders_2(sK1)
% 2.53/1.03      | ~ l1_orders_2(sK1) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_297]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_302,plain,
% 2.53/1.03      ( ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0) ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_298,c_24,c_23,c_20]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_303,plain,
% 2.53/1.03      ( r1_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X0)
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.53/1.03      inference(renaming,[status(thm)],[c_302]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_9,plain,
% 2.53/1.03      ( ~ r1_orders_2(X0,X1,X2)
% 2.53/1.03      | ~ r2_orders_2(X0,X2,X3)
% 2.53/1.03      | r2_orders_2(X0,X1,X3)
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.53/1.03      | ~ v4_orders_2(X0)
% 2.53/1.03      | ~ v5_orders_2(X0)
% 2.53/1.03      | ~ l1_orders_2(X0) ),
% 2.53/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_479,plain,
% 2.53/1.03      ( ~ r1_orders_2(X0,X1,X2)
% 2.53/1.03      | ~ r2_orders_2(X0,X2,X3)
% 2.53/1.03      | r2_orders_2(X0,X1,X3)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(X0))
% 2.53/1.03      | ~ m1_subset_1(X3,u1_struct_0(X0))
% 2.53/1.03      | ~ v4_orders_2(X0)
% 2.53/1.03      | ~ l1_orders_2(X0)
% 2.53/1.03      | sK1 != X0 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_480,plain,
% 2.53/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.53/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.53/1.03      | r2_orders_2(sK1,X0,X2)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ v4_orders_2(sK1)
% 2.53/1.03      | ~ l1_orders_2(sK1) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_479]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_482,plain,
% 2.53/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.53/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.53/1.03      | r2_orders_2(sK1,X0,X2)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_480,c_22,c_20]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_483,plain,
% 2.53/1.03      ( ~ r1_orders_2(sK1,X0,X1)
% 2.53/1.03      | ~ r2_orders_2(sK1,X1,X2)
% 2.53/1.03      | r2_orders_2(sK1,X0,X2)
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1)) ),
% 2.53/1.03      inference(renaming,[status(thm)],[c_482]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_629,plain,
% 2.53/1.03      ( ~ r2_orders_2(sK1,X0,X1)
% 2.53/1.03      | r2_orders_2(sK1,X2,X1)
% 2.53/1.03      | ~ r2_hidden(X3,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X3,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X2,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1))
% 2.53/1.03      | X0 != X3
% 2.53/1.03      | k1_funct_1(sK3,u1_struct_0(sK1)) != X2
% 2.53/1.03      | sK1 != sK1 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_303,c_483]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_630,plain,
% 2.53/1.03      ( ~ r2_orders_2(sK1,X0,X1)
% 2.53/1.03      | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1)
% 2.53/1.03      | ~ r2_hidden(X0,sK4)
% 2.53/1.03      | ~ m1_subset_1(X0,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(sK1))
% 2.53/1.03      | ~ m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_629]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1037,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,k1_funct_1(sK3,u1_struct_0(sK1)),X1) = iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(k1_funct_1(sK3,u1_struct_0(sK1)),u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_16,negated_conjecture,
% 2.53/1.03      ( k1_funct_1(sK3,u1_struct_0(sK1)) = sK2 ),
% 2.53/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1144,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(light_normalisation,[status(thm)],[c_1037,c_16]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1151,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1144,c_1046]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_6,plain,
% 2.53/1.03      ( ~ m2_orders_2(X0,X1,X2)
% 2.53/1.03      | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(X1)))
% 2.53/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.03      | v2_struct_0(X1)
% 2.53/1.03      | ~ v3_orders_2(X1)
% 2.53/1.03      | ~ v4_orders_2(X1)
% 2.53/1.03      | ~ v5_orders_2(X1)
% 2.53/1.03      | ~ l1_orders_2(X1) ),
% 2.53/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_254,plain,
% 2.53/1.03      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(X1)))
% 2.53/1.03      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.53/1.03      | v2_struct_0(X1)
% 2.53/1.03      | ~ v3_orders_2(X1)
% 2.53/1.03      | ~ v4_orders_2(X1)
% 2.53/1.03      | ~ v5_orders_2(X1)
% 2.53/1.03      | ~ l1_orders_2(X1)
% 2.53/1.03      | sK3 != X0
% 2.53/1.03      | sK4 != X2
% 2.53/1.03      | sK1 != X1 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_6,c_17]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_255,plain,
% 2.53/1.03      ( ~ m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1)))
% 2.53/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 2.53/1.03      | v2_struct_0(sK1)
% 2.53/1.03      | ~ v3_orders_2(sK1)
% 2.53/1.03      | ~ v4_orders_2(sK1)
% 2.53/1.03      | ~ v5_orders_2(sK1)
% 2.53/1.03      | ~ l1_orders_2(sK1) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_254]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_257,plain,
% 2.53/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_255,c_24,c_23,c_22,c_21,c_20,c_18]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1045,plain,
% 2.53/1.03      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_257]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1527,plain,
% 2.53/1.03      ( r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.03      inference(superposition,[status(thm)],[c_1045,c_1048]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1630,plain,
% 2.53/1.03      ( r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.53/1.03      | r2_orders_2(sK1,X0,X1) != iProver_top
% 2.53/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1151,c_1527]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1631,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,X1) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,sK2,X1) = iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X1,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(renaming,[status(thm)],[c_1630]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1638,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,sK2) != iProver_top
% 2.53/1.03      | r2_orders_2(sK1,sK2,sK2) = iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 2.53/1.03      inference(superposition,[status(thm)],[c_1046,c_1631]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_30,plain,
% 2.53/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_3,plain,
% 2.53/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.03      | ~ l1_orders_2(X0) ),
% 2.53/1.03      inference(cnf_transformation,[],[f69]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_537,plain,
% 2.53/1.03      ( ~ r2_orders_2(X0,X1,X1)
% 2.53/1.03      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.53/1.03      | sK1 != X0 ),
% 2.53/1.03      inference(resolution_lifted,[status(thm)],[c_3,c_20]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_538,plain,
% 2.53/1.03      ( ~ r2_orders_2(sK1,X0,X0) | ~ m1_subset_1(X0,u1_struct_0(sK1)) ),
% 2.53/1.03      inference(unflattening,[status(thm)],[c_537]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1190,plain,
% 2.53/1.03      ( ~ r2_orders_2(sK1,sK2,sK2) | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 2.53/1.03      inference(instantiation,[status(thm)],[c_538]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1191,plain,
% 2.53/1.03      ( r2_orders_2(sK1,sK2,sK2) != iProver_top
% 2.53/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_1190]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_1791,plain,
% 2.53/1.03      ( r2_orders_2(sK1,X0,sK2) != iProver_top
% 2.53/1.03      | r2_hidden(X0,sK4) != iProver_top ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_1638,c_30,c_1191]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_2491,plain,
% 2.53/1.03      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.53/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top ),
% 2.53/1.03      inference(superposition,[status(thm)],[c_2481,c_1791]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_2519,plain,
% 2.53/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.53/1.03      | k3_orders_2(sK1,X0,sK2) = k1_xboole_0 ),
% 2.53/1.03      inference(global_propositional_subsumption,[status(thm)],[c_2491,c_30]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_2520,plain,
% 2.53/1.03      ( k3_orders_2(sK1,X0,sK2) = k1_xboole_0
% 2.53/1.03      | r2_hidden(sK0(k3_orders_2(sK1,X0,sK2)),sK4) != iProver_top
% 2.53/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.03      inference(renaming,[status(thm)],[c_2519]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_2528,plain,
% 2.53/1.03      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0
% 2.53/1.03      | m1_subset_1(sK2,u1_struct_0(sK1)) != iProver_top
% 2.53/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top ),
% 2.53/1.03      inference(superposition,[status(thm)],[c_1931,c_2520]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_25,plain,
% 2.53/1.03      ( v2_struct_0(sK1) != iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_26,plain,
% 2.53/1.03      ( v3_orders_2(sK1) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_27,plain,
% 2.53/1.03      ( v4_orders_2(sK1) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_28,plain,
% 2.53/1.03      ( v5_orders_2(sK1) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_29,plain,
% 2.53/1.03      ( l1_orders_2(sK1) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_31,plain,
% 2.53/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) = iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_256,plain,
% 2.53/1.03      ( m1_orders_1(sK3,k1_orders_1(u1_struct_0(sK1))) != iProver_top
% 2.53/1.03      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top
% 2.53/1.03      | v2_struct_0(sK1) = iProver_top
% 2.53/1.03      | v3_orders_2(sK1) != iProver_top
% 2.53/1.03      | v4_orders_2(sK1) != iProver_top
% 2.53/1.03      | v5_orders_2(sK1) != iProver_top
% 2.53/1.03      | l1_orders_2(sK1) != iProver_top ),
% 2.53/1.03      inference(predicate_to_equality,[status(thm)],[c_255]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_3444,plain,
% 2.53/1.03      ( k3_orders_2(sK1,sK4,sK2) = k1_xboole_0 ),
% 2.53/1.03      inference(global_propositional_subsumption,
% 2.53/1.03                [status(thm)],
% 2.53/1.03                [c_2528,c_25,c_26,c_27,c_28,c_29,c_30,c_31,c_256]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_15,negated_conjecture,
% 2.53/1.03      ( k1_xboole_0 != k3_orders_2(sK1,sK4,sK2) ),
% 2.53/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_3447,plain,
% 2.53/1.03      ( k1_xboole_0 != k1_xboole_0 ),
% 2.53/1.03      inference(demodulation,[status(thm)],[c_3444,c_15]) ).
% 2.53/1.03  
% 2.53/1.03  cnf(c_3537,plain,
% 2.53/1.03      ( $false ),
% 2.53/1.03      inference(equality_resolution_simp,[status(thm)],[c_3447]) ).
% 2.53/1.03  
% 2.53/1.03  
% 2.53/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.53/1.03  
% 2.53/1.03  ------                               Statistics
% 2.53/1.03  
% 2.53/1.03  ------ General
% 2.53/1.03  
% 2.53/1.03  abstr_ref_over_cycles:                  0
% 2.53/1.03  abstr_ref_under_cycles:                 0
% 2.53/1.03  gc_basic_clause_elim:                   0
% 2.53/1.03  forced_gc_time:                         0
% 2.53/1.03  parsing_time:                           0.012
% 2.53/1.03  unif_index_cands_time:                  0.
% 2.53/1.03  unif_index_add_time:                    0.
% 2.53/1.03  orderings_time:                         0.
% 2.53/1.03  out_proof_time:                         0.013
% 2.53/1.03  total_time:                             0.164
% 2.53/1.03  num_of_symbols:                         54
% 2.53/1.03  num_of_terms:                           2772
% 2.53/1.03  
% 2.53/1.03  ------ Preprocessing
% 2.53/1.03  
% 2.53/1.03  num_of_splits:                          0
% 2.53/1.03  num_of_split_atoms:                     0
% 2.53/1.03  num_of_reused_defs:                     0
% 2.53/1.03  num_eq_ax_congr_red:                    11
% 2.53/1.03  num_of_sem_filtered_clauses:            1
% 2.53/1.03  num_of_subtypes:                        0
% 2.53/1.03  monotx_restored_types:                  0
% 2.53/1.03  sat_num_of_epr_types:                   0
% 2.53/1.03  sat_num_of_non_cyclic_types:            0
% 2.53/1.03  sat_guarded_non_collapsed_types:        0
% 2.53/1.03  num_pure_diseq_elim:                    0
% 2.53/1.03  simp_replaced_by:                       0
% 2.53/1.03  res_preprocessed:                       89
% 2.53/1.03  prep_upred:                             0
% 2.53/1.03  prep_unflattend:                        24
% 2.53/1.03  smt_new_axioms:                         0
% 2.53/1.03  pred_elim_cands:                        3
% 2.53/1.03  pred_elim:                              9
% 2.53/1.03  pred_elim_cl:                           10
% 2.53/1.03  pred_elim_cycles:                       11
% 2.53/1.03  merged_defs:                            0
% 2.53/1.03  merged_defs_ncl:                        0
% 2.53/1.03  bin_hyper_res:                          0
% 2.53/1.03  prep_cycles:                            4
% 2.53/1.03  pred_elim_time:                         0.011
% 2.53/1.03  splitting_time:                         0.
% 2.53/1.03  sem_filter_time:                        0.
% 2.53/1.03  monotx_time:                            0.001
% 2.53/1.03  subtype_inf_time:                       0.
% 2.53/1.03  
% 2.53/1.03  ------ Problem properties
% 2.53/1.03  
% 2.53/1.03  clauses:                                15
% 2.53/1.03  conjectures:                            3
% 2.53/1.03  epr:                                    0
% 2.53/1.03  horn:                                   13
% 2.53/1.03  ground:                                 4
% 2.53/1.03  unary:                                  4
% 2.53/1.03  binary:                                 2
% 2.53/1.03  lits:                                   52
% 2.53/1.03  lits_eq:                                4
% 2.53/1.03  fd_pure:                                0
% 2.53/1.03  fd_pseudo:                              0
% 2.53/1.03  fd_cond:                                2
% 2.53/1.03  fd_pseudo_cond:                         0
% 2.53/1.03  ac_symbols:                             0
% 2.53/1.03  
% 2.53/1.03  ------ Propositional Solver
% 2.53/1.03  
% 2.53/1.03  prop_solver_calls:                      28
% 2.53/1.03  prop_fast_solver_calls:                 997
% 2.53/1.03  smt_solver_calls:                       0
% 2.53/1.03  smt_fast_solver_calls:                  0
% 2.53/1.03  prop_num_of_clauses:                    1346
% 2.53/1.03  prop_preprocess_simplified:             3627
% 2.53/1.03  prop_fo_subsumed:                       43
% 2.53/1.03  prop_solver_time:                       0.
% 2.53/1.03  smt_solver_time:                        0.
% 2.53/1.03  smt_fast_solver_time:                   0.
% 2.53/1.03  prop_fast_solver_time:                  0.
% 2.53/1.03  prop_unsat_core_time:                   0.
% 2.53/1.03  
% 2.53/1.03  ------ QBF
% 2.53/1.03  
% 2.53/1.03  qbf_q_res:                              0
% 2.53/1.03  qbf_num_tautologies:                    0
% 2.53/1.03  qbf_prep_cycles:                        0
% 2.53/1.03  
% 2.53/1.03  ------ BMC1
% 2.53/1.03  
% 2.53/1.03  bmc1_current_bound:                     -1
% 2.53/1.03  bmc1_last_solved_bound:                 -1
% 2.53/1.03  bmc1_unsat_core_size:                   -1
% 2.53/1.03  bmc1_unsat_core_parents_size:           -1
% 2.53/1.03  bmc1_merge_next_fun:                    0
% 2.53/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.53/1.03  
% 2.53/1.03  ------ Instantiation
% 2.53/1.03  
% 2.53/1.03  inst_num_of_clauses:                    402
% 2.53/1.03  inst_num_in_passive:                    68
% 2.53/1.03  inst_num_in_active:                     167
% 2.53/1.03  inst_num_in_unprocessed:                167
% 2.53/1.03  inst_num_of_loops:                      180
% 2.53/1.03  inst_num_of_learning_restarts:          0
% 2.53/1.03  inst_num_moves_active_passive:          10
% 2.53/1.03  inst_lit_activity:                      0
% 2.53/1.03  inst_lit_activity_moves:                0
% 2.53/1.03  inst_num_tautologies:                   0
% 2.53/1.03  inst_num_prop_implied:                  0
% 2.53/1.03  inst_num_existing_simplified:           0
% 2.53/1.03  inst_num_eq_res_simplified:             0
% 2.53/1.03  inst_num_child_elim:                    0
% 2.53/1.03  inst_num_of_dismatching_blockings:      10
% 2.53/1.03  inst_num_of_non_proper_insts:           239
% 2.53/1.03  inst_num_of_duplicates:                 0
% 2.53/1.03  inst_inst_num_from_inst_to_res:         0
% 2.53/1.03  inst_dismatching_checking_time:         0.
% 2.53/1.03  
% 2.53/1.03  ------ Resolution
% 2.53/1.03  
% 2.53/1.03  res_num_of_clauses:                     0
% 2.53/1.03  res_num_in_passive:                     0
% 2.53/1.03  res_num_in_active:                      0
% 2.53/1.03  res_num_of_loops:                       93
% 2.53/1.03  res_forward_subset_subsumed:            20
% 2.53/1.03  res_backward_subset_subsumed:           0
% 2.53/1.03  res_forward_subsumed:                   1
% 2.53/1.03  res_backward_subsumed:                  0
% 2.53/1.03  res_forward_subsumption_resolution:     1
% 2.53/1.03  res_backward_subsumption_resolution:    0
% 2.53/1.03  res_clause_to_clause_subsumption:       445
% 2.53/1.03  res_orphan_elimination:                 0
% 2.53/1.03  res_tautology_del:                      16
% 2.53/1.03  res_num_eq_res_simplified:              0
% 2.53/1.03  res_num_sel_changes:                    0
% 2.53/1.03  res_moves_from_active_to_pass:          0
% 2.53/1.03  
% 2.53/1.03  ------ Superposition
% 2.53/1.03  
% 2.53/1.03  sup_time_total:                         0.
% 2.53/1.03  sup_time_generating:                    0.
% 2.53/1.03  sup_time_sim_full:                      0.
% 2.53/1.03  sup_time_sim_immed:                     0.
% 2.53/1.03  
% 2.53/1.03  sup_num_of_clauses:                     59
% 2.53/1.03  sup_num_in_active:                      34
% 2.53/1.03  sup_num_in_passive:                     25
% 2.53/1.03  sup_num_of_loops:                       35
% 2.53/1.03  sup_fw_superposition:                   24
% 2.53/1.03  sup_bw_superposition:                   43
% 2.53/1.03  sup_immediate_simplified:               22
% 2.53/1.03  sup_given_eliminated:                   0
% 2.53/1.03  comparisons_done:                       0
% 2.53/1.03  comparisons_avoided:                    3
% 2.53/1.03  
% 2.53/1.03  ------ Simplifications
% 2.53/1.03  
% 2.53/1.03  
% 2.53/1.03  sim_fw_subset_subsumed:                 12
% 2.53/1.03  sim_bw_subset_subsumed:                 0
% 2.53/1.03  sim_fw_subsumed:                        3
% 2.53/1.03  sim_bw_subsumed:                        0
% 2.53/1.03  sim_fw_subsumption_res:                 11
% 2.53/1.03  sim_bw_subsumption_res:                 0
% 2.53/1.03  sim_tautology_del:                      3
% 2.53/1.03  sim_eq_tautology_del:                   1
% 2.53/1.03  sim_eq_res_simp:                        0
% 2.53/1.03  sim_fw_demodulated:                     1
% 2.53/1.03  sim_bw_demodulated:                     1
% 2.53/1.03  sim_light_normalised:                   5
% 2.53/1.03  sim_joinable_taut:                      0
% 2.53/1.03  sim_joinable_simp:                      0
% 2.53/1.03  sim_ac_normalised:                      0
% 2.53/1.03  sim_smt_subsumption:                    0
% 2.53/1.03  
%------------------------------------------------------------------------------
