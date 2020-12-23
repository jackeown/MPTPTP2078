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
% DateTime   : Thu Dec  3 12:21:48 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 413 expanded)
%              Number of clauses        :   64 (  85 expanded)
%              Number of leaves         :   16 ( 131 expanded)
%              Depth                    :   18
%              Number of atoms          :  722 (4032 expanded)
%              Number of equality atoms :  100 ( 704 expanded)
%              Maximal formula depth    :   16 (   7 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( X3 != X4
              | ~ m1_subset_1(X4,u1_struct_0(X2)) )
          & ! [X5] :
              ( X3 != X5
              | ~ m1_subset_1(X5,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
     => ( ! [X4] :
            ( sK4 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) )
        & ! [X5] :
            ( sK4 != X5
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ! [X4] :
                  ( X3 != X4
                  | ~ m1_subset_1(X4,u1_struct_0(X2)) )
              & ! [X5] :
                  ( X3 != X5
                  | ~ m1_subset_1(X5,u1_struct_0(X1)) )
              & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ! [X4] :
                ( X3 != X4
                | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
            & ! [X5] :
                ( X3 != X5
                | ~ m1_subset_1(X5,u1_struct_0(X1)) )
            & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3))) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ! [X4] :
                    ( X3 != X4
                    | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                & ! [X5] :
                    ( X3 != X5
                    | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
                & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2))) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ! [X4] :
                        ( X3 != X4
                        | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                    & ! [X5] :
                        ( X3 != X5
                        | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2))) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ! [X4] :
        ( sK4 != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK3)) )
    & ! [X5] :
        ( sK4 != X5
        | ~ m1_subset_1(X5,u1_struct_0(sK2)) )
    & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f40,f39,f38,f37])).

fof(f69,plain,(
    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f66,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3) )
                    & ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f65,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
            & ~ r2_hidden(sK0(X0,X1,X2),X0) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( r2_hidden(sK0(X0,X1,X2),X1)
          | r2_hidden(sK0(X0,X1,X2),X0)
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK0(X0,X1,X2),X1)
              & ~ r2_hidden(sK0(X0,X1,X2),X0) )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( r2_hidden(sK0(X0,X1,X2),X1)
            | r2_hidden(sK0(X0,X1,X2),X0)
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f74,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_2(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,k1_connsp_2(X0,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X4] :
      ( sK4 != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK3)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(equality_resolution,[],[f71])).

fof(f70,plain,(
    ! [X5] :
      ( sK4 != X5
      | ~ m1_subset_1(X5,u1_struct_0(sK2)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f77,plain,(
    ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f70])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_5558,plain,
    ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ r2_hidden(X0,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_7826,plain,
    ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
    | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_5558])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_988,plain,
    ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1000,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2305,plain,
    ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_1000])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_987,plain,
    ( m1_pre_topc(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_985,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_179,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_13,c_16,c_15,c_14])).

cnf(c_180,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_179])).

cnf(c_978,plain,
    ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_180])).

cnf(c_1485,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_985,c_978])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1731,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1485,c_30,c_32,c_33])).

cnf(c_1732,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
    | m1_pre_topc(X0,sK1) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1731])).

cnf(c_1737,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_987,c_1732])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1130,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_180])).

cnf(c_1429,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1)
    | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1130])).

cnf(c_1742,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1737,c_29,c_27,c_26,c_25,c_24,c_23,c_1429])).

cnf(c_5,plain,
    ( r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1002,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3229,plain,
    ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1742,c_1002])).

cnf(c_4468,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_3229])).

cnf(c_4469,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4468])).

cnf(c_9,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2262,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
    | ~ l1_pre_topc(X0)
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2264,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
    | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_2262])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1847,plain,
    ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
    | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(X1))
    | r2_hidden(X0,k1_connsp_2(X1,X0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1681,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
    | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
    | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1194,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X1,sK1)
    | m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1375,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | m1_pre_topc(k1_tsep_1(sK1,sK2,X0),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1194])).

cnf(c_1611,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1375])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1193,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(X1,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_pre_topc(k1_tsep_1(sK1,X0,X1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1362,plain,
    ( ~ m1_pre_topc(X0,sK1)
    | ~ m1_pre_topc(sK2,sK1)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_pre_topc(k1_tsep_1(sK1,sK2,X0))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_1599,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_19,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_165,plain,
    ( ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_19,c_16])).

cnf(c_166,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_165])).

cnf(c_1131,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(sK2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,sK2,X0))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_166])).

cnf(c_1409,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ m1_pre_topc(sK3,sK1)
    | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1054,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1046,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_20,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_21,negated_conjecture,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7826,c_4469,c_2264,c_1847,c_1681,c_1611,c_1599,c_1409,c_1054,c_1046,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:12:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.77/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/0.97  
% 2.77/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.77/0.97  
% 2.77/0.97  ------  iProver source info
% 2.77/0.97  
% 2.77/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.77/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.77/0.97  git: non_committed_changes: false
% 2.77/0.97  git: last_make_outside_of_git: false
% 2.77/0.97  
% 2.77/0.97  ------ 
% 2.77/0.97  
% 2.77/0.97  ------ Input Options
% 2.77/0.97  
% 2.77/0.97  --out_options                           all
% 2.77/0.97  --tptp_safe_out                         true
% 2.77/0.97  --problem_path                          ""
% 2.77/0.97  --include_path                          ""
% 2.77/0.97  --clausifier                            res/vclausify_rel
% 2.77/0.97  --clausifier_options                    ""
% 2.77/0.97  --stdin                                 false
% 2.77/0.97  --stats_out                             all
% 2.77/0.97  
% 2.77/0.97  ------ General Options
% 2.77/0.97  
% 2.77/0.97  --fof                                   false
% 2.77/0.97  --time_out_real                         305.
% 2.77/0.97  --time_out_virtual                      -1.
% 2.77/0.97  --symbol_type_check                     false
% 2.77/0.97  --clausify_out                          false
% 2.77/0.97  --sig_cnt_out                           false
% 2.77/0.97  --trig_cnt_out                          false
% 2.77/0.97  --trig_cnt_out_tolerance                1.
% 2.77/0.97  --trig_cnt_out_sk_spl                   false
% 2.77/0.97  --abstr_cl_out                          false
% 2.77/0.97  
% 2.77/0.97  ------ Global Options
% 2.77/0.97  
% 2.77/0.97  --schedule                              default
% 2.77/0.97  --add_important_lit                     false
% 2.77/0.97  --prop_solver_per_cl                    1000
% 2.77/0.97  --min_unsat_core                        false
% 2.77/0.97  --soft_assumptions                      false
% 2.77/0.97  --soft_lemma_size                       3
% 2.77/0.97  --prop_impl_unit_size                   0
% 2.77/0.97  --prop_impl_unit                        []
% 2.77/0.97  --share_sel_clauses                     true
% 2.77/0.97  --reset_solvers                         false
% 2.77/0.97  --bc_imp_inh                            [conj_cone]
% 2.77/0.97  --conj_cone_tolerance                   3.
% 2.77/0.97  --extra_neg_conj                        none
% 2.77/0.97  --large_theory_mode                     true
% 2.77/0.97  --prolific_symb_bound                   200
% 2.77/0.97  --lt_threshold                          2000
% 2.77/0.97  --clause_weak_htbl                      true
% 2.77/0.97  --gc_record_bc_elim                     false
% 2.77/0.97  
% 2.77/0.97  ------ Preprocessing Options
% 2.77/0.97  
% 2.77/0.97  --preprocessing_flag                    true
% 2.77/0.97  --time_out_prep_mult                    0.1
% 2.77/0.97  --splitting_mode                        input
% 2.77/0.97  --splitting_grd                         true
% 2.77/0.97  --splitting_cvd                         false
% 2.77/0.97  --splitting_cvd_svl                     false
% 2.77/0.97  --splitting_nvd                         32
% 2.77/0.97  --sub_typing                            true
% 2.77/0.97  --prep_gs_sim                           true
% 2.77/0.97  --prep_unflatten                        true
% 2.77/0.97  --prep_res_sim                          true
% 2.77/0.97  --prep_upred                            true
% 2.77/0.97  --prep_sem_filter                       exhaustive
% 2.77/0.97  --prep_sem_filter_out                   false
% 2.77/0.97  --pred_elim                             true
% 2.77/0.97  --res_sim_input                         true
% 2.77/0.97  --eq_ax_congr_red                       true
% 2.77/0.97  --pure_diseq_elim                       true
% 2.77/0.97  --brand_transform                       false
% 2.77/0.97  --non_eq_to_eq                          false
% 2.77/0.97  --prep_def_merge                        true
% 2.77/0.97  --prep_def_merge_prop_impl              false
% 2.77/0.97  --prep_def_merge_mbd                    true
% 2.77/0.97  --prep_def_merge_tr_red                 false
% 2.77/0.97  --prep_def_merge_tr_cl                  false
% 2.77/0.97  --smt_preprocessing                     true
% 2.77/0.97  --smt_ac_axioms                         fast
% 2.77/0.97  --preprocessed_out                      false
% 2.77/0.97  --preprocessed_stats                    false
% 2.77/0.97  
% 2.77/0.97  ------ Abstraction refinement Options
% 2.77/0.97  
% 2.77/0.97  --abstr_ref                             []
% 2.77/0.97  --abstr_ref_prep                        false
% 2.77/0.97  --abstr_ref_until_sat                   false
% 2.77/0.97  --abstr_ref_sig_restrict                funpre
% 2.77/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.97  --abstr_ref_under                       []
% 2.77/0.97  
% 2.77/0.97  ------ SAT Options
% 2.77/0.97  
% 2.77/0.97  --sat_mode                              false
% 2.77/0.97  --sat_fm_restart_options                ""
% 2.77/0.97  --sat_gr_def                            false
% 2.77/0.97  --sat_epr_types                         true
% 2.77/0.97  --sat_non_cyclic_types                  false
% 2.77/0.97  --sat_finite_models                     false
% 2.77/0.97  --sat_fm_lemmas                         false
% 2.77/0.97  --sat_fm_prep                           false
% 2.77/0.97  --sat_fm_uc_incr                        true
% 2.77/0.97  --sat_out_model                         small
% 2.77/0.97  --sat_out_clauses                       false
% 2.77/0.97  
% 2.77/0.97  ------ QBF Options
% 2.77/0.97  
% 2.77/0.97  --qbf_mode                              false
% 2.77/0.97  --qbf_elim_univ                         false
% 2.77/0.97  --qbf_dom_inst                          none
% 2.77/0.97  --qbf_dom_pre_inst                      false
% 2.77/0.97  --qbf_sk_in                             false
% 2.77/0.97  --qbf_pred_elim                         true
% 2.77/0.97  --qbf_split                             512
% 2.77/0.97  
% 2.77/0.97  ------ BMC1 Options
% 2.77/0.97  
% 2.77/0.97  --bmc1_incremental                      false
% 2.77/0.97  --bmc1_axioms                           reachable_all
% 2.77/0.97  --bmc1_min_bound                        0
% 2.77/0.97  --bmc1_max_bound                        -1
% 2.77/0.97  --bmc1_max_bound_default                -1
% 2.77/0.97  --bmc1_symbol_reachability              true
% 2.77/0.97  --bmc1_property_lemmas                  false
% 2.77/0.97  --bmc1_k_induction                      false
% 2.77/0.97  --bmc1_non_equiv_states                 false
% 2.77/0.97  --bmc1_deadlock                         false
% 2.77/0.97  --bmc1_ucm                              false
% 2.77/0.97  --bmc1_add_unsat_core                   none
% 2.77/0.97  --bmc1_unsat_core_children              false
% 2.77/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.97  --bmc1_out_stat                         full
% 2.77/0.97  --bmc1_ground_init                      false
% 2.77/0.97  --bmc1_pre_inst_next_state              false
% 2.77/0.97  --bmc1_pre_inst_state                   false
% 2.77/0.97  --bmc1_pre_inst_reach_state             false
% 2.77/0.97  --bmc1_out_unsat_core                   false
% 2.77/0.97  --bmc1_aig_witness_out                  false
% 2.77/0.97  --bmc1_verbose                          false
% 2.77/0.97  --bmc1_dump_clauses_tptp                false
% 2.77/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.97  --bmc1_dump_file                        -
% 2.77/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.97  --bmc1_ucm_extend_mode                  1
% 2.77/0.97  --bmc1_ucm_init_mode                    2
% 2.77/0.97  --bmc1_ucm_cone_mode                    none
% 2.77/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.97  --bmc1_ucm_relax_model                  4
% 2.77/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.97  --bmc1_ucm_layered_model                none
% 2.77/0.97  --bmc1_ucm_max_lemma_size               10
% 2.77/0.97  
% 2.77/0.97  ------ AIG Options
% 2.77/0.97  
% 2.77/0.97  --aig_mode                              false
% 2.77/0.97  
% 2.77/0.97  ------ Instantiation Options
% 2.77/0.97  
% 2.77/0.97  --instantiation_flag                    true
% 2.77/0.97  --inst_sos_flag                         true
% 2.77/0.97  --inst_sos_phase                        true
% 2.77/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.97  --inst_lit_sel_side                     num_symb
% 2.77/0.97  --inst_solver_per_active                1400
% 2.77/0.97  --inst_solver_calls_frac                1.
% 2.77/0.97  --inst_passive_queue_type               priority_queues
% 2.77/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.97  --inst_passive_queues_freq              [25;2]
% 2.77/0.97  --inst_dismatching                      true
% 2.77/0.97  --inst_eager_unprocessed_to_passive     true
% 2.77/0.97  --inst_prop_sim_given                   true
% 2.77/0.97  --inst_prop_sim_new                     false
% 2.77/0.97  --inst_subs_new                         false
% 2.77/0.97  --inst_eq_res_simp                      false
% 2.77/0.97  --inst_subs_given                       false
% 2.77/0.97  --inst_orphan_elimination               true
% 2.77/0.97  --inst_learning_loop_flag               true
% 2.77/0.97  --inst_learning_start                   3000
% 2.77/0.97  --inst_learning_factor                  2
% 2.77/0.97  --inst_start_prop_sim_after_learn       3
% 2.77/0.97  --inst_sel_renew                        solver
% 2.77/0.97  --inst_lit_activity_flag                true
% 2.77/0.97  --inst_restr_to_given                   false
% 2.77/0.97  --inst_activity_threshold               500
% 2.77/0.97  --inst_out_proof                        true
% 2.77/0.97  
% 2.77/0.97  ------ Resolution Options
% 2.77/0.97  
% 2.77/0.97  --resolution_flag                       true
% 2.77/0.97  --res_lit_sel                           adaptive
% 2.77/0.97  --res_lit_sel_side                      none
% 2.77/0.97  --res_ordering                          kbo
% 2.77/0.97  --res_to_prop_solver                    active
% 2.77/0.97  --res_prop_simpl_new                    false
% 2.77/0.97  --res_prop_simpl_given                  true
% 2.77/0.97  --res_passive_queue_type                priority_queues
% 2.77/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.97  --res_passive_queues_freq               [15;5]
% 2.77/0.97  --res_forward_subs                      full
% 2.77/0.97  --res_backward_subs                     full
% 2.77/0.97  --res_forward_subs_resolution           true
% 2.77/0.97  --res_backward_subs_resolution          true
% 2.77/0.97  --res_orphan_elimination                true
% 2.77/0.97  --res_time_limit                        2.
% 2.77/0.97  --res_out_proof                         true
% 2.77/0.97  
% 2.77/0.97  ------ Superposition Options
% 2.77/0.97  
% 2.77/0.97  --superposition_flag                    true
% 2.77/0.97  --sup_passive_queue_type                priority_queues
% 2.77/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.97  --demod_completeness_check              fast
% 2.77/0.97  --demod_use_ground                      true
% 2.77/0.97  --sup_to_prop_solver                    passive
% 2.77/0.97  --sup_prop_simpl_new                    true
% 2.77/0.97  --sup_prop_simpl_given                  true
% 2.77/0.97  --sup_fun_splitting                     true
% 2.77/0.97  --sup_smt_interval                      50000
% 2.77/0.97  
% 2.77/0.97  ------ Superposition Simplification Setup
% 2.77/0.97  
% 2.77/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.77/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.77/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.77/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.77/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.77/0.97  --sup_immed_triv                        [TrivRules]
% 2.77/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_immed_bw_main                     []
% 2.77/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.77/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_input_bw                          []
% 2.77/0.97  
% 2.77/0.97  ------ Combination Options
% 2.77/0.97  
% 2.77/0.97  --comb_res_mult                         3
% 2.77/0.97  --comb_sup_mult                         2
% 2.77/0.97  --comb_inst_mult                        10
% 2.77/0.97  
% 2.77/0.97  ------ Debug Options
% 2.77/0.97  
% 2.77/0.97  --dbg_backtrace                         false
% 2.77/0.97  --dbg_dump_prop_clauses                 false
% 2.77/0.97  --dbg_dump_prop_clauses_file            -
% 2.77/0.97  --dbg_out_stat                          false
% 2.77/0.97  ------ Parsing...
% 2.77/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.77/0.97  
% 2.77/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 2.77/0.97  
% 2.77/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.77/0.97  
% 2.77/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.77/0.97  ------ Proving...
% 2.77/0.97  ------ Problem Properties 
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  clauses                                 30
% 2.77/0.97  conjectures                             10
% 2.77/0.97  EPR                                     10
% 2.77/0.97  Horn                                    17
% 2.77/0.97  unary                                   10
% 2.77/0.97  binary                                  3
% 2.77/0.97  lits                                    109
% 2.77/0.97  lits eq                                 6
% 2.77/0.97  fd_pure                                 0
% 2.77/0.97  fd_pseudo                               0
% 2.77/0.97  fd_cond                                 0
% 2.77/0.97  fd_pseudo_cond                          4
% 2.77/0.97  AC symbols                              0
% 2.77/0.97  
% 2.77/0.97  ------ Schedule dynamic 5 is on 
% 2.77/0.97  
% 2.77/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  ------ 
% 2.77/0.97  Current options:
% 2.77/0.97  ------ 
% 2.77/0.97  
% 2.77/0.97  ------ Input Options
% 2.77/0.97  
% 2.77/0.97  --out_options                           all
% 2.77/0.97  --tptp_safe_out                         true
% 2.77/0.97  --problem_path                          ""
% 2.77/0.97  --include_path                          ""
% 2.77/0.97  --clausifier                            res/vclausify_rel
% 2.77/0.97  --clausifier_options                    ""
% 2.77/0.97  --stdin                                 false
% 2.77/0.97  --stats_out                             all
% 2.77/0.97  
% 2.77/0.97  ------ General Options
% 2.77/0.97  
% 2.77/0.97  --fof                                   false
% 2.77/0.97  --time_out_real                         305.
% 2.77/0.97  --time_out_virtual                      -1.
% 2.77/0.97  --symbol_type_check                     false
% 2.77/0.97  --clausify_out                          false
% 2.77/0.97  --sig_cnt_out                           false
% 2.77/0.97  --trig_cnt_out                          false
% 2.77/0.97  --trig_cnt_out_tolerance                1.
% 2.77/0.97  --trig_cnt_out_sk_spl                   false
% 2.77/0.97  --abstr_cl_out                          false
% 2.77/0.97  
% 2.77/0.97  ------ Global Options
% 2.77/0.97  
% 2.77/0.97  --schedule                              default
% 2.77/0.97  --add_important_lit                     false
% 2.77/0.97  --prop_solver_per_cl                    1000
% 2.77/0.97  --min_unsat_core                        false
% 2.77/0.97  --soft_assumptions                      false
% 2.77/0.97  --soft_lemma_size                       3
% 2.77/0.97  --prop_impl_unit_size                   0
% 2.77/0.97  --prop_impl_unit                        []
% 2.77/0.97  --share_sel_clauses                     true
% 2.77/0.97  --reset_solvers                         false
% 2.77/0.97  --bc_imp_inh                            [conj_cone]
% 2.77/0.97  --conj_cone_tolerance                   3.
% 2.77/0.97  --extra_neg_conj                        none
% 2.77/0.97  --large_theory_mode                     true
% 2.77/0.97  --prolific_symb_bound                   200
% 2.77/0.97  --lt_threshold                          2000
% 2.77/0.97  --clause_weak_htbl                      true
% 2.77/0.97  --gc_record_bc_elim                     false
% 2.77/0.97  
% 2.77/0.97  ------ Preprocessing Options
% 2.77/0.97  
% 2.77/0.97  --preprocessing_flag                    true
% 2.77/0.97  --time_out_prep_mult                    0.1
% 2.77/0.97  --splitting_mode                        input
% 2.77/0.97  --splitting_grd                         true
% 2.77/0.97  --splitting_cvd                         false
% 2.77/0.97  --splitting_cvd_svl                     false
% 2.77/0.97  --splitting_nvd                         32
% 2.77/0.97  --sub_typing                            true
% 2.77/0.97  --prep_gs_sim                           true
% 2.77/0.97  --prep_unflatten                        true
% 2.77/0.97  --prep_res_sim                          true
% 2.77/0.97  --prep_upred                            true
% 2.77/0.97  --prep_sem_filter                       exhaustive
% 2.77/0.97  --prep_sem_filter_out                   false
% 2.77/0.97  --pred_elim                             true
% 2.77/0.97  --res_sim_input                         true
% 2.77/0.97  --eq_ax_congr_red                       true
% 2.77/0.97  --pure_diseq_elim                       true
% 2.77/0.97  --brand_transform                       false
% 2.77/0.97  --non_eq_to_eq                          false
% 2.77/0.97  --prep_def_merge                        true
% 2.77/0.97  --prep_def_merge_prop_impl              false
% 2.77/0.97  --prep_def_merge_mbd                    true
% 2.77/0.97  --prep_def_merge_tr_red                 false
% 2.77/0.97  --prep_def_merge_tr_cl                  false
% 2.77/0.97  --smt_preprocessing                     true
% 2.77/0.97  --smt_ac_axioms                         fast
% 2.77/0.97  --preprocessed_out                      false
% 2.77/0.97  --preprocessed_stats                    false
% 2.77/0.97  
% 2.77/0.97  ------ Abstraction refinement Options
% 2.77/0.97  
% 2.77/0.97  --abstr_ref                             []
% 2.77/0.97  --abstr_ref_prep                        false
% 2.77/0.97  --abstr_ref_until_sat                   false
% 2.77/0.97  --abstr_ref_sig_restrict                funpre
% 2.77/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.77/0.97  --abstr_ref_under                       []
% 2.77/0.97  
% 2.77/0.97  ------ SAT Options
% 2.77/0.97  
% 2.77/0.97  --sat_mode                              false
% 2.77/0.97  --sat_fm_restart_options                ""
% 2.77/0.97  --sat_gr_def                            false
% 2.77/0.97  --sat_epr_types                         true
% 2.77/0.97  --sat_non_cyclic_types                  false
% 2.77/0.97  --sat_finite_models                     false
% 2.77/0.97  --sat_fm_lemmas                         false
% 2.77/0.97  --sat_fm_prep                           false
% 2.77/0.97  --sat_fm_uc_incr                        true
% 2.77/0.97  --sat_out_model                         small
% 2.77/0.97  --sat_out_clauses                       false
% 2.77/0.97  
% 2.77/0.97  ------ QBF Options
% 2.77/0.97  
% 2.77/0.97  --qbf_mode                              false
% 2.77/0.97  --qbf_elim_univ                         false
% 2.77/0.97  --qbf_dom_inst                          none
% 2.77/0.97  --qbf_dom_pre_inst                      false
% 2.77/0.97  --qbf_sk_in                             false
% 2.77/0.97  --qbf_pred_elim                         true
% 2.77/0.97  --qbf_split                             512
% 2.77/0.97  
% 2.77/0.97  ------ BMC1 Options
% 2.77/0.97  
% 2.77/0.97  --bmc1_incremental                      false
% 2.77/0.97  --bmc1_axioms                           reachable_all
% 2.77/0.97  --bmc1_min_bound                        0
% 2.77/0.97  --bmc1_max_bound                        -1
% 2.77/0.97  --bmc1_max_bound_default                -1
% 2.77/0.97  --bmc1_symbol_reachability              true
% 2.77/0.97  --bmc1_property_lemmas                  false
% 2.77/0.97  --bmc1_k_induction                      false
% 2.77/0.97  --bmc1_non_equiv_states                 false
% 2.77/0.97  --bmc1_deadlock                         false
% 2.77/0.97  --bmc1_ucm                              false
% 2.77/0.97  --bmc1_add_unsat_core                   none
% 2.77/0.97  --bmc1_unsat_core_children              false
% 2.77/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.77/0.97  --bmc1_out_stat                         full
% 2.77/0.97  --bmc1_ground_init                      false
% 2.77/0.97  --bmc1_pre_inst_next_state              false
% 2.77/0.97  --bmc1_pre_inst_state                   false
% 2.77/0.97  --bmc1_pre_inst_reach_state             false
% 2.77/0.97  --bmc1_out_unsat_core                   false
% 2.77/0.97  --bmc1_aig_witness_out                  false
% 2.77/0.97  --bmc1_verbose                          false
% 2.77/0.97  --bmc1_dump_clauses_tptp                false
% 2.77/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.77/0.97  --bmc1_dump_file                        -
% 2.77/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.77/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.77/0.97  --bmc1_ucm_extend_mode                  1
% 2.77/0.97  --bmc1_ucm_init_mode                    2
% 2.77/0.97  --bmc1_ucm_cone_mode                    none
% 2.77/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.77/0.97  --bmc1_ucm_relax_model                  4
% 2.77/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.77/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.77/0.97  --bmc1_ucm_layered_model                none
% 2.77/0.97  --bmc1_ucm_max_lemma_size               10
% 2.77/0.97  
% 2.77/0.97  ------ AIG Options
% 2.77/0.97  
% 2.77/0.97  --aig_mode                              false
% 2.77/0.97  
% 2.77/0.97  ------ Instantiation Options
% 2.77/0.97  
% 2.77/0.97  --instantiation_flag                    true
% 2.77/0.97  --inst_sos_flag                         true
% 2.77/0.97  --inst_sos_phase                        true
% 2.77/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.77/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.77/0.97  --inst_lit_sel_side                     none
% 2.77/0.97  --inst_solver_per_active                1400
% 2.77/0.97  --inst_solver_calls_frac                1.
% 2.77/0.97  --inst_passive_queue_type               priority_queues
% 2.77/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.77/0.97  --inst_passive_queues_freq              [25;2]
% 2.77/0.97  --inst_dismatching                      true
% 2.77/0.97  --inst_eager_unprocessed_to_passive     true
% 2.77/0.97  --inst_prop_sim_given                   true
% 2.77/0.97  --inst_prop_sim_new                     false
% 2.77/0.97  --inst_subs_new                         false
% 2.77/0.97  --inst_eq_res_simp                      false
% 2.77/0.97  --inst_subs_given                       false
% 2.77/0.97  --inst_orphan_elimination               true
% 2.77/0.97  --inst_learning_loop_flag               true
% 2.77/0.97  --inst_learning_start                   3000
% 2.77/0.97  --inst_learning_factor                  2
% 2.77/0.97  --inst_start_prop_sim_after_learn       3
% 2.77/0.97  --inst_sel_renew                        solver
% 2.77/0.97  --inst_lit_activity_flag                true
% 2.77/0.97  --inst_restr_to_given                   false
% 2.77/0.97  --inst_activity_threshold               500
% 2.77/0.97  --inst_out_proof                        true
% 2.77/0.97  
% 2.77/0.97  ------ Resolution Options
% 2.77/0.97  
% 2.77/0.97  --resolution_flag                       false
% 2.77/0.97  --res_lit_sel                           adaptive
% 2.77/0.97  --res_lit_sel_side                      none
% 2.77/0.97  --res_ordering                          kbo
% 2.77/0.97  --res_to_prop_solver                    active
% 2.77/0.97  --res_prop_simpl_new                    false
% 2.77/0.97  --res_prop_simpl_given                  true
% 2.77/0.97  --res_passive_queue_type                priority_queues
% 2.77/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.77/0.97  --res_passive_queues_freq               [15;5]
% 2.77/0.97  --res_forward_subs                      full
% 2.77/0.97  --res_backward_subs                     full
% 2.77/0.97  --res_forward_subs_resolution           true
% 2.77/0.97  --res_backward_subs_resolution          true
% 2.77/0.97  --res_orphan_elimination                true
% 2.77/0.97  --res_time_limit                        2.
% 2.77/0.97  --res_out_proof                         true
% 2.77/0.97  
% 2.77/0.97  ------ Superposition Options
% 2.77/0.97  
% 2.77/0.97  --superposition_flag                    true
% 2.77/0.97  --sup_passive_queue_type                priority_queues
% 2.77/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.77/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.77/0.97  --demod_completeness_check              fast
% 2.77/0.97  --demod_use_ground                      true
% 2.77/0.97  --sup_to_prop_solver                    passive
% 2.77/0.97  --sup_prop_simpl_new                    true
% 2.77/0.97  --sup_prop_simpl_given                  true
% 2.77/0.97  --sup_fun_splitting                     true
% 2.77/0.97  --sup_smt_interval                      50000
% 2.77/0.97  
% 2.77/0.97  ------ Superposition Simplification Setup
% 2.77/0.97  
% 2.77/0.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.77/0.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.77/0.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.77/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.77/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.77/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.77/0.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.77/0.97  --sup_immed_triv                        [TrivRules]
% 2.77/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_immed_bw_main                     []
% 2.77/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.77/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.77/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.77/0.97  --sup_input_bw                          []
% 2.77/0.97  
% 2.77/0.97  ------ Combination Options
% 2.77/0.97  
% 2.77/0.97  --comb_res_mult                         3
% 2.77/0.97  --comb_sup_mult                         2
% 2.77/0.97  --comb_inst_mult                        10
% 2.77/0.97  
% 2.77/0.97  ------ Debug Options
% 2.77/0.97  
% 2.77/0.97  --dbg_backtrace                         false
% 2.77/0.97  --dbg_dump_prop_clauses                 false
% 2.77/0.97  --dbg_dump_prop_clauses_file            -
% 2.77/0.97  --dbg_out_stat                          false
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  ------ Proving...
% 2.77/0.97  
% 2.77/0.97  
% 2.77/0.97  % SZS status Theorem for theBenchmark.p
% 2.77/0.97  
% 2.77/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.77/0.97  
% 2.77/0.97  fof(f4,axiom,(
% 2.77/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f17,plain,(
% 2.77/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.77/0.97    inference(ennf_transformation,[],[f4])).
% 2.77/0.97  
% 2.77/0.97  fof(f50,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f17])).
% 2.77/0.97  
% 2.77/0.97  fof(f11,conjecture,(
% 2.77/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f12,negated_conjecture,(
% 2.77/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.77/0.97    inference(negated_conjecture,[],[f11])).
% 2.77/0.97  
% 2.77/0.97  fof(f13,plain,(
% 2.77/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 2.77/0.97    inference(rectify,[],[f12])).
% 2.77/0.97  
% 2.77/0.97  fof(f29,plain,(
% 2.77/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f13])).
% 2.77/0.97  
% 2.77/0.97  fof(f30,plain,(
% 2.77/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f29])).
% 2.77/0.97  
% 2.77/0.97  fof(f40,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) => (! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(X0,X1,X2))))) )),
% 2.77/0.97    introduced(choice_axiom,[])).
% 2.77/0.97  
% 2.77/0.97  fof(f39,plain,(
% 2.77/0.97    ( ! [X0,X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,sK3)))) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 2.77/0.97    introduced(choice_axiom,[])).
% 2.77/0.97  
% 2.77/0.97  fof(f38,plain,(
% 2.77/0.97    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,sK2,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 2.77/0.97    introduced(choice_axiom,[])).
% 2.77/0.97  
% 2.77/0.97  fof(f37,plain,(
% 2.77/0.97    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(sK1,X1,X2)))) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 2.77/0.97    introduced(choice_axiom,[])).
% 2.77/0.97  
% 2.77/0.97  fof(f41,plain,(
% 2.77/0.97    (((! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) & ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 2.77/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f30,f40,f39,f38,f37])).
% 2.77/0.97  
% 2.77/0.97  fof(f69,plain,(
% 2.77/0.97    m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f3,axiom,(
% 2.77/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f15,plain,(
% 2.77/0.97    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.77/0.97    inference(ennf_transformation,[],[f3])).
% 2.77/0.97  
% 2.77/0.97  fof(f16,plain,(
% 2.77/0.97    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.77/0.97    inference(flattening,[],[f15])).
% 2.77/0.97  
% 2.77/0.97  fof(f49,plain,(
% 2.77/0.97    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f16])).
% 2.77/0.97  
% 2.77/0.97  fof(f68,plain,(
% 2.77/0.97    m1_pre_topc(sK3,sK1)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f66,plain,(
% 2.77/0.97    m1_pre_topc(sK2,sK1)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f8,axiom,(
% 2.77/0.97    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3))))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f23,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f8])).
% 2.77/0.97  
% 2.77/0.97  fof(f24,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f23])).
% 2.77/0.97  
% 2.77/0.97  fof(f36,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) != u1_struct_0(X3)) & (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(nnf_transformation,[],[f24])).
% 2.77/0.97  
% 2.77/0.97  fof(f54,plain,(
% 2.77/0.97    ( ! [X2,X0,X3,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(X3) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f36])).
% 2.77/0.97  
% 2.77/0.97  fof(f75,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(equality_resolution,[],[f54])).
% 2.77/0.97  
% 2.77/0.97  fof(f9,axiom,(
% 2.77/0.97    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f25,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f9])).
% 2.77/0.97  
% 2.77/0.97  fof(f26,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f25])).
% 2.77/0.97  
% 2.77/0.97  fof(f56,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f26])).
% 2.77/0.97  
% 2.77/0.97  fof(f57,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f26])).
% 2.77/0.97  
% 2.77/0.97  fof(f58,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f26])).
% 2.77/0.97  
% 2.77/0.97  fof(f62,plain,(
% 2.77/0.97    ~v2_struct_0(sK1)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f64,plain,(
% 2.77/0.97    l1_pre_topc(sK1)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f65,plain,(
% 2.77/0.97    ~v2_struct_0(sK2)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f67,plain,(
% 2.77/0.97    ~v2_struct_0(sK3)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f1,axiom,(
% 2.77/0.97    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f31,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.77/0.97    inference(nnf_transformation,[],[f1])).
% 2.77/0.97  
% 2.77/0.97  fof(f32,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.77/0.97    inference(flattening,[],[f31])).
% 2.77/0.97  
% 2.77/0.97  fof(f33,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.77/0.97    inference(rectify,[],[f32])).
% 2.77/0.97  
% 2.77/0.97  fof(f34,plain,(
% 2.77/0.97    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 2.77/0.97    introduced(choice_axiom,[])).
% 2.77/0.97  
% 2.77/0.97  fof(f35,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK0(X0,X1,X2),X1) & ~r2_hidden(sK0(X0,X1,X2),X0)) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (r2_hidden(sK0(X0,X1,X2),X1) | r2_hidden(sK0(X0,X1,X2),X0) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.77/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f33,f34])).
% 2.77/0.97  
% 2.77/0.97  fof(f42,plain,(
% 2.77/0.97    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.77/0.97    inference(cnf_transformation,[],[f35])).
% 2.77/0.97  
% 2.77/0.97  fof(f74,plain,(
% 2.77/0.97    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k2_xboole_0(X0,X1))) )),
% 2.77/0.97    inference(equality_resolution,[],[f42])).
% 2.77/0.97  
% 2.77/0.97  fof(f5,axiom,(
% 2.77/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f18,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.77/0.97    inference(ennf_transformation,[],[f5])).
% 2.77/0.97  
% 2.77/0.97  fof(f51,plain,(
% 2.77/0.97    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f18])).
% 2.77/0.97  
% 2.77/0.97  fof(f6,axiom,(
% 2.77/0.97    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f19,plain,(
% 2.77/0.97    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f6])).
% 2.77/0.97  
% 2.77/0.97  fof(f20,plain,(
% 2.77/0.97    ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f19])).
% 2.77/0.97  
% 2.77/0.97  fof(f52,plain,(
% 2.77/0.97    ( ! [X0,X1] : (m1_subset_1(k1_connsp_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f20])).
% 2.77/0.97  
% 2.77/0.97  fof(f7,axiom,(
% 2.77/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_hidden(X1,k1_connsp_2(X0,X1))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f21,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f7])).
% 2.77/0.97  
% 2.77/0.97  fof(f22,plain,(
% 2.77/0.97    ! [X0] : (! [X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f21])).
% 2.77/0.97  
% 2.77/0.97  fof(f53,plain,(
% 2.77/0.97    ( ! [X0,X1] : (r2_hidden(X1,k1_connsp_2(X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f22])).
% 2.77/0.97  
% 2.77/0.97  fof(f10,axiom,(
% 2.77/0.97    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f27,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.77/0.97    inference(ennf_transformation,[],[f10])).
% 2.77/0.97  
% 2.77/0.97  fof(f28,plain,(
% 2.77/0.97    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.77/0.97    inference(flattening,[],[f27])).
% 2.77/0.97  
% 2.77/0.97  fof(f61,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f28])).
% 2.77/0.97  
% 2.77/0.97  fof(f59,plain,(
% 2.77/0.97    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f28])).
% 2.77/0.97  
% 2.77/0.97  fof(f2,axiom,(
% 2.77/0.97    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.77/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.77/0.97  
% 2.77/0.97  fof(f14,plain,(
% 2.77/0.97    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.77/0.97    inference(ennf_transformation,[],[f2])).
% 2.77/0.97  
% 2.77/0.97  fof(f48,plain,(
% 2.77/0.97    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.77/0.97    inference(cnf_transformation,[],[f14])).
% 2.77/0.97  
% 2.77/0.97  fof(f71,plain,(
% 2.77/0.97    ( ! [X4] : (sK4 != X4 | ~m1_subset_1(X4,u1_struct_0(sK3))) )),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f76,plain,(
% 2.77/0.97    ~m1_subset_1(sK4,u1_struct_0(sK3))),
% 2.77/0.97    inference(equality_resolution,[],[f71])).
% 2.77/0.97  
% 2.77/0.97  fof(f70,plain,(
% 2.77/0.97    ( ! [X5] : (sK4 != X5 | ~m1_subset_1(X5,u1_struct_0(sK2))) )),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  fof(f77,plain,(
% 2.77/0.97    ~m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.77/0.97    inference(equality_resolution,[],[f70])).
% 2.77/0.97  
% 2.77/0.97  fof(f63,plain,(
% 2.77/0.97    v2_pre_topc(sK1)),
% 2.77/0.97    inference(cnf_transformation,[],[f41])).
% 2.77/0.97  
% 2.77/0.97  cnf(c_8,plain,
% 2.77/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.77/0.97      | ~ r2_hidden(X2,X0)
% 2.77/0.97      | ~ v1_xboole_0(X1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_5558,plain,
% 2.77/0.97      ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 2.77/0.97      | ~ r2_hidden(X0,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
% 2.77/0.97      | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.77/0.97      inference(instantiation,[status(thm)],[c_8]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_7826,plain,
% 2.77/0.97      ( ~ m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 2.77/0.97      | ~ r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
% 2.77/0.97      | ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.77/0.97      inference(instantiation,[status(thm)],[c_5558]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_22,negated_conjecture,
% 2.77/0.97      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.77/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_988,plain,
% 2.77/0.97      ( m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_7,plain,
% 2.77/0.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1000,plain,
% 2.77/0.97      ( m1_subset_1(X0,X1) != iProver_top
% 2.77/0.97      | r2_hidden(X0,X1) = iProver_top
% 2.77/0.97      | v1_xboole_0(X1) = iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_2305,plain,
% 2.77/0.97      ( r2_hidden(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top
% 2.77/0.97      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.77/0.97      inference(superposition,[status(thm)],[c_988,c_1000]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_23,negated_conjecture,
% 2.77/0.97      ( m1_pre_topc(sK3,sK1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f68]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_987,plain,
% 2.77/0.97      ( m1_pre_topc(sK3,sK1) = iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_25,negated_conjecture,
% 2.77/0.97      ( m1_pre_topc(sK2,sK1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_985,plain,
% 2.77/0.97      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_13,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 2.77/0.97      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X2)
% 2.77/0.97      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.77/0.97      | ~ l1_pre_topc(X1)
% 2.77/0.97      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 2.77/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_16,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X2)
% 2.77/0.97      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.77/0.97      | ~ l1_pre_topc(X1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_15,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X2)
% 2.77/0.97      | ~ l1_pre_topc(X1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_14,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X2)
% 2.77/0.97      | ~ l1_pre_topc(X1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_179,plain,
% 2.77/0.97      ( v2_struct_0(X2)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ l1_pre_topc(X1)
% 2.77/0.97      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 2.77/0.97      inference(global_propositional_subsumption,
% 2.77/0.97                [status(thm)],
% 2.77/0.97                [c_13,c_16,c_15,c_14]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_180,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(X2,X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X2)
% 2.77/0.97      | ~ l1_pre_topc(X1)
% 2.77/0.97      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 2.77/0.97      inference(renaming,[status(thm)],[c_179]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_978,plain,
% 2.77/0.97      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
% 2.77/0.97      | m1_pre_topc(X1,X0) != iProver_top
% 2.77/0.97      | m1_pre_topc(X2,X0) != iProver_top
% 2.77/0.97      | v2_struct_0(X0) = iProver_top
% 2.77/0.97      | v2_struct_0(X1) = iProver_top
% 2.77/0.97      | v2_struct_0(X2) = iProver_top
% 2.77/0.97      | l1_pre_topc(X0) != iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_180]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1485,plain,
% 2.77/0.97      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 2.77/0.97      | m1_pre_topc(X0,sK1) != iProver_top
% 2.77/0.97      | v2_struct_0(X0) = iProver_top
% 2.77/0.97      | v2_struct_0(sK1) = iProver_top
% 2.77/0.97      | v2_struct_0(sK2) = iProver_top
% 2.77/0.97      | l1_pre_topc(sK1) != iProver_top ),
% 2.77/0.97      inference(superposition,[status(thm)],[c_985,c_978]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_29,negated_conjecture,
% 2.77/0.97      ( ~ v2_struct_0(sK1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f62]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_30,plain,
% 2.77/0.97      ( v2_struct_0(sK1) != iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_27,negated_conjecture,
% 2.77/0.97      ( l1_pre_topc(sK1) ),
% 2.77/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_32,plain,
% 2.77/0.97      ( l1_pre_topc(sK1) = iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_26,negated_conjecture,
% 2.77/0.97      ( ~ v2_struct_0(sK2) ),
% 2.77/0.97      inference(cnf_transformation,[],[f65]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_33,plain,
% 2.77/0.97      ( v2_struct_0(sK2) != iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1731,plain,
% 2.77/0.97      ( v2_struct_0(X0) = iProver_top
% 2.77/0.97      | m1_pre_topc(X0,sK1) != iProver_top
% 2.77/0.97      | u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 2.77/0.97      inference(global_propositional_subsumption,
% 2.77/0.97                [status(thm)],
% 2.77/0.97                [c_1485,c_30,c_32,c_33]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1732,plain,
% 2.77/0.97      ( u1_struct_0(k1_tsep_1(sK1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0))
% 2.77/0.97      | m1_pre_topc(X0,sK1) != iProver_top
% 2.77/0.97      | v2_struct_0(X0) = iProver_top ),
% 2.77/0.97      inference(renaming,[status(thm)],[c_1731]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1737,plain,
% 2.77/0.97      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
% 2.77/0.97      | v2_struct_0(sK3) = iProver_top ),
% 2.77/0.97      inference(superposition,[status(thm)],[c_987,c_1732]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_24,negated_conjecture,
% 2.77/0.97      ( ~ v2_struct_0(sK3) ),
% 2.77/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1130,plain,
% 2.77/0.97      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.97      | ~ m1_pre_topc(sK2,X1)
% 2.77/0.97      | v2_struct_0(X1)
% 2.77/0.97      | v2_struct_0(X0)
% 2.77/0.97      | v2_struct_0(sK2)
% 2.77/0.97      | ~ l1_pre_topc(X1)
% 2.77/0.97      | u1_struct_0(k1_tsep_1(X1,sK2,X0)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(X0)) ),
% 2.77/0.97      inference(instantiation,[status(thm)],[c_180]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1429,plain,
% 2.77/0.97      ( ~ m1_pre_topc(sK2,sK1)
% 2.77/0.97      | ~ m1_pre_topc(sK3,sK1)
% 2.77/0.97      | v2_struct_0(sK1)
% 2.77/0.97      | v2_struct_0(sK2)
% 2.77/0.97      | v2_struct_0(sK3)
% 2.77/0.97      | ~ l1_pre_topc(sK1)
% 2.77/0.97      | u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.77/0.97      inference(instantiation,[status(thm)],[c_1130]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1742,plain,
% 2.77/0.97      ( u1_struct_0(k1_tsep_1(sK1,sK2,sK3)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 2.77/0.97      inference(global_propositional_subsumption,
% 2.77/0.97                [status(thm)],
% 2.77/0.97                [c_1737,c_29,c_27,c_26,c_25,c_24,c_23,c_1429]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_5,plain,
% 2.77/0.97      ( r2_hidden(X0,X1)
% 2.77/0.97      | r2_hidden(X0,X2)
% 2.77/0.97      | ~ r2_hidden(X0,k2_xboole_0(X2,X1)) ),
% 2.77/0.97      inference(cnf_transformation,[],[f74]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_1002,plain,
% 2.77/0.97      ( r2_hidden(X0,X1) = iProver_top
% 2.77/0.97      | r2_hidden(X0,X2) = iProver_top
% 2.77/0.97      | r2_hidden(X0,k2_xboole_0(X2,X1)) != iProver_top ),
% 2.77/0.97      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_3229,plain,
% 2.77/0.97      ( r2_hidden(X0,u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) != iProver_top
% 2.77/0.97      | r2_hidden(X0,u1_struct_0(sK2)) = iProver_top
% 2.77/0.97      | r2_hidden(X0,u1_struct_0(sK3)) = iProver_top ),
% 2.77/0.97      inference(superposition,[status(thm)],[c_1742,c_1002]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_4468,plain,
% 2.77/0.97      ( r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 2.77/0.97      | r2_hidden(sK4,u1_struct_0(sK3)) = iProver_top
% 2.77/0.97      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) = iProver_top ),
% 2.77/0.97      inference(superposition,[status(thm)],[c_2305,c_3229]) ).
% 2.77/0.97  
% 2.77/0.97  cnf(c_4469,plain,
% 2.77/0.97      ( r2_hidden(sK4,u1_struct_0(sK2))
% 2.77/0.97      | r2_hidden(sK4,u1_struct_0(sK3))
% 2.77/0.97      | v1_xboole_0(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))) ),
% 2.77/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4468]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_9,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 2.77/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_2262,plain,
% 2.77/0.98      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),X0)
% 2.77/0.98      | ~ l1_pre_topc(X0)
% 2.77/0.98      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_2264,plain,
% 2.77/0.98      ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
% 2.77/0.98      | l1_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_2262]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_10,plain,
% 2.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.77/0.98      | m1_subset_1(k1_connsp_2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | ~ v2_pre_topc(X1)
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1847,plain,
% 2.77/0.98      ( m1_subset_1(k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK1,sK2,sK3))))
% 2.77/0.98      | ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 2.77/0.98      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_11,plain,
% 2.77/0.98      ( ~ m1_subset_1(X0,u1_struct_0(X1))
% 2.77/0.98      | r2_hidden(X0,k1_connsp_2(X1,X0))
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | ~ v2_pre_topc(X1)
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1681,plain,
% 2.77/0.98      ( ~ m1_subset_1(sK4,u1_struct_0(k1_tsep_1(sK1,sK2,sK3)))
% 2.77/0.98      | r2_hidden(sK4,k1_connsp_2(k1_tsep_1(sK1,sK2,sK3),sK4))
% 2.77/0.98      | v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ l1_pre_topc(k1_tsep_1(sK1,sK2,sK3)) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1194,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.77/0.98      | ~ m1_pre_topc(X1,sK1)
% 2.77/0.98      | m1_pre_topc(k1_tsep_1(sK1,X0,X1),sK1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_14]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1375,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.77/0.98      | m1_pre_topc(k1_tsep_1(sK1,sK2,X0),sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_1194]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1611,plain,
% 2.77/0.98      ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK3),sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | v2_struct_0(sK3)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_1375]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_17,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.98      | ~ m1_pre_topc(X2,X1)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X2)
% 2.77/0.98      | ~ v2_pre_topc(X1)
% 2.77/0.98      | v2_pre_topc(k1_tsep_1(X1,X0,X2))
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1193,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.77/0.98      | ~ m1_pre_topc(X1,sK1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_pre_topc(k1_tsep_1(sK1,X0,X1))
% 2.77/0.98      | ~ v2_pre_topc(sK1)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1362,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK2,sK1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | v2_pre_topc(k1_tsep_1(sK1,sK2,X0))
% 2.77/0.98      | ~ v2_pre_topc(sK1)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_1193]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1599,plain,
% 2.77/0.98      ( ~ m1_pre_topc(sK2,sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | v2_struct_0(sK3)
% 2.77/0.98      | v2_pre_topc(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | ~ v2_pre_topc(sK1)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_1362]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_19,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.98      | ~ m1_pre_topc(X2,X1)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X2)
% 2.77/0.98      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.77/0.98      | ~ v2_pre_topc(X1)
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_165,plain,
% 2.77/0.98      ( ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.77/0.98      | v2_struct_0(X2)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | ~ m1_pre_topc(X2,X1)
% 2.77/0.98      | ~ m1_pre_topc(X0,X1)
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(global_propositional_subsumption,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_19,c_16]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_166,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.98      | ~ m1_pre_topc(X2,X1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(X2)
% 2.77/0.98      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(renaming,[status(thm)],[c_165]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1131,plain,
% 2.77/0.98      ( ~ m1_pre_topc(X0,X1)
% 2.77/0.98      | ~ m1_pre_topc(sK2,X1)
% 2.77/0.98      | v2_struct_0(X1)
% 2.77/0.98      | v2_struct_0(X0)
% 2.77/0.98      | ~ v2_struct_0(k1_tsep_1(X1,sK2,X0))
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | ~ l1_pre_topc(X1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_166]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1409,plain,
% 2.77/0.98      ( ~ m1_pre_topc(sK2,sK1)
% 2.77/0.98      | ~ m1_pre_topc(sK3,sK1)
% 2.77/0.98      | ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK3))
% 2.77/0.98      | v2_struct_0(sK1)
% 2.77/0.98      | v2_struct_0(sK2)
% 2.77/0.98      | v2_struct_0(sK3)
% 2.77/0.98      | ~ l1_pre_topc(sK1) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_1131]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_6,plain,
% 2.77/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1054,plain,
% 2.77/0.98      ( m1_subset_1(sK4,u1_struct_0(sK2))
% 2.77/0.98      | ~ r2_hidden(sK4,u1_struct_0(sK2)) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_1046,plain,
% 2.77/0.98      ( m1_subset_1(sK4,u1_struct_0(sK3))
% 2.77/0.98      | ~ r2_hidden(sK4,u1_struct_0(sK3)) ),
% 2.77/0.98      inference(instantiation,[status(thm)],[c_6]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_20,negated_conjecture,
% 2.77/0.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK3)) ),
% 2.77/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_21,negated_conjecture,
% 2.77/0.98      ( ~ m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.77/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(c_28,negated_conjecture,
% 2.77/0.98      ( v2_pre_topc(sK1) ),
% 2.77/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.77/0.98  
% 2.77/0.98  cnf(contradiction,plain,
% 2.77/0.98      ( $false ),
% 2.77/0.98      inference(minisat,
% 2.77/0.98                [status(thm)],
% 2.77/0.98                [c_7826,c_4469,c_2264,c_1847,c_1681,c_1611,c_1599,c_1409,
% 2.77/0.98                 c_1054,c_1046,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,
% 2.77/0.98                 c_28,c_29]) ).
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.77/0.98  
% 2.77/0.98  ------                               Statistics
% 2.77/0.98  
% 2.77/0.98  ------ General
% 2.77/0.98  
% 2.77/0.98  abstr_ref_over_cycles:                  0
% 2.77/0.98  abstr_ref_under_cycles:                 0
% 2.77/0.98  gc_basic_clause_elim:                   0
% 2.77/0.98  forced_gc_time:                         0
% 2.77/0.98  parsing_time:                           0.009
% 2.77/0.98  unif_index_cands_time:                  0.
% 2.77/0.98  unif_index_add_time:                    0.
% 2.77/0.98  orderings_time:                         0.
% 2.77/0.98  out_proof_time:                         0.011
% 2.77/0.98  total_time:                             0.337
% 2.77/0.98  num_of_symbols:                         49
% 2.77/0.98  num_of_terms:                           10910
% 2.77/0.98  
% 2.77/0.98  ------ Preprocessing
% 2.77/0.98  
% 2.77/0.98  num_of_splits:                          0
% 2.77/0.98  num_of_split_atoms:                     0
% 2.77/0.98  num_of_reused_defs:                     0
% 2.77/0.98  num_eq_ax_congr_red:                    12
% 2.77/0.98  num_of_sem_filtered_clauses:            1
% 2.77/0.98  num_of_subtypes:                        0
% 2.77/0.98  monotx_restored_types:                  0
% 2.77/0.98  sat_num_of_epr_types:                   0
% 2.77/0.98  sat_num_of_non_cyclic_types:            0
% 2.77/0.98  sat_guarded_non_collapsed_types:        0
% 2.77/0.98  num_pure_diseq_elim:                    0
% 2.77/0.98  simp_replaced_by:                       0
% 2.77/0.98  res_preprocessed:                       117
% 2.77/0.98  prep_upred:                             0
% 2.77/0.98  prep_unflattend:                        2
% 2.77/0.98  smt_new_axioms:                         0
% 2.77/0.98  pred_elim_cands:                        8
% 2.77/0.98  pred_elim:                              0
% 2.77/0.98  pred_elim_cl:                           0
% 2.77/0.98  pred_elim_cycles:                       2
% 2.77/0.98  merged_defs:                            0
% 2.77/0.98  merged_defs_ncl:                        0
% 2.77/0.98  bin_hyper_res:                          0
% 2.77/0.98  prep_cycles:                            3
% 2.77/0.98  pred_elim_time:                         0.006
% 2.77/0.98  splitting_time:                         0.
% 2.77/0.98  sem_filter_time:                        0.
% 2.77/0.98  monotx_time:                            0.
% 2.77/0.98  subtype_inf_time:                       0.
% 2.77/0.98  
% 2.77/0.98  ------ Problem properties
% 2.77/0.98  
% 2.77/0.98  clauses:                                30
% 2.77/0.98  conjectures:                            10
% 2.77/0.98  epr:                                    10
% 2.77/0.98  horn:                                   17
% 2.77/0.98  ground:                                 10
% 2.77/0.98  unary:                                  10
% 2.77/0.98  binary:                                 3
% 2.77/0.98  lits:                                   109
% 2.77/0.98  lits_eq:                                6
% 2.77/0.98  fd_pure:                                0
% 2.77/0.98  fd_pseudo:                              0
% 2.77/0.98  fd_cond:                                0
% 2.77/0.98  fd_pseudo_cond:                         4
% 2.77/0.98  ac_symbols:                             0
% 2.77/0.98  
% 2.77/0.98  ------ Propositional Solver
% 2.77/0.98  
% 2.77/0.98  prop_solver_calls:                      25
% 2.77/0.98  prop_fast_solver_calls:                 1267
% 2.77/0.98  smt_solver_calls:                       0
% 2.77/0.98  smt_fast_solver_calls:                  0
% 2.77/0.98  prop_num_of_clauses:                    3978
% 2.77/0.98  prop_preprocess_simplified:             9521
% 2.77/0.98  prop_fo_subsumed:                       44
% 2.77/0.98  prop_solver_time:                       0.
% 2.77/0.98  smt_solver_time:                        0.
% 2.77/0.98  smt_fast_solver_time:                   0.
% 2.77/0.98  prop_fast_solver_time:                  0.
% 2.77/0.98  prop_unsat_core_time:                   0.
% 2.77/0.98  
% 2.77/0.98  ------ QBF
% 2.77/0.98  
% 2.77/0.98  qbf_q_res:                              0
% 2.77/0.98  qbf_num_tautologies:                    0
% 2.77/0.98  qbf_prep_cycles:                        0
% 2.77/0.98  
% 2.77/0.98  ------ BMC1
% 2.77/0.98  
% 2.77/0.98  bmc1_current_bound:                     -1
% 2.77/0.98  bmc1_last_solved_bound:                 -1
% 2.77/0.98  bmc1_unsat_core_size:                   -1
% 2.77/0.98  bmc1_unsat_core_parents_size:           -1
% 2.77/0.98  bmc1_merge_next_fun:                    0
% 2.77/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.77/0.98  
% 2.77/0.98  ------ Instantiation
% 2.77/0.98  
% 2.77/0.98  inst_num_of_clauses:                    977
% 2.77/0.98  inst_num_in_passive:                    411
% 2.77/0.98  inst_num_in_active:                     530
% 2.77/0.98  inst_num_in_unprocessed:                35
% 2.77/0.98  inst_num_of_loops:                      577
% 2.77/0.98  inst_num_of_learning_restarts:          0
% 2.77/0.98  inst_num_moves_active_passive:          45
% 2.77/0.98  inst_lit_activity:                      0
% 2.77/0.98  inst_lit_activity_moves:                1
% 2.77/0.98  inst_num_tautologies:                   0
% 2.77/0.98  inst_num_prop_implied:                  0
% 2.77/0.98  inst_num_existing_simplified:           0
% 2.77/0.98  inst_num_eq_res_simplified:             0
% 2.77/0.98  inst_num_child_elim:                    0
% 2.77/0.98  inst_num_of_dismatching_blockings:      478
% 2.77/0.98  inst_num_of_non_proper_insts:           651
% 2.77/0.98  inst_num_of_duplicates:                 0
% 2.77/0.98  inst_inst_num_from_inst_to_res:         0
% 2.77/0.98  inst_dismatching_checking_time:         0.
% 2.77/0.98  
% 2.77/0.98  ------ Resolution
% 2.77/0.98  
% 2.77/0.98  res_num_of_clauses:                     0
% 2.77/0.98  res_num_in_passive:                     0
% 2.77/0.98  res_num_in_active:                      0
% 2.77/0.98  res_num_of_loops:                       120
% 2.77/0.98  res_forward_subset_subsumed:            11
% 2.77/0.98  res_backward_subset_subsumed:           0
% 2.77/0.98  res_forward_subsumed:                   0
% 2.77/0.98  res_backward_subsumed:                  0
% 2.77/0.98  res_forward_subsumption_resolution:     2
% 2.77/0.98  res_backward_subsumption_resolution:    0
% 2.77/0.98  res_clause_to_clause_subsumption:       1189
% 2.77/0.98  res_orphan_elimination:                 0
% 2.77/0.98  res_tautology_del:                      20
% 2.77/0.98  res_num_eq_res_simplified:              0
% 2.77/0.98  res_num_sel_changes:                    0
% 2.77/0.98  res_moves_from_active_to_pass:          0
% 2.77/0.98  
% 2.77/0.98  ------ Superposition
% 2.77/0.98  
% 2.77/0.98  sup_time_total:                         0.
% 2.77/0.98  sup_time_generating:                    0.
% 2.77/0.98  sup_time_sim_full:                      0.
% 2.77/0.98  sup_time_sim_immed:                     0.
% 2.77/0.98  
% 2.77/0.98  sup_num_of_clauses:                     295
% 2.77/0.98  sup_num_in_active:                      113
% 2.77/0.98  sup_num_in_passive:                     182
% 2.77/0.98  sup_num_of_loops:                       114
% 2.77/0.98  sup_fw_superposition:                   193
% 2.77/0.98  sup_bw_superposition:                   192
% 2.77/0.98  sup_immediate_simplified:               67
% 2.77/0.98  sup_given_eliminated:                   0
% 2.77/0.98  comparisons_done:                       0
% 2.77/0.98  comparisons_avoided:                    0
% 2.77/0.98  
% 2.77/0.98  ------ Simplifications
% 2.77/0.98  
% 2.77/0.98  
% 2.77/0.98  sim_fw_subset_subsumed:                 26
% 2.77/0.98  sim_bw_subset_subsumed:                 0
% 2.77/0.98  sim_fw_subsumed:                        8
% 2.77/0.98  sim_bw_subsumed:                        1
% 2.77/0.98  sim_fw_subsumption_res:                 0
% 2.77/0.98  sim_bw_subsumption_res:                 0
% 2.77/0.98  sim_tautology_del:                      23
% 2.77/0.98  sim_eq_tautology_del:                   0
% 2.77/0.98  sim_eq_res_simp:                        6
% 2.77/0.98  sim_fw_demodulated:                     24
% 2.77/0.98  sim_bw_demodulated:                     0
% 2.77/0.98  sim_light_normalised:                   36
% 2.77/0.98  sim_joinable_taut:                      0
% 2.77/0.98  sim_joinable_simp:                      0
% 2.77/0.98  sim_ac_normalised:                      0
% 2.77/0.98  sim_smt_subsumption:                    0
% 2.77/0.98  
%------------------------------------------------------------------------------
