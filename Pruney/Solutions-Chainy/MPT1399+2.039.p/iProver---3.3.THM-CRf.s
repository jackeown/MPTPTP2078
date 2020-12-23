%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:18:39 EST 2020

% Result     : Theorem 0.69s
% Output     : CNFRefutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 710 expanded)
%              Number of clauses        :   65 ( 166 expanded)
%              Number of leaves         :   16 ( 192 expanded)
%              Depth                    :   21
%              Number of atoms          :  414 (6984 expanded)
%              Number of equality atoms :   84 ( 624 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal clause size      :   30 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k1_xboole_0 = X2
          & ! [X3] :
              ( ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(X1,X3)
                  | ~ v4_pre_topc(X3,X0)
                  | ~ v3_pre_topc(X3,X0) )
                & ( ( r2_hidden(X1,X3)
                    & v4_pre_topc(X3,X0)
                    & v3_pre_topc(X3,X0) )
                  | ~ r2_hidden(X3,X2) ) )
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( k1_xboole_0 = sK3
        & ! [X3] :
            ( ( ( r2_hidden(X3,sK3)
                | ~ r2_hidden(X1,X3)
                | ~ v4_pre_topc(X3,X0)
                | ~ v3_pre_topc(X3,X0) )
              & ( ( r2_hidden(X1,X3)
                  & v4_pre_topc(X3,X0)
                  & v3_pre_topc(X3,X0) )
                | ~ r2_hidden(X3,sK3) ) )
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,X0)
                      | ~ v3_pre_topc(X3,X0) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,X0)
                        & v3_pre_topc(X3,X0) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_xboole_0 = X2
            & ! [X3] :
                ( ( ( r2_hidden(X3,X2)
                    | ~ r2_hidden(sK2,X3)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ v3_pre_topc(X3,X0) )
                  & ( ( r2_hidden(sK2,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) )
                    | ~ r2_hidden(X3,X2) ) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k1_xboole_0 = X2
                & ! [X3] :
                    ( ( ( r2_hidden(X3,X2)
                        | ~ r2_hidden(X1,X3)
                        | ~ v4_pre_topc(X3,X0)
                        | ~ v3_pre_topc(X3,X0) )
                      & ( ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) )
                        | ~ r2_hidden(X3,X2) ) )
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( ( r2_hidden(X3,X2)
                      | ~ r2_hidden(X1,X3)
                      | ~ v4_pre_topc(X3,sK1)
                      | ~ v3_pre_topc(X3,sK1) )
                    & ( ( r2_hidden(X1,X3)
                        & v4_pre_topc(X3,sK1)
                        & v3_pre_topc(X3,sK1) )
                      | ~ r2_hidden(X3,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( k1_xboole_0 = sK3
    & ! [X3] :
        ( ( ( r2_hidden(X3,sK3)
            | ~ r2_hidden(sK2,X3)
            | ~ v4_pre_topc(X3,sK1)
            | ~ v3_pre_topc(X3,sK1) )
          & ( ( r2_hidden(sK2,X3)
              & v4_pre_topc(X3,sK1)
              & v3_pre_topc(X3,sK1) )
            | ~ r2_hidden(X3,sK3) ) )
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
    & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).

fof(f49,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f54,plain,(
    ! [X3] :
      ( r2_hidden(X3,sK3)
      | ~ r2_hidden(sK2,X3)
      | ~ v4_pre_topc(X3,sK1)
      | ~ v3_pre_topc(X3,sK1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f43,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f47,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f48,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f22,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f45,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X3] :
      ( r2_hidden(sK2,X3)
      | ~ r2_hidden(X3,sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,negated_conjecture,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ v4_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_19,negated_conjecture,
    ( v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_255,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_19])).

cnf(c_256,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_255])).

cnf(c_18,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_45,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_258,plain,
    ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_256,c_19,c_18,c_45])).

cnf(c_343,plain,
    ( ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(X0,sK3)
    | ~ r2_hidden(sK2,X0)
    | k2_struct_0(sK1) != X0
    | sK1 != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_258])).

cnf(c_344,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_10,plain,
    ( v3_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_39,plain,
    ( v3_pre_topc(k2_struct_0(sK1),sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_346,plain,
    ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_344,c_19,c_18,c_39])).

cnf(c_469,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | k2_struct_0(sK1) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_17,c_346])).

cnf(c_1127,plain,
    ( k2_struct_0(sK1) != sK2
    | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK1)
    | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_469])).

cnf(c_11,negated_conjecture,
    ( k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_7,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_230,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_7,c_6])).

cnf(c_270,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_230,c_18])).

cnf(c_271,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_1206,plain,
    ( k2_struct_0(sK1) != sK2
    | k1_zfmisc_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
    | r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1127,c_11,c_271])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_217,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_218,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_217])).

cnf(c_42,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_48,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_220,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_218,c_20,c_18,c_42,c_48])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_418,plain,
    ( r2_hidden(X0,X1)
    | v1_xboole_0(X1)
    | u1_struct_0(sK1) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_17])).

cnf(c_419,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_418])).

cnf(c_604,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_220,c_419])).

cnf(c_51,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_606,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_604,c_18,c_48,c_51])).

cnf(c_1126,plain,
    ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1148,plain,
    ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1126,c_271])).

cnf(c_1211,plain,
    ( k2_struct_0(sK1) != sK2
    | k1_zfmisc_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
    | r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1206,c_1148])).

cnf(c_4,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_391,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | k2_subset_1(X0) != k2_struct_0(sK1) ),
    inference(resolution_lifted,[status(thm)],[c_4,c_346])).

cnf(c_878,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3)
    | ~ r2_hidden(sK2,k2_struct_0(sK1))
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_391])).

cnf(c_1132,plain,
    ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_878])).

cnf(c_1171,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
    | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1132,c_11])).

cnf(c_1175,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1171,c_1148])).

cnf(c_3,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1260,plain,
    ( k2_subset_1(k2_struct_0(sK1)) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_877,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | k2_subset_1(X0) != k2_struct_0(sK1)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_391])).

cnf(c_1261,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(k2_struct_0(sK1))
    | k2_subset_1(k2_struct_0(sK1)) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_877])).

cnf(c_1262,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(k2_struct_0(sK1))
    | k2_subset_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1261])).

cnf(c_884,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_1344,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_884])).

cnf(c_1569,plain,
    ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_18,c_48,c_51,c_1175,c_1260,c_1262,c_1344])).

cnf(c_13,negated_conjecture,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r2_hidden(X0,sK3)
    | r2_hidden(sK2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_376,plain,
    ( ~ r2_hidden(X0,sK3)
    | r2_hidden(sK2,X0)
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
    | k2_subset_1(X1) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_377,plain,
    ( ~ r2_hidden(k2_subset_1(X0),sK3)
    | r2_hidden(sK2,k2_subset_1(X0))
    | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1134,plain,
    ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r2_hidden(k2_subset_1(X0),sK3) != iProver_top
    | r2_hidden(sK2,k2_subset_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_1199,plain,
    ( k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
    | r2_hidden(X0,k1_xboole_0) != iProver_top
    | r2_hidden(sK2,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1134,c_3,c_11,c_271])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_307,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_308,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_309,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_1283,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1199,c_309])).

cnf(c_1574,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1569,c_1283])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 0.69/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.69/1.03  
% 0.69/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.69/1.03  
% 0.69/1.03  ------  iProver source info
% 0.69/1.03  
% 0.69/1.03  git: date: 2020-06-30 10:37:57 +0100
% 0.69/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.69/1.03  git: non_committed_changes: false
% 0.69/1.03  git: last_make_outside_of_git: false
% 0.69/1.03  
% 0.69/1.03  ------ 
% 0.69/1.03  
% 0.69/1.03  ------ Input Options
% 0.69/1.03  
% 0.69/1.03  --out_options                           all
% 0.69/1.03  --tptp_safe_out                         true
% 0.69/1.03  --problem_path                          ""
% 0.69/1.03  --include_path                          ""
% 0.69/1.03  --clausifier                            res/vclausify_rel
% 0.69/1.03  --clausifier_options                    --mode clausify
% 0.69/1.03  --stdin                                 false
% 0.69/1.03  --stats_out                             all
% 0.69/1.03  
% 0.69/1.03  ------ General Options
% 0.69/1.03  
% 0.69/1.03  --fof                                   false
% 0.69/1.03  --time_out_real                         305.
% 0.69/1.03  --time_out_virtual                      -1.
% 0.69/1.03  --symbol_type_check                     false
% 0.69/1.03  --clausify_out                          false
% 0.69/1.03  --sig_cnt_out                           false
% 0.69/1.03  --trig_cnt_out                          false
% 0.69/1.03  --trig_cnt_out_tolerance                1.
% 0.69/1.03  --trig_cnt_out_sk_spl                   false
% 0.69/1.03  --abstr_cl_out                          false
% 0.69/1.03  
% 0.69/1.03  ------ Global Options
% 0.69/1.03  
% 0.69/1.03  --schedule                              default
% 0.69/1.03  --add_important_lit                     false
% 0.69/1.03  --prop_solver_per_cl                    1000
% 0.69/1.03  --min_unsat_core                        false
% 0.69/1.03  --soft_assumptions                      false
% 0.69/1.03  --soft_lemma_size                       3
% 0.69/1.03  --prop_impl_unit_size                   0
% 0.69/1.03  --prop_impl_unit                        []
% 0.69/1.03  --share_sel_clauses                     true
% 0.69/1.03  --reset_solvers                         false
% 0.69/1.03  --bc_imp_inh                            [conj_cone]
% 0.69/1.03  --conj_cone_tolerance                   3.
% 0.69/1.03  --extra_neg_conj                        none
% 0.69/1.03  --large_theory_mode                     true
% 0.69/1.03  --prolific_symb_bound                   200
% 0.69/1.03  --lt_threshold                          2000
% 0.69/1.03  --clause_weak_htbl                      true
% 0.69/1.03  --gc_record_bc_elim                     false
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing Options
% 0.69/1.03  
% 0.69/1.03  --preprocessing_flag                    true
% 0.69/1.03  --time_out_prep_mult                    0.1
% 0.69/1.03  --splitting_mode                        input
% 0.69/1.03  --splitting_grd                         true
% 0.69/1.03  --splitting_cvd                         false
% 0.69/1.03  --splitting_cvd_svl                     false
% 0.69/1.03  --splitting_nvd                         32
% 0.69/1.03  --sub_typing                            true
% 0.69/1.03  --prep_gs_sim                           true
% 0.69/1.03  --prep_unflatten                        true
% 0.69/1.03  --prep_res_sim                          true
% 0.69/1.03  --prep_upred                            true
% 0.69/1.03  --prep_sem_filter                       exhaustive
% 0.69/1.03  --prep_sem_filter_out                   false
% 0.69/1.03  --pred_elim                             true
% 0.69/1.03  --res_sim_input                         true
% 0.69/1.03  --eq_ax_congr_red                       true
% 0.69/1.03  --pure_diseq_elim                       true
% 0.69/1.03  --brand_transform                       false
% 0.69/1.03  --non_eq_to_eq                          false
% 0.69/1.03  --prep_def_merge                        true
% 0.69/1.03  --prep_def_merge_prop_impl              false
% 0.69/1.03  --prep_def_merge_mbd                    true
% 0.69/1.03  --prep_def_merge_tr_red                 false
% 0.69/1.03  --prep_def_merge_tr_cl                  false
% 0.69/1.03  --smt_preprocessing                     true
% 0.69/1.03  --smt_ac_axioms                         fast
% 0.69/1.03  --preprocessed_out                      false
% 0.69/1.03  --preprocessed_stats                    false
% 0.69/1.03  
% 0.69/1.03  ------ Abstraction refinement Options
% 0.69/1.03  
% 0.69/1.03  --abstr_ref                             []
% 0.69/1.03  --abstr_ref_prep                        false
% 0.69/1.03  --abstr_ref_until_sat                   false
% 0.69/1.03  --abstr_ref_sig_restrict                funpre
% 0.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.69/1.03  --abstr_ref_under                       []
% 0.69/1.03  
% 0.69/1.03  ------ SAT Options
% 0.69/1.03  
% 0.69/1.03  --sat_mode                              false
% 0.69/1.03  --sat_fm_restart_options                ""
% 0.69/1.03  --sat_gr_def                            false
% 0.69/1.03  --sat_epr_types                         true
% 0.69/1.03  --sat_non_cyclic_types                  false
% 0.69/1.03  --sat_finite_models                     false
% 0.69/1.03  --sat_fm_lemmas                         false
% 0.69/1.03  --sat_fm_prep                           false
% 0.69/1.03  --sat_fm_uc_incr                        true
% 0.69/1.03  --sat_out_model                         small
% 0.69/1.03  --sat_out_clauses                       false
% 0.69/1.03  
% 0.69/1.03  ------ QBF Options
% 0.69/1.03  
% 0.69/1.03  --qbf_mode                              false
% 0.69/1.03  --qbf_elim_univ                         false
% 0.69/1.03  --qbf_dom_inst                          none
% 0.69/1.03  --qbf_dom_pre_inst                      false
% 0.69/1.03  --qbf_sk_in                             false
% 0.69/1.03  --qbf_pred_elim                         true
% 0.69/1.03  --qbf_split                             512
% 0.69/1.03  
% 0.69/1.03  ------ BMC1 Options
% 0.69/1.03  
% 0.69/1.03  --bmc1_incremental                      false
% 0.69/1.03  --bmc1_axioms                           reachable_all
% 0.69/1.03  --bmc1_min_bound                        0
% 0.69/1.03  --bmc1_max_bound                        -1
% 0.69/1.03  --bmc1_max_bound_default                -1
% 0.69/1.03  --bmc1_symbol_reachability              true
% 0.69/1.03  --bmc1_property_lemmas                  false
% 0.69/1.03  --bmc1_k_induction                      false
% 0.69/1.03  --bmc1_non_equiv_states                 false
% 0.69/1.03  --bmc1_deadlock                         false
% 0.69/1.03  --bmc1_ucm                              false
% 0.69/1.03  --bmc1_add_unsat_core                   none
% 0.69/1.03  --bmc1_unsat_core_children              false
% 0.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.69/1.03  --bmc1_out_stat                         full
% 0.69/1.03  --bmc1_ground_init                      false
% 0.69/1.03  --bmc1_pre_inst_next_state              false
% 0.69/1.03  --bmc1_pre_inst_state                   false
% 0.69/1.03  --bmc1_pre_inst_reach_state             false
% 0.69/1.03  --bmc1_out_unsat_core                   false
% 0.69/1.03  --bmc1_aig_witness_out                  false
% 0.69/1.03  --bmc1_verbose                          false
% 0.69/1.03  --bmc1_dump_clauses_tptp                false
% 0.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.69/1.03  --bmc1_dump_file                        -
% 0.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.69/1.03  --bmc1_ucm_extend_mode                  1
% 0.69/1.03  --bmc1_ucm_init_mode                    2
% 0.69/1.03  --bmc1_ucm_cone_mode                    none
% 0.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.69/1.03  --bmc1_ucm_relax_model                  4
% 0.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.69/1.03  --bmc1_ucm_layered_model                none
% 0.69/1.03  --bmc1_ucm_max_lemma_size               10
% 0.69/1.03  
% 0.69/1.03  ------ AIG Options
% 0.69/1.03  
% 0.69/1.03  --aig_mode                              false
% 0.69/1.03  
% 0.69/1.03  ------ Instantiation Options
% 0.69/1.03  
% 0.69/1.03  --instantiation_flag                    true
% 0.69/1.03  --inst_sos_flag                         false
% 0.69/1.03  --inst_sos_phase                        true
% 0.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.69/1.03  --inst_lit_sel_side                     num_symb
% 0.69/1.03  --inst_solver_per_active                1400
% 0.69/1.03  --inst_solver_calls_frac                1.
% 0.69/1.03  --inst_passive_queue_type               priority_queues
% 0.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.69/1.03  --inst_passive_queues_freq              [25;2]
% 0.69/1.03  --inst_dismatching                      true
% 0.69/1.03  --inst_eager_unprocessed_to_passive     true
% 0.69/1.03  --inst_prop_sim_given                   true
% 0.69/1.03  --inst_prop_sim_new                     false
% 0.69/1.03  --inst_subs_new                         false
% 0.69/1.03  --inst_eq_res_simp                      false
% 0.69/1.03  --inst_subs_given                       false
% 0.69/1.03  --inst_orphan_elimination               true
% 0.69/1.03  --inst_learning_loop_flag               true
% 0.69/1.03  --inst_learning_start                   3000
% 0.69/1.03  --inst_learning_factor                  2
% 0.69/1.03  --inst_start_prop_sim_after_learn       3
% 0.69/1.03  --inst_sel_renew                        solver
% 0.69/1.03  --inst_lit_activity_flag                true
% 0.69/1.03  --inst_restr_to_given                   false
% 0.69/1.03  --inst_activity_threshold               500
% 0.69/1.03  --inst_out_proof                        true
% 0.69/1.03  
% 0.69/1.03  ------ Resolution Options
% 0.69/1.03  
% 0.69/1.03  --resolution_flag                       true
% 0.69/1.03  --res_lit_sel                           adaptive
% 0.69/1.03  --res_lit_sel_side                      none
% 0.69/1.03  --res_ordering                          kbo
% 0.69/1.03  --res_to_prop_solver                    active
% 0.69/1.03  --res_prop_simpl_new                    false
% 0.69/1.03  --res_prop_simpl_given                  true
% 0.69/1.03  --res_passive_queue_type                priority_queues
% 0.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.69/1.03  --res_passive_queues_freq               [15;5]
% 0.69/1.03  --res_forward_subs                      full
% 0.69/1.03  --res_backward_subs                     full
% 0.69/1.03  --res_forward_subs_resolution           true
% 0.69/1.03  --res_backward_subs_resolution          true
% 0.69/1.03  --res_orphan_elimination                true
% 0.69/1.03  --res_time_limit                        2.
% 0.69/1.03  --res_out_proof                         true
% 0.69/1.03  
% 0.69/1.03  ------ Superposition Options
% 0.69/1.03  
% 0.69/1.03  --superposition_flag                    true
% 0.69/1.03  --sup_passive_queue_type                priority_queues
% 0.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.69/1.03  --demod_completeness_check              fast
% 0.69/1.03  --demod_use_ground                      true
% 0.69/1.03  --sup_to_prop_solver                    passive
% 0.69/1.03  --sup_prop_simpl_new                    true
% 0.69/1.03  --sup_prop_simpl_given                  true
% 0.69/1.03  --sup_fun_splitting                     false
% 0.69/1.03  --sup_smt_interval                      50000
% 0.69/1.03  
% 0.69/1.03  ------ Superposition Simplification Setup
% 0.69/1.03  
% 0.69/1.03  --sup_indices_passive                   []
% 0.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_full_bw                           [BwDemod]
% 0.69/1.03  --sup_immed_triv                        [TrivRules]
% 0.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_immed_bw_main                     []
% 0.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.03  
% 0.69/1.03  ------ Combination Options
% 0.69/1.03  
% 0.69/1.03  --comb_res_mult                         3
% 0.69/1.03  --comb_sup_mult                         2
% 0.69/1.03  --comb_inst_mult                        10
% 0.69/1.03  
% 0.69/1.03  ------ Debug Options
% 0.69/1.03  
% 0.69/1.03  --dbg_backtrace                         false
% 0.69/1.03  --dbg_dump_prop_clauses                 false
% 0.69/1.03  --dbg_dump_prop_clauses_file            -
% 0.69/1.03  --dbg_out_stat                          false
% 0.69/1.03  ------ Parsing...
% 0.69/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.69/1.03  ------ Proving...
% 0.69/1.03  ------ Problem Properties 
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  clauses                                 17
% 0.69/1.03  conjectures                             1
% 0.69/1.03  EPR                                     3
% 0.69/1.03  Horn                                    13
% 0.69/1.03  unary                                   6
% 0.69/1.03  binary                                  4
% 0.69/1.03  lits                                    37
% 0.69/1.03  lits eq                                 12
% 0.69/1.03  fd_pure                                 0
% 0.69/1.03  fd_pseudo                               0
% 0.69/1.03  fd_cond                                 0
% 0.69/1.03  fd_pseudo_cond                          0
% 0.69/1.03  AC symbols                              0
% 0.69/1.03  
% 0.69/1.03  ------ Schedule dynamic 5 is on 
% 0.69/1.03  
% 0.69/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  ------ 
% 0.69/1.03  Current options:
% 0.69/1.03  ------ 
% 0.69/1.03  
% 0.69/1.03  ------ Input Options
% 0.69/1.03  
% 0.69/1.03  --out_options                           all
% 0.69/1.03  --tptp_safe_out                         true
% 0.69/1.03  --problem_path                          ""
% 0.69/1.03  --include_path                          ""
% 0.69/1.03  --clausifier                            res/vclausify_rel
% 0.69/1.03  --clausifier_options                    --mode clausify
% 0.69/1.03  --stdin                                 false
% 0.69/1.03  --stats_out                             all
% 0.69/1.03  
% 0.69/1.03  ------ General Options
% 0.69/1.03  
% 0.69/1.03  --fof                                   false
% 0.69/1.03  --time_out_real                         305.
% 0.69/1.03  --time_out_virtual                      -1.
% 0.69/1.03  --symbol_type_check                     false
% 0.69/1.03  --clausify_out                          false
% 0.69/1.03  --sig_cnt_out                           false
% 0.69/1.03  --trig_cnt_out                          false
% 0.69/1.03  --trig_cnt_out_tolerance                1.
% 0.69/1.03  --trig_cnt_out_sk_spl                   false
% 0.69/1.03  --abstr_cl_out                          false
% 0.69/1.03  
% 0.69/1.03  ------ Global Options
% 0.69/1.03  
% 0.69/1.03  --schedule                              default
% 0.69/1.03  --add_important_lit                     false
% 0.69/1.03  --prop_solver_per_cl                    1000
% 0.69/1.03  --min_unsat_core                        false
% 0.69/1.03  --soft_assumptions                      false
% 0.69/1.03  --soft_lemma_size                       3
% 0.69/1.03  --prop_impl_unit_size                   0
% 0.69/1.03  --prop_impl_unit                        []
% 0.69/1.03  --share_sel_clauses                     true
% 0.69/1.03  --reset_solvers                         false
% 0.69/1.03  --bc_imp_inh                            [conj_cone]
% 0.69/1.03  --conj_cone_tolerance                   3.
% 0.69/1.03  --extra_neg_conj                        none
% 0.69/1.03  --large_theory_mode                     true
% 0.69/1.03  --prolific_symb_bound                   200
% 0.69/1.03  --lt_threshold                          2000
% 0.69/1.03  --clause_weak_htbl                      true
% 0.69/1.03  --gc_record_bc_elim                     false
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing Options
% 0.69/1.03  
% 0.69/1.03  --preprocessing_flag                    true
% 0.69/1.03  --time_out_prep_mult                    0.1
% 0.69/1.03  --splitting_mode                        input
% 0.69/1.03  --splitting_grd                         true
% 0.69/1.03  --splitting_cvd                         false
% 0.69/1.03  --splitting_cvd_svl                     false
% 0.69/1.03  --splitting_nvd                         32
% 0.69/1.03  --sub_typing                            true
% 0.69/1.03  --prep_gs_sim                           true
% 0.69/1.03  --prep_unflatten                        true
% 0.69/1.03  --prep_res_sim                          true
% 0.69/1.03  --prep_upred                            true
% 0.69/1.03  --prep_sem_filter                       exhaustive
% 0.69/1.03  --prep_sem_filter_out                   false
% 0.69/1.03  --pred_elim                             true
% 0.69/1.03  --res_sim_input                         true
% 0.69/1.03  --eq_ax_congr_red                       true
% 0.69/1.03  --pure_diseq_elim                       true
% 0.69/1.03  --brand_transform                       false
% 0.69/1.03  --non_eq_to_eq                          false
% 0.69/1.03  --prep_def_merge                        true
% 0.69/1.03  --prep_def_merge_prop_impl              false
% 0.69/1.03  --prep_def_merge_mbd                    true
% 0.69/1.03  --prep_def_merge_tr_red                 false
% 0.69/1.03  --prep_def_merge_tr_cl                  false
% 0.69/1.03  --smt_preprocessing                     true
% 0.69/1.03  --smt_ac_axioms                         fast
% 0.69/1.03  --preprocessed_out                      false
% 0.69/1.03  --preprocessed_stats                    false
% 0.69/1.03  
% 0.69/1.03  ------ Abstraction refinement Options
% 0.69/1.03  
% 0.69/1.03  --abstr_ref                             []
% 0.69/1.03  --abstr_ref_prep                        false
% 0.69/1.03  --abstr_ref_until_sat                   false
% 0.69/1.03  --abstr_ref_sig_restrict                funpre
% 0.69/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 0.69/1.03  --abstr_ref_under                       []
% 0.69/1.03  
% 0.69/1.03  ------ SAT Options
% 0.69/1.03  
% 0.69/1.03  --sat_mode                              false
% 0.69/1.03  --sat_fm_restart_options                ""
% 0.69/1.03  --sat_gr_def                            false
% 0.69/1.03  --sat_epr_types                         true
% 0.69/1.03  --sat_non_cyclic_types                  false
% 0.69/1.03  --sat_finite_models                     false
% 0.69/1.03  --sat_fm_lemmas                         false
% 0.69/1.03  --sat_fm_prep                           false
% 0.69/1.03  --sat_fm_uc_incr                        true
% 0.69/1.03  --sat_out_model                         small
% 0.69/1.03  --sat_out_clauses                       false
% 0.69/1.03  
% 0.69/1.03  ------ QBF Options
% 0.69/1.03  
% 0.69/1.03  --qbf_mode                              false
% 0.69/1.03  --qbf_elim_univ                         false
% 0.69/1.03  --qbf_dom_inst                          none
% 0.69/1.03  --qbf_dom_pre_inst                      false
% 0.69/1.03  --qbf_sk_in                             false
% 0.69/1.03  --qbf_pred_elim                         true
% 0.69/1.03  --qbf_split                             512
% 0.69/1.03  
% 0.69/1.03  ------ BMC1 Options
% 0.69/1.03  
% 0.69/1.03  --bmc1_incremental                      false
% 0.69/1.03  --bmc1_axioms                           reachable_all
% 0.69/1.03  --bmc1_min_bound                        0
% 0.69/1.03  --bmc1_max_bound                        -1
% 0.69/1.03  --bmc1_max_bound_default                -1
% 0.69/1.03  --bmc1_symbol_reachability              true
% 0.69/1.03  --bmc1_property_lemmas                  false
% 0.69/1.03  --bmc1_k_induction                      false
% 0.69/1.03  --bmc1_non_equiv_states                 false
% 0.69/1.03  --bmc1_deadlock                         false
% 0.69/1.03  --bmc1_ucm                              false
% 0.69/1.03  --bmc1_add_unsat_core                   none
% 0.69/1.03  --bmc1_unsat_core_children              false
% 0.69/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 0.69/1.03  --bmc1_out_stat                         full
% 0.69/1.03  --bmc1_ground_init                      false
% 0.69/1.03  --bmc1_pre_inst_next_state              false
% 0.69/1.03  --bmc1_pre_inst_state                   false
% 0.69/1.03  --bmc1_pre_inst_reach_state             false
% 0.69/1.03  --bmc1_out_unsat_core                   false
% 0.69/1.03  --bmc1_aig_witness_out                  false
% 0.69/1.03  --bmc1_verbose                          false
% 0.69/1.03  --bmc1_dump_clauses_tptp                false
% 0.69/1.03  --bmc1_dump_unsat_core_tptp             false
% 0.69/1.03  --bmc1_dump_file                        -
% 0.69/1.03  --bmc1_ucm_expand_uc_limit              128
% 0.69/1.03  --bmc1_ucm_n_expand_iterations          6
% 0.69/1.03  --bmc1_ucm_extend_mode                  1
% 0.69/1.03  --bmc1_ucm_init_mode                    2
% 0.69/1.03  --bmc1_ucm_cone_mode                    none
% 0.69/1.03  --bmc1_ucm_reduced_relation_type        0
% 0.69/1.03  --bmc1_ucm_relax_model                  4
% 0.69/1.03  --bmc1_ucm_full_tr_after_sat            true
% 0.69/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 0.69/1.03  --bmc1_ucm_layered_model                none
% 0.69/1.03  --bmc1_ucm_max_lemma_size               10
% 0.69/1.03  
% 0.69/1.03  ------ AIG Options
% 0.69/1.03  
% 0.69/1.03  --aig_mode                              false
% 0.69/1.03  
% 0.69/1.03  ------ Instantiation Options
% 0.69/1.03  
% 0.69/1.03  --instantiation_flag                    true
% 0.69/1.03  --inst_sos_flag                         false
% 0.69/1.03  --inst_sos_phase                        true
% 0.69/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.69/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.69/1.03  --inst_lit_sel_side                     none
% 0.69/1.03  --inst_solver_per_active                1400
% 0.69/1.03  --inst_solver_calls_frac                1.
% 0.69/1.03  --inst_passive_queue_type               priority_queues
% 0.69/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.69/1.03  --inst_passive_queues_freq              [25;2]
% 0.69/1.03  --inst_dismatching                      true
% 0.69/1.03  --inst_eager_unprocessed_to_passive     true
% 0.69/1.03  --inst_prop_sim_given                   true
% 0.69/1.03  --inst_prop_sim_new                     false
% 0.69/1.03  --inst_subs_new                         false
% 0.69/1.03  --inst_eq_res_simp                      false
% 0.69/1.03  --inst_subs_given                       false
% 0.69/1.03  --inst_orphan_elimination               true
% 0.69/1.03  --inst_learning_loop_flag               true
% 0.69/1.03  --inst_learning_start                   3000
% 0.69/1.03  --inst_learning_factor                  2
% 0.69/1.03  --inst_start_prop_sim_after_learn       3
% 0.69/1.03  --inst_sel_renew                        solver
% 0.69/1.03  --inst_lit_activity_flag                true
% 0.69/1.03  --inst_restr_to_given                   false
% 0.69/1.03  --inst_activity_threshold               500
% 0.69/1.03  --inst_out_proof                        true
% 0.69/1.03  
% 0.69/1.03  ------ Resolution Options
% 0.69/1.03  
% 0.69/1.03  --resolution_flag                       false
% 0.69/1.03  --res_lit_sel                           adaptive
% 0.69/1.03  --res_lit_sel_side                      none
% 0.69/1.03  --res_ordering                          kbo
% 0.69/1.03  --res_to_prop_solver                    active
% 0.69/1.03  --res_prop_simpl_new                    false
% 0.69/1.03  --res_prop_simpl_given                  true
% 0.69/1.03  --res_passive_queue_type                priority_queues
% 0.69/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.69/1.03  --res_passive_queues_freq               [15;5]
% 0.69/1.03  --res_forward_subs                      full
% 0.69/1.03  --res_backward_subs                     full
% 0.69/1.03  --res_forward_subs_resolution           true
% 0.69/1.03  --res_backward_subs_resolution          true
% 0.69/1.03  --res_orphan_elimination                true
% 0.69/1.03  --res_time_limit                        2.
% 0.69/1.03  --res_out_proof                         true
% 0.69/1.03  
% 0.69/1.03  ------ Superposition Options
% 0.69/1.03  
% 0.69/1.03  --superposition_flag                    true
% 0.69/1.03  --sup_passive_queue_type                priority_queues
% 0.69/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.69/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.69/1.03  --demod_completeness_check              fast
% 0.69/1.03  --demod_use_ground                      true
% 0.69/1.03  --sup_to_prop_solver                    passive
% 0.69/1.03  --sup_prop_simpl_new                    true
% 0.69/1.03  --sup_prop_simpl_given                  true
% 0.69/1.03  --sup_fun_splitting                     false
% 0.69/1.03  --sup_smt_interval                      50000
% 0.69/1.03  
% 0.69/1.03  ------ Superposition Simplification Setup
% 0.69/1.03  
% 0.69/1.03  --sup_indices_passive                   []
% 0.69/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.69/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.69/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_full_bw                           [BwDemod]
% 0.69/1.03  --sup_immed_triv                        [TrivRules]
% 0.69/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.69/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_immed_bw_main                     []
% 0.69/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.69/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.69/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.69/1.03  
% 0.69/1.03  ------ Combination Options
% 0.69/1.03  
% 0.69/1.03  --comb_res_mult                         3
% 0.69/1.03  --comb_sup_mult                         2
% 0.69/1.03  --comb_inst_mult                        10
% 0.69/1.03  
% 0.69/1.03  ------ Debug Options
% 0.69/1.03  
% 0.69/1.03  --dbg_backtrace                         false
% 0.69/1.03  --dbg_dump_prop_clauses                 false
% 0.69/1.03  --dbg_dump_prop_clauses_file            -
% 0.69/1.03  --dbg_out_stat                          false
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  ------ Proving...
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  % SZS status Theorem for theBenchmark.p
% 0.69/1.03  
% 0.69/1.03   Resolution empty clause
% 0.69/1.03  
% 0.69/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.69/1.03  
% 0.69/1.03  fof(f11,conjecture,(
% 0.69/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f12,negated_conjecture,(
% 0.69/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.69/1.03    inference(negated_conjecture,[],[f11])).
% 0.69/1.03  
% 0.69/1.03  fof(f23,plain,(
% 0.69/1.03    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.69/1.03    inference(ennf_transformation,[],[f12])).
% 0.69/1.03  
% 0.69/1.03  fof(f24,plain,(
% 0.69/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.03    inference(flattening,[],[f23])).
% 0.69/1.03  
% 0.69/1.03  fof(f29,plain,(
% 0.69/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | (~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0))) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.03    inference(nnf_transformation,[],[f24])).
% 0.69/1.03  
% 0.69/1.03  fof(f30,plain,(
% 0.69/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.69/1.03    inference(flattening,[],[f29])).
% 0.69/1.03  
% 0.69/1.03  fof(f33,plain,(
% 0.69/1.03    ( ! [X0,X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) => (k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))) )),
% 0.69/1.03    introduced(choice_axiom,[])).
% 0.69/1.03  
% 0.69/1.03  fof(f32,plain,(
% 0.69/1.03    ( ! [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(sK2,u1_struct_0(X0)))) )),
% 0.69/1.03    introduced(choice_axiom,[])).
% 0.69/1.03  
% 0.69/1.03  fof(f31,plain,(
% 0.69/1.03    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,X0) | ~v3_pre_topc(X3,X0)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : (((r2_hidden(X3,X2) | ~r2_hidden(X1,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(X1,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.69/1.03    introduced(choice_axiom,[])).
% 0.69/1.03  
% 0.69/1.03  fof(f34,plain,(
% 0.69/1.03    ((k1_xboole_0 = sK3 & ! [X3] : (((r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1)) & ((r2_hidden(sK2,X3) & v4_pre_topc(X3,sK1) & v3_pre_topc(X3,sK1)) | ~r2_hidden(X3,sK3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f30,f33,f32,f31])).
% 0.69/1.03  
% 0.69/1.03  fof(f49,plain,(
% 0.69/1.03    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f54,plain,(
% 0.69/1.03    ( ! [X3] : (r2_hidden(X3,sK3) | ~r2_hidden(sK2,X3) | ~v4_pre_topc(X3,sK1) | ~v3_pre_topc(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f8,axiom,(
% 0.69/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f17,plain,(
% 0.69/1.03    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.69/1.03    inference(ennf_transformation,[],[f8])).
% 0.69/1.03  
% 0.69/1.03  fof(f18,plain,(
% 0.69/1.03    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.69/1.03    inference(flattening,[],[f17])).
% 0.69/1.03  
% 0.69/1.03  fof(f43,plain,(
% 0.69/1.03    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f18])).
% 0.69/1.03  
% 0.69/1.03  fof(f47,plain,(
% 0.69/1.03    v2_pre_topc(sK1)),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f48,plain,(
% 0.69/1.03    l1_pre_topc(sK1)),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f10,axiom,(
% 0.69/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f21,plain,(
% 0.69/1.03    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.69/1.03    inference(ennf_transformation,[],[f10])).
% 0.69/1.03  
% 0.69/1.03  fof(f22,plain,(
% 0.69/1.03    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.69/1.03    inference(flattening,[],[f21])).
% 0.69/1.03  
% 0.69/1.03  fof(f45,plain,(
% 0.69/1.03    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f22])).
% 0.69/1.03  
% 0.69/1.03  fof(f55,plain,(
% 0.69/1.03    k1_xboole_0 = sK3),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f7,axiom,(
% 0.69/1.03    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f16,plain,(
% 0.69/1.03    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.69/1.03    inference(ennf_transformation,[],[f7])).
% 0.69/1.03  
% 0.69/1.03  fof(f42,plain,(
% 0.69/1.03    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f16])).
% 0.69/1.03  
% 0.69/1.03  fof(f6,axiom,(
% 0.69/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f15,plain,(
% 0.69/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.69/1.03    inference(ennf_transformation,[],[f6])).
% 0.69/1.03  
% 0.69/1.03  fof(f41,plain,(
% 0.69/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f15])).
% 0.69/1.03  
% 0.69/1.03  fof(f9,axiom,(
% 0.69/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f19,plain,(
% 0.69/1.03    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.69/1.03    inference(ennf_transformation,[],[f9])).
% 0.69/1.03  
% 0.69/1.03  fof(f20,plain,(
% 0.69/1.03    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.69/1.03    inference(flattening,[],[f19])).
% 0.69/1.03  
% 0.69/1.03  fof(f44,plain,(
% 0.69/1.03    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f20])).
% 0.69/1.03  
% 0.69/1.03  fof(f46,plain,(
% 0.69/1.03    ~v2_struct_0(sK1)),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f5,axiom,(
% 0.69/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f13,plain,(
% 0.69/1.03    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.69/1.03    inference(ennf_transformation,[],[f5])).
% 0.69/1.03  
% 0.69/1.03  fof(f14,plain,(
% 0.69/1.03    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.69/1.03    inference(flattening,[],[f13])).
% 0.69/1.03  
% 0.69/1.03  fof(f40,plain,(
% 0.69/1.03    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f14])).
% 0.69/1.03  
% 0.69/1.03  fof(f4,axiom,(
% 0.69/1.03    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f39,plain,(
% 0.69/1.03    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.69/1.03    inference(cnf_transformation,[],[f4])).
% 0.69/1.03  
% 0.69/1.03  fof(f3,axiom,(
% 0.69/1.03    ! [X0] : k2_subset_1(X0) = X0),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f38,plain,(
% 0.69/1.03    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.69/1.03    inference(cnf_transformation,[],[f3])).
% 0.69/1.03  
% 0.69/1.03  fof(f53,plain,(
% 0.69/1.03    ( ! [X3] : (r2_hidden(sK2,X3) | ~r2_hidden(X3,sK3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.69/1.03    inference(cnf_transformation,[],[f34])).
% 0.69/1.03  
% 0.69/1.03  fof(f1,axiom,(
% 0.69/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f25,plain,(
% 0.69/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.69/1.03    inference(nnf_transformation,[],[f1])).
% 0.69/1.03  
% 0.69/1.03  fof(f26,plain,(
% 0.69/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.69/1.03    inference(rectify,[],[f25])).
% 0.69/1.03  
% 0.69/1.03  fof(f27,plain,(
% 0.69/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 0.69/1.03    introduced(choice_axiom,[])).
% 0.69/1.03  
% 0.69/1.03  fof(f28,plain,(
% 0.69/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.69/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 0.69/1.03  
% 0.69/1.03  fof(f35,plain,(
% 0.69/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.69/1.03    inference(cnf_transformation,[],[f28])).
% 0.69/1.03  
% 0.69/1.03  fof(f2,axiom,(
% 0.69/1.03    v1_xboole_0(k1_xboole_0)),
% 0.69/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.69/1.03  
% 0.69/1.03  fof(f37,plain,(
% 0.69/1.03    v1_xboole_0(k1_xboole_0)),
% 0.69/1.03    inference(cnf_transformation,[],[f2])).
% 0.69/1.03  
% 0.69/1.03  cnf(c_17,negated_conjecture,
% 0.69/1.03      ( m1_subset_1(sK2,u1_struct_0(sK1)) ),
% 0.69/1.03      inference(cnf_transformation,[],[f49]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_12,negated_conjecture,
% 0.69/1.03      ( ~ v3_pre_topc(X0,sK1)
% 0.69/1.03      | ~ v4_pre_topc(X0,sK1)
% 0.69/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.69/1.03      | r2_hidden(X0,sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f54]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_8,plain,
% 0.69/1.03      ( v4_pre_topc(k2_struct_0(X0),X0)
% 0.69/1.03      | ~ v2_pre_topc(X0)
% 0.69/1.03      | ~ l1_pre_topc(X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f43]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_19,negated_conjecture,
% 0.69/1.03      ( v2_pre_topc(sK1) ),
% 0.69/1.03      inference(cnf_transformation,[],[f47]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_255,plain,
% 0.69/1.03      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK1 != X0 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_8,c_19]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_256,plain,
% 0.69/1.03      ( v4_pre_topc(k2_struct_0(sK1),sK1) | ~ l1_pre_topc(sK1) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_255]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_18,negated_conjecture,
% 0.69/1.03      ( l1_pre_topc(sK1) ),
% 0.69/1.03      inference(cnf_transformation,[],[f48]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_45,plain,
% 0.69/1.03      ( v4_pre_topc(k2_struct_0(sK1),sK1)
% 0.69/1.03      | ~ v2_pre_topc(sK1)
% 0.69/1.03      | ~ l1_pre_topc(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_258,plain,
% 0.69/1.03      ( v4_pre_topc(k2_struct_0(sK1),sK1) ),
% 0.69/1.03      inference(global_propositional_subsumption,
% 0.69/1.03                [status(thm)],
% 0.69/1.03                [c_256,c_19,c_18,c_45]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_343,plain,
% 0.69/1.03      ( ~ v3_pre_topc(X0,sK1)
% 0.69/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.69/1.03      | r2_hidden(X0,sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,X0)
% 0.69/1.03      | k2_struct_0(sK1) != X0
% 0.69/1.03      | sK1 != sK1 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_258]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_344,plain,
% 0.69/1.03      ( ~ v3_pre_topc(k2_struct_0(sK1),sK1)
% 0.69/1.03      | ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.69/1.03      | r2_hidden(k2_struct_0(sK1),sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_343]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_10,plain,
% 0.69/1.03      ( v3_pre_topc(k2_struct_0(X0),X0)
% 0.69/1.03      | ~ v2_pre_topc(X0)
% 0.69/1.03      | ~ l1_pre_topc(X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f45]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_39,plain,
% 0.69/1.03      ( v3_pre_topc(k2_struct_0(sK1),sK1)
% 0.69/1.03      | ~ v2_pre_topc(sK1)
% 0.69/1.03      | ~ l1_pre_topc(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_10]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_346,plain,
% 0.69/1.03      ( ~ m1_subset_1(k2_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
% 0.69/1.03      | r2_hidden(k2_struct_0(sK1),sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,k2_struct_0(sK1)) ),
% 0.69/1.03      inference(global_propositional_subsumption,
% 0.69/1.03                [status(thm)],
% 0.69/1.03                [c_344,c_19,c_18,c_39]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_469,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 0.69/1.03      | k2_struct_0(sK1) != sK2
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK1) ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_346]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1127,plain,
% 0.69/1.03      ( k2_struct_0(sK1) != sK2
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != u1_struct_0(sK1)
% 0.69/1.03      | r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 0.69/1.03      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_469]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_11,negated_conjecture,
% 0.69/1.03      ( k1_xboole_0 = sK3 ),
% 0.69/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_7,plain,
% 0.69/1.03      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f42]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_6,plain,
% 0.69/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f41]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_230,plain,
% 0.69/1.03      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.69/1.03      inference(resolution,[status(thm)],[c_7,c_6]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_270,plain,
% 0.69/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_230,c_18]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_271,plain,
% 0.69/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_270]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1206,plain,
% 0.69/1.03      ( k2_struct_0(sK1) != sK2
% 0.69/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
% 0.69/1.03      | r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
% 0.69/1.03      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top ),
% 0.69/1.03      inference(light_normalisation,[status(thm)],[c_1127,c_11,c_271]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_9,plain,
% 0.69/1.03      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 0.69/1.03      inference(cnf_transformation,[],[f44]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_20,negated_conjecture,
% 0.69/1.03      ( ~ v2_struct_0(sK1) ),
% 0.69/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_217,plain,
% 0.69/1.03      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_218,plain,
% 0.69/1.03      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_217]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_42,plain,
% 0.69/1.03      ( v2_struct_0(sK1)
% 0.69/1.03      | ~ l1_struct_0(sK1)
% 0.69/1.03      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_48,plain,
% 0.69/1.03      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_7]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_220,plain,
% 0.69/1.03      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 0.69/1.03      inference(global_propositional_subsumption,
% 0.69/1.03                [status(thm)],
% 0.69/1.03                [c_218,c_20,c_18,c_42,c_48]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_5,plain,
% 0.69/1.03      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 0.69/1.03      inference(cnf_transformation,[],[f40]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_418,plain,
% 0.69/1.03      ( r2_hidden(X0,X1)
% 0.69/1.03      | v1_xboole_0(X1)
% 0.69/1.03      | u1_struct_0(sK1) != X1
% 0.69/1.03      | sK2 != X0 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_17]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_419,plain,
% 0.69/1.03      ( r2_hidden(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_418]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_604,plain,
% 0.69/1.03      ( r2_hidden(sK2,u1_struct_0(sK1))
% 0.69/1.03      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_220,c_419]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_51,plain,
% 0.69/1.03      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_606,plain,
% 0.69/1.03      ( r2_hidden(sK2,u1_struct_0(sK1)) ),
% 0.69/1.03      inference(global_propositional_subsumption,
% 0.69/1.03                [status(thm)],
% 0.69/1.03                [c_604,c_18,c_48,c_51]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1126,plain,
% 0.69/1.03      ( r2_hidden(sK2,u1_struct_0(sK1)) = iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1148,plain,
% 0.69/1.03      ( r2_hidden(sK2,k2_struct_0(sK1)) = iProver_top ),
% 0.69/1.03      inference(light_normalisation,[status(thm)],[c_1126,c_271]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1211,plain,
% 0.69/1.03      ( k2_struct_0(sK1) != sK2
% 0.69/1.03      | k1_zfmisc_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
% 0.69/1.03      | r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 0.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1206,c_1148]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_4,plain,
% 0.69/1.03      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 0.69/1.03      inference(cnf_transformation,[],[f39]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_391,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 0.69/1.03      | k2_subset_1(X0) != k2_struct_0(sK1) ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_346]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_878,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),sK3)
% 0.69/1.03      | ~ r2_hidden(sK2,k2_struct_0(sK1))
% 0.69/1.03      | sP0_iProver_split ),
% 0.69/1.03      inference(splitting,
% 0.69/1.03                [splitting(split),new_symbols(definition,[])],
% 0.69/1.03                [c_391]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1132,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),sK3) = iProver_top
% 0.69/1.03      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 0.69/1.03      | sP0_iProver_split = iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_878]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1171,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
% 0.69/1.03      | r2_hidden(sK2,k2_struct_0(sK1)) != iProver_top
% 0.69/1.03      | sP0_iProver_split = iProver_top ),
% 0.69/1.03      inference(light_normalisation,[status(thm)],[c_1132,c_11]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1175,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top
% 0.69/1.03      | sP0_iProver_split = iProver_top ),
% 0.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1171,c_1148]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_3,plain,
% 0.69/1.03      ( k2_subset_1(X0) = X0 ),
% 0.69/1.03      inference(cnf_transformation,[],[f38]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1260,plain,
% 0.69/1.03      ( k2_subset_1(k2_struct_0(sK1)) = k2_struct_0(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_877,plain,
% 0.69/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 0.69/1.03      | k2_subset_1(X0) != k2_struct_0(sK1)
% 0.69/1.03      | ~ sP0_iProver_split ),
% 0.69/1.03      inference(splitting,
% 0.69/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 0.69/1.03                [c_391]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1261,plain,
% 0.69/1.03      ( ~ sP0_iProver_split
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(k2_struct_0(sK1))
% 0.69/1.03      | k2_subset_1(k2_struct_0(sK1)) != k2_struct_0(sK1) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_877]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1262,plain,
% 0.69/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(k2_struct_0(sK1))
% 0.69/1.03      | k2_subset_1(k2_struct_0(sK1)) != k2_struct_0(sK1)
% 0.69/1.03      | sP0_iProver_split != iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_1261]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_884,plain,
% 0.69/1.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 0.69/1.03      theory(equality) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1344,plain,
% 0.69/1.03      ( u1_struct_0(sK1) != k2_struct_0(sK1)
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) = k1_zfmisc_1(k2_struct_0(sK1)) ),
% 0.69/1.03      inference(instantiation,[status(thm)],[c_884]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1569,plain,
% 0.69/1.03      ( r2_hidden(k2_struct_0(sK1),k1_xboole_0) = iProver_top ),
% 0.69/1.03      inference(global_propositional_subsumption,
% 0.69/1.03                [status(thm)],
% 0.69/1.03                [c_1211,c_18,c_48,c_51,c_1175,c_1260,c_1262,c_1344]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_13,negated_conjecture,
% 0.69/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
% 0.69/1.03      | ~ r2_hidden(X0,sK3)
% 0.69/1.03      | r2_hidden(sK2,X0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f53]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_376,plain,
% 0.69/1.03      ( ~ r2_hidden(X0,sK3)
% 0.69/1.03      | r2_hidden(sK2,X0)
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X1)
% 0.69/1.03      | k2_subset_1(X1) != X0 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_377,plain,
% 0.69/1.03      ( ~ r2_hidden(k2_subset_1(X0),sK3)
% 0.69/1.03      | r2_hidden(sK2,k2_subset_1(X0))
% 0.69/1.03      | k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_376]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1134,plain,
% 0.69/1.03      ( k1_zfmisc_1(u1_struct_0(sK1)) != k1_zfmisc_1(X0)
% 0.69/1.03      | r2_hidden(k2_subset_1(X0),sK3) != iProver_top
% 0.69/1.03      | r2_hidden(sK2,k2_subset_1(X0)) = iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1199,plain,
% 0.69/1.03      ( k1_zfmisc_1(k2_struct_0(sK1)) != k1_zfmisc_1(X0)
% 0.69/1.03      | r2_hidden(X0,k1_xboole_0) != iProver_top
% 0.69/1.03      | r2_hidden(sK2,X0) = iProver_top ),
% 0.69/1.03      inference(light_normalisation,[status(thm)],[c_1134,c_3,c_11,c_271]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1,plain,
% 0.69/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 0.69/1.03      inference(cnf_transformation,[],[f35]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_2,plain,
% 0.69/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 0.69/1.03      inference(cnf_transformation,[],[f37]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_307,plain,
% 0.69/1.03      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 0.69/1.03      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_308,plain,
% 0.69/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 0.69/1.03      inference(unflattening,[status(thm)],[c_307]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_309,plain,
% 0.69/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.69/1.03      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1283,plain,
% 0.69/1.03      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 0.69/1.03      inference(global_propositional_subsumption,[status(thm)],[c_1199,c_309]) ).
% 0.69/1.03  
% 0.69/1.03  cnf(c_1574,plain,
% 0.69/1.03      ( $false ),
% 0.69/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_1569,c_1283]) ).
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.69/1.03  
% 0.69/1.03  ------                               Statistics
% 0.69/1.03  
% 0.69/1.03  ------ General
% 0.69/1.03  
% 0.69/1.03  abstr_ref_over_cycles:                  0
% 0.69/1.03  abstr_ref_under_cycles:                 0
% 0.69/1.03  gc_basic_clause_elim:                   0
% 0.69/1.03  forced_gc_time:                         0
% 0.69/1.03  parsing_time:                           0.008
% 0.69/1.03  unif_index_cands_time:                  0.
% 0.69/1.03  unif_index_add_time:                    0.
% 0.69/1.03  orderings_time:                         0.
% 0.69/1.03  out_proof_time:                         0.01
% 0.69/1.03  total_time:                             0.071
% 0.69/1.03  num_of_symbols:                         47
% 0.69/1.03  num_of_terms:                           775
% 0.69/1.03  
% 0.69/1.03  ------ Preprocessing
% 0.69/1.03  
% 0.69/1.03  num_of_splits:                          1
% 0.69/1.03  num_of_split_atoms:                     1
% 0.69/1.03  num_of_reused_defs:                     0
% 0.69/1.03  num_eq_ax_congr_red:                    8
% 0.69/1.03  num_of_sem_filtered_clauses:            1
% 0.69/1.03  num_of_subtypes:                        0
% 0.69/1.03  monotx_restored_types:                  0
% 0.69/1.03  sat_num_of_epr_types:                   0
% 0.69/1.03  sat_num_of_non_cyclic_types:            0
% 0.69/1.03  sat_guarded_non_collapsed_types:        0
% 0.69/1.03  num_pure_diseq_elim:                    0
% 0.69/1.03  simp_replaced_by:                       0
% 0.69/1.03  res_preprocessed:                       86
% 0.69/1.03  prep_upred:                             0
% 0.69/1.03  prep_unflattend:                        34
% 0.69/1.03  smt_new_axioms:                         0
% 0.69/1.03  pred_elim_cands:                        2
% 0.69/1.03  pred_elim:                              7
% 0.69/1.03  pred_elim_cl:                           5
% 0.69/1.03  pred_elim_cycles:                       11
% 0.69/1.03  merged_defs:                            0
% 0.69/1.03  merged_defs_ncl:                        0
% 0.69/1.03  bin_hyper_res:                          0
% 0.69/1.03  prep_cycles:                            4
% 0.69/1.03  pred_elim_time:                         0.008
% 0.69/1.03  splitting_time:                         0.
% 0.69/1.03  sem_filter_time:                        0.
% 0.69/1.03  monotx_time:                            0.
% 0.69/1.03  subtype_inf_time:                       0.
% 0.69/1.03  
% 0.69/1.03  ------ Problem properties
% 0.69/1.03  
% 0.69/1.03  clauses:                                17
% 0.69/1.03  conjectures:                            1
% 0.69/1.03  epr:                                    3
% 0.69/1.03  horn:                                   13
% 0.69/1.03  ground:                                 11
% 0.69/1.03  unary:                                  6
% 0.69/1.03  binary:                                 4
% 0.69/1.03  lits:                                   37
% 0.69/1.03  lits_eq:                                12
% 0.69/1.03  fd_pure:                                0
% 0.69/1.03  fd_pseudo:                              0
% 0.69/1.03  fd_cond:                                0
% 0.69/1.03  fd_pseudo_cond:                         0
% 0.69/1.03  ac_symbols:                             0
% 0.69/1.03  
% 0.69/1.03  ------ Propositional Solver
% 0.69/1.03  
% 0.69/1.03  prop_solver_calls:                      25
% 0.69/1.03  prop_fast_solver_calls:                 506
% 0.69/1.03  smt_solver_calls:                       0
% 0.69/1.03  smt_fast_solver_calls:                  0
% 0.69/1.03  prop_num_of_clauses:                    351
% 0.69/1.03  prop_preprocess_simplified:             2243
% 0.69/1.03  prop_fo_subsumed:                       11
% 0.69/1.03  prop_solver_time:                       0.
% 0.69/1.03  smt_solver_time:                        0.
% 0.69/1.03  smt_fast_solver_time:                   0.
% 0.69/1.03  prop_fast_solver_time:                  0.
% 0.69/1.03  prop_unsat_core_time:                   0.
% 0.69/1.03  
% 0.69/1.03  ------ QBF
% 0.69/1.03  
% 0.69/1.03  qbf_q_res:                              0
% 0.69/1.03  qbf_num_tautologies:                    0
% 0.69/1.03  qbf_prep_cycles:                        0
% 0.69/1.03  
% 0.69/1.03  ------ BMC1
% 0.69/1.03  
% 0.69/1.03  bmc1_current_bound:                     -1
% 0.69/1.03  bmc1_last_solved_bound:                 -1
% 0.69/1.03  bmc1_unsat_core_size:                   -1
% 0.69/1.03  bmc1_unsat_core_parents_size:           -1
% 0.69/1.03  bmc1_merge_next_fun:                    0
% 0.69/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.69/1.03  
% 0.69/1.03  ------ Instantiation
% 0.69/1.03  
% 0.69/1.03  inst_num_of_clauses:                    100
% 0.69/1.03  inst_num_in_passive:                    17
% 0.69/1.03  inst_num_in_active:                     64
% 0.69/1.03  inst_num_in_unprocessed:                19
% 0.69/1.03  inst_num_of_loops:                      70
% 0.69/1.03  inst_num_of_learning_restarts:          0
% 0.69/1.03  inst_num_moves_active_passive:          4
% 0.69/1.03  inst_lit_activity:                      0
% 0.69/1.03  inst_lit_activity_moves:                0
% 0.69/1.03  inst_num_tautologies:                   0
% 0.69/1.03  inst_num_prop_implied:                  0
% 0.69/1.03  inst_num_existing_simplified:           0
% 0.69/1.03  inst_num_eq_res_simplified:             0
% 0.69/1.03  inst_num_child_elim:                    0
% 0.69/1.03  inst_num_of_dismatching_blockings:      4
% 0.69/1.03  inst_num_of_non_proper_insts:           58
% 0.69/1.03  inst_num_of_duplicates:                 0
% 0.69/1.03  inst_inst_num_from_inst_to_res:         0
% 0.69/1.03  inst_dismatching_checking_time:         0.
% 0.69/1.03  
% 0.69/1.03  ------ Resolution
% 0.69/1.03  
% 0.69/1.03  res_num_of_clauses:                     0
% 0.69/1.03  res_num_in_passive:                     0
% 0.69/1.03  res_num_in_active:                      0
% 0.69/1.03  res_num_of_loops:                       90
% 0.69/1.03  res_forward_subset_subsumed:            10
% 0.69/1.03  res_backward_subset_subsumed:           1
% 0.69/1.03  res_forward_subsumed:                   0
% 0.69/1.03  res_backward_subsumed:                  1
% 0.69/1.03  res_forward_subsumption_resolution:     0
% 0.69/1.03  res_backward_subsumption_resolution:    0
% 0.69/1.03  res_clause_to_clause_subsumption:       44
% 0.69/1.03  res_orphan_elimination:                 0
% 0.69/1.03  res_tautology_del:                      6
% 0.69/1.03  res_num_eq_res_simplified:              0
% 0.69/1.03  res_num_sel_changes:                    0
% 0.69/1.03  res_moves_from_active_to_pass:          0
% 0.69/1.03  
% 0.69/1.03  ------ Superposition
% 0.69/1.03  
% 0.69/1.03  sup_time_total:                         0.
% 0.69/1.03  sup_time_generating:                    0.
% 0.69/1.03  sup_time_sim_full:                      0.
% 0.69/1.03  sup_time_sim_immed:                     0.
% 0.69/1.03  
% 0.69/1.03  sup_num_of_clauses:                     17
% 0.69/1.03  sup_num_in_active:                      13
% 0.69/1.03  sup_num_in_passive:                     4
% 0.69/1.03  sup_num_of_loops:                       13
% 0.69/1.03  sup_fw_superposition:                   3
% 0.69/1.03  sup_bw_superposition:                   2
% 0.69/1.03  sup_immediate_simplified:               0
% 0.69/1.03  sup_given_eliminated:                   0
% 0.69/1.03  comparisons_done:                       0
% 0.69/1.03  comparisons_avoided:                    0
% 0.69/1.03  
% 0.69/1.03  ------ Simplifications
% 0.69/1.03  
% 0.69/1.03  
% 0.69/1.03  sim_fw_subset_subsumed:                 0
% 0.69/1.03  sim_bw_subset_subsumed:                 0
% 0.69/1.03  sim_fw_subsumed:                        1
% 0.69/1.03  sim_bw_subsumed:                        0
% 0.69/1.03  sim_fw_subsumption_res:                 4
% 0.69/1.03  sim_bw_subsumption_res:                 0
% 0.69/1.03  sim_tautology_del:                      2
% 0.69/1.03  sim_eq_tautology_del:                   0
% 0.69/1.03  sim_eq_res_simp:                        0
% 0.69/1.03  sim_fw_demodulated:                     0
% 0.69/1.03  sim_bw_demodulated:                     0
% 0.69/1.03  sim_light_normalised:                   10
% 0.69/1.03  sim_joinable_taut:                      0
% 0.69/1.03  sim_joinable_simp:                      0
% 0.69/1.03  sim_ac_normalised:                      0
% 0.69/1.03  sim_smt_subsumption:                    0
% 0.69/1.03  
%------------------------------------------------------------------------------
