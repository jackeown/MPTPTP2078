%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:21 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 294 expanded)
%              Number of clauses        :   75 ( 111 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   23
%              Number of atoms          :  390 (1003 expanded)
%              Number of equality atoms :  110 ( 174 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f46,f45])).

fof(f72,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v4_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v4_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v4_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f43,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
                    & v4_pre_topc(sK2(X0,X1,X4),X0)
                    & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f62,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1063,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1057,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1058,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1590,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1057,c_1058])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1059,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2047,plain,
    ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1590,c_1059])).

cnf(c_2500,plain,
    ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2047,c_1057])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_12])).

cnf(c_340,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_2508,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2500,c_1053])).

cnf(c_2628,plain,
    ( v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_2508])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1062,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2701,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2628,c_1062])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1060,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1077,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1060,c_6])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1061,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2099,plain,
    ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
    inference(superposition,[status(thm)],[c_1077,c_1061])).

cnf(c_1592,plain,
    ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
    inference(superposition,[status(thm)],[c_1077,c_1058])).

cnf(c_2101,plain,
    ( k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0) ),
    inference(light_normalisation,[status(thm)],[c_2099,c_1592])).

cnf(c_2345,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2101,c_1590])).

cnf(c_2713,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2701,c_2345])).

cnf(c_24,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1055,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1549,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1055,c_1062])).

cnf(c_22,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_15,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_311,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_312,plain,
    ( v4_pre_topc(k2_struct_0(sK3),sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_311])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_314,plain,
    ( v4_pre_topc(k2_struct_0(sK3),sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_312,c_25])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_525,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_25])).

cnf(c_526,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v4_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_656,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | k2_struct_0(sK3) != X1
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_526])).

cnf(c_657,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_656])).

cnf(c_688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) != sK1(sK3,X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_657])).

cnf(c_689,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
    inference(unflattening,[status(thm)],[c_688])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_691,plain,
    ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_689,c_23])).

cnf(c_1051,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4)
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_14,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_297,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_14,c_13])).

cnf(c_427,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_297,c_25])).

cnf(c_428,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_427])).

cnf(c_1115,plain,
    ( k9_subset_1(k2_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4)
    | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1051,c_428])).

cnf(c_1118,plain,
    ( k9_subset_1(k2_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1115,c_1077])).

cnf(c_1606,plain,
    ( k9_subset_1(k2_struct_0(sK3),k1_xboole_0,k2_struct_0(sK3)) != sK1(sK3,k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1549,c_1118])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_17,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_510,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_511,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_510])).

cnf(c_634,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK1(sK3,X0) != X1
    | k1_xboole_0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_511])).

cnf(c_635,plain,
    ( v2_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_xboole_0 = sK1(sK3,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_643,plain,
    ( v2_tex_2(k1_xboole_0,sK3)
    | k1_xboole_0 = sK1(sK3,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_635,c_10])).

cnf(c_702,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0
    | sK3 != sK3
    | sK4 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_643])).

cnf(c_733,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0
    | sK4 != k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_702])).

cnf(c_1607,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1549,c_733])).

cnf(c_1614,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_1607])).

cnf(c_1618,plain,
    ( k9_subset_1(k2_struct_0(sK3),k1_xboole_0,k2_struct_0(sK3)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1606,c_1614])).

cnf(c_1984,plain,
    ( k3_xboole_0(k1_xboole_0,k2_struct_0(sK3)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1592,c_1618])).

cnf(c_2883,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2713,c_1984])).

cnf(c_2886,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_2883])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.72/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.02  
% 2.72/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.72/1.02  
% 2.72/1.02  ------  iProver source info
% 2.72/1.02  
% 2.72/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.72/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.72/1.02  git: non_committed_changes: false
% 2.72/1.02  git: last_make_outside_of_git: false
% 2.72/1.02  
% 2.72/1.02  ------ 
% 2.72/1.02  
% 2.72/1.02  ------ Input Options
% 2.72/1.02  
% 2.72/1.02  --out_options                           all
% 2.72/1.02  --tptp_safe_out                         true
% 2.72/1.02  --problem_path                          ""
% 2.72/1.02  --include_path                          ""
% 2.72/1.02  --clausifier                            res/vclausify_rel
% 2.72/1.02  --clausifier_options                    --mode clausify
% 2.72/1.02  --stdin                                 false
% 2.72/1.02  --stats_out                             all
% 2.72/1.02  
% 2.72/1.02  ------ General Options
% 2.72/1.02  
% 2.72/1.02  --fof                                   false
% 2.72/1.02  --time_out_real                         305.
% 2.72/1.02  --time_out_virtual                      -1.
% 2.72/1.02  --symbol_type_check                     false
% 2.72/1.02  --clausify_out                          false
% 2.72/1.02  --sig_cnt_out                           false
% 2.72/1.02  --trig_cnt_out                          false
% 2.72/1.02  --trig_cnt_out_tolerance                1.
% 2.72/1.02  --trig_cnt_out_sk_spl                   false
% 2.72/1.02  --abstr_cl_out                          false
% 2.72/1.02  
% 2.72/1.02  ------ Global Options
% 2.72/1.02  
% 2.72/1.02  --schedule                              default
% 2.72/1.02  --add_important_lit                     false
% 2.72/1.02  --prop_solver_per_cl                    1000
% 2.72/1.02  --min_unsat_core                        false
% 2.72/1.02  --soft_assumptions                      false
% 2.72/1.02  --soft_lemma_size                       3
% 2.72/1.02  --prop_impl_unit_size                   0
% 2.72/1.02  --prop_impl_unit                        []
% 2.72/1.02  --share_sel_clauses                     true
% 2.72/1.02  --reset_solvers                         false
% 2.72/1.02  --bc_imp_inh                            [conj_cone]
% 2.72/1.02  --conj_cone_tolerance                   3.
% 2.72/1.02  --extra_neg_conj                        none
% 2.72/1.02  --large_theory_mode                     true
% 2.72/1.02  --prolific_symb_bound                   200
% 2.72/1.02  --lt_threshold                          2000
% 2.72/1.02  --clause_weak_htbl                      true
% 2.72/1.02  --gc_record_bc_elim                     false
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing Options
% 2.72/1.02  
% 2.72/1.02  --preprocessing_flag                    true
% 2.72/1.02  --time_out_prep_mult                    0.1
% 2.72/1.02  --splitting_mode                        input
% 2.72/1.02  --splitting_grd                         true
% 2.72/1.02  --splitting_cvd                         false
% 2.72/1.02  --splitting_cvd_svl                     false
% 2.72/1.02  --splitting_nvd                         32
% 2.72/1.02  --sub_typing                            true
% 2.72/1.02  --prep_gs_sim                           true
% 2.72/1.02  --prep_unflatten                        true
% 2.72/1.02  --prep_res_sim                          true
% 2.72/1.02  --prep_upred                            true
% 2.72/1.02  --prep_sem_filter                       exhaustive
% 2.72/1.02  --prep_sem_filter_out                   false
% 2.72/1.02  --pred_elim                             true
% 2.72/1.02  --res_sim_input                         true
% 2.72/1.02  --eq_ax_congr_red                       true
% 2.72/1.02  --pure_diseq_elim                       true
% 2.72/1.02  --brand_transform                       false
% 2.72/1.02  --non_eq_to_eq                          false
% 2.72/1.02  --prep_def_merge                        true
% 2.72/1.02  --prep_def_merge_prop_impl              false
% 2.72/1.02  --prep_def_merge_mbd                    true
% 2.72/1.02  --prep_def_merge_tr_red                 false
% 2.72/1.02  --prep_def_merge_tr_cl                  false
% 2.72/1.02  --smt_preprocessing                     true
% 2.72/1.02  --smt_ac_axioms                         fast
% 2.72/1.02  --preprocessed_out                      false
% 2.72/1.02  --preprocessed_stats                    false
% 2.72/1.02  
% 2.72/1.02  ------ Abstraction refinement Options
% 2.72/1.02  
% 2.72/1.02  --abstr_ref                             []
% 2.72/1.02  --abstr_ref_prep                        false
% 2.72/1.02  --abstr_ref_until_sat                   false
% 2.72/1.02  --abstr_ref_sig_restrict                funpre
% 2.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.02  --abstr_ref_under                       []
% 2.72/1.02  
% 2.72/1.02  ------ SAT Options
% 2.72/1.02  
% 2.72/1.02  --sat_mode                              false
% 2.72/1.02  --sat_fm_restart_options                ""
% 2.72/1.02  --sat_gr_def                            false
% 2.72/1.02  --sat_epr_types                         true
% 2.72/1.02  --sat_non_cyclic_types                  false
% 2.72/1.02  --sat_finite_models                     false
% 2.72/1.02  --sat_fm_lemmas                         false
% 2.72/1.02  --sat_fm_prep                           false
% 2.72/1.02  --sat_fm_uc_incr                        true
% 2.72/1.02  --sat_out_model                         small
% 2.72/1.02  --sat_out_clauses                       false
% 2.72/1.02  
% 2.72/1.02  ------ QBF Options
% 2.72/1.02  
% 2.72/1.02  --qbf_mode                              false
% 2.72/1.02  --qbf_elim_univ                         false
% 2.72/1.02  --qbf_dom_inst                          none
% 2.72/1.02  --qbf_dom_pre_inst                      false
% 2.72/1.02  --qbf_sk_in                             false
% 2.72/1.02  --qbf_pred_elim                         true
% 2.72/1.02  --qbf_split                             512
% 2.72/1.02  
% 2.72/1.02  ------ BMC1 Options
% 2.72/1.02  
% 2.72/1.02  --bmc1_incremental                      false
% 2.72/1.02  --bmc1_axioms                           reachable_all
% 2.72/1.02  --bmc1_min_bound                        0
% 2.72/1.02  --bmc1_max_bound                        -1
% 2.72/1.02  --bmc1_max_bound_default                -1
% 2.72/1.02  --bmc1_symbol_reachability              true
% 2.72/1.02  --bmc1_property_lemmas                  false
% 2.72/1.02  --bmc1_k_induction                      false
% 2.72/1.02  --bmc1_non_equiv_states                 false
% 2.72/1.02  --bmc1_deadlock                         false
% 2.72/1.02  --bmc1_ucm                              false
% 2.72/1.02  --bmc1_add_unsat_core                   none
% 2.72/1.02  --bmc1_unsat_core_children              false
% 2.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.02  --bmc1_out_stat                         full
% 2.72/1.02  --bmc1_ground_init                      false
% 2.72/1.02  --bmc1_pre_inst_next_state              false
% 2.72/1.02  --bmc1_pre_inst_state                   false
% 2.72/1.02  --bmc1_pre_inst_reach_state             false
% 2.72/1.02  --bmc1_out_unsat_core                   false
% 2.72/1.02  --bmc1_aig_witness_out                  false
% 2.72/1.02  --bmc1_verbose                          false
% 2.72/1.02  --bmc1_dump_clauses_tptp                false
% 2.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.02  --bmc1_dump_file                        -
% 2.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.02  --bmc1_ucm_extend_mode                  1
% 2.72/1.02  --bmc1_ucm_init_mode                    2
% 2.72/1.02  --bmc1_ucm_cone_mode                    none
% 2.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.02  --bmc1_ucm_relax_model                  4
% 2.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.02  --bmc1_ucm_layered_model                none
% 2.72/1.02  --bmc1_ucm_max_lemma_size               10
% 2.72/1.02  
% 2.72/1.02  ------ AIG Options
% 2.72/1.02  
% 2.72/1.02  --aig_mode                              false
% 2.72/1.02  
% 2.72/1.02  ------ Instantiation Options
% 2.72/1.02  
% 2.72/1.02  --instantiation_flag                    true
% 2.72/1.02  --inst_sos_flag                         false
% 2.72/1.02  --inst_sos_phase                        true
% 2.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.02  --inst_lit_sel_side                     num_symb
% 2.72/1.02  --inst_solver_per_active                1400
% 2.72/1.02  --inst_solver_calls_frac                1.
% 2.72/1.02  --inst_passive_queue_type               priority_queues
% 2.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.02  --inst_passive_queues_freq              [25;2]
% 2.72/1.02  --inst_dismatching                      true
% 2.72/1.02  --inst_eager_unprocessed_to_passive     true
% 2.72/1.02  --inst_prop_sim_given                   true
% 2.72/1.02  --inst_prop_sim_new                     false
% 2.72/1.02  --inst_subs_new                         false
% 2.72/1.02  --inst_eq_res_simp                      false
% 2.72/1.02  --inst_subs_given                       false
% 2.72/1.02  --inst_orphan_elimination               true
% 2.72/1.02  --inst_learning_loop_flag               true
% 2.72/1.02  --inst_learning_start                   3000
% 2.72/1.02  --inst_learning_factor                  2
% 2.72/1.02  --inst_start_prop_sim_after_learn       3
% 2.72/1.02  --inst_sel_renew                        solver
% 2.72/1.02  --inst_lit_activity_flag                true
% 2.72/1.02  --inst_restr_to_given                   false
% 2.72/1.02  --inst_activity_threshold               500
% 2.72/1.02  --inst_out_proof                        true
% 2.72/1.02  
% 2.72/1.02  ------ Resolution Options
% 2.72/1.02  
% 2.72/1.02  --resolution_flag                       true
% 2.72/1.02  --res_lit_sel                           adaptive
% 2.72/1.02  --res_lit_sel_side                      none
% 2.72/1.02  --res_ordering                          kbo
% 2.72/1.02  --res_to_prop_solver                    active
% 2.72/1.02  --res_prop_simpl_new                    false
% 2.72/1.02  --res_prop_simpl_given                  true
% 2.72/1.02  --res_passive_queue_type                priority_queues
% 2.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.02  --res_passive_queues_freq               [15;5]
% 2.72/1.02  --res_forward_subs                      full
% 2.72/1.02  --res_backward_subs                     full
% 2.72/1.02  --res_forward_subs_resolution           true
% 2.72/1.02  --res_backward_subs_resolution          true
% 2.72/1.02  --res_orphan_elimination                true
% 2.72/1.02  --res_time_limit                        2.
% 2.72/1.02  --res_out_proof                         true
% 2.72/1.02  
% 2.72/1.02  ------ Superposition Options
% 2.72/1.02  
% 2.72/1.02  --superposition_flag                    true
% 2.72/1.02  --sup_passive_queue_type                priority_queues
% 2.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.02  --demod_completeness_check              fast
% 2.72/1.02  --demod_use_ground                      true
% 2.72/1.02  --sup_to_prop_solver                    passive
% 2.72/1.02  --sup_prop_simpl_new                    true
% 2.72/1.02  --sup_prop_simpl_given                  true
% 2.72/1.02  --sup_fun_splitting                     false
% 2.72/1.02  --sup_smt_interval                      50000
% 2.72/1.02  
% 2.72/1.02  ------ Superposition Simplification Setup
% 2.72/1.02  
% 2.72/1.02  --sup_indices_passive                   []
% 2.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_full_bw                           [BwDemod]
% 2.72/1.02  --sup_immed_triv                        [TrivRules]
% 2.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_immed_bw_main                     []
% 2.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.02  
% 2.72/1.02  ------ Combination Options
% 2.72/1.02  
% 2.72/1.02  --comb_res_mult                         3
% 2.72/1.02  --comb_sup_mult                         2
% 2.72/1.02  --comb_inst_mult                        10
% 2.72/1.02  
% 2.72/1.02  ------ Debug Options
% 2.72/1.02  
% 2.72/1.02  --dbg_backtrace                         false
% 2.72/1.02  --dbg_dump_prop_clauses                 false
% 2.72/1.02  --dbg_dump_prop_clauses_file            -
% 2.72/1.02  --dbg_out_stat                          false
% 2.72/1.02  ------ Parsing...
% 2.72/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.72/1.02  ------ Proving...
% 2.72/1.02  ------ Problem Properties 
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  clauses                                 16
% 2.72/1.02  conjectures                             2
% 2.72/1.02  EPR                                     3
% 2.72/1.02  Horn                                    15
% 2.72/1.02  unary                                   8
% 2.72/1.02  binary                                  6
% 2.72/1.02  lits                                    26
% 2.72/1.02  lits eq                                 8
% 2.72/1.02  fd_pure                                 0
% 2.72/1.02  fd_pseudo                               0
% 2.72/1.02  fd_cond                                 1
% 2.72/1.02  fd_pseudo_cond                          0
% 2.72/1.02  AC symbols                              0
% 2.72/1.02  
% 2.72/1.02  ------ Schedule dynamic 5 is on 
% 2.72/1.02  
% 2.72/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  ------ 
% 2.72/1.02  Current options:
% 2.72/1.02  ------ 
% 2.72/1.02  
% 2.72/1.02  ------ Input Options
% 2.72/1.02  
% 2.72/1.02  --out_options                           all
% 2.72/1.02  --tptp_safe_out                         true
% 2.72/1.02  --problem_path                          ""
% 2.72/1.02  --include_path                          ""
% 2.72/1.02  --clausifier                            res/vclausify_rel
% 2.72/1.02  --clausifier_options                    --mode clausify
% 2.72/1.02  --stdin                                 false
% 2.72/1.02  --stats_out                             all
% 2.72/1.02  
% 2.72/1.02  ------ General Options
% 2.72/1.02  
% 2.72/1.02  --fof                                   false
% 2.72/1.02  --time_out_real                         305.
% 2.72/1.02  --time_out_virtual                      -1.
% 2.72/1.02  --symbol_type_check                     false
% 2.72/1.02  --clausify_out                          false
% 2.72/1.02  --sig_cnt_out                           false
% 2.72/1.02  --trig_cnt_out                          false
% 2.72/1.02  --trig_cnt_out_tolerance                1.
% 2.72/1.02  --trig_cnt_out_sk_spl                   false
% 2.72/1.02  --abstr_cl_out                          false
% 2.72/1.02  
% 2.72/1.02  ------ Global Options
% 2.72/1.02  
% 2.72/1.02  --schedule                              default
% 2.72/1.02  --add_important_lit                     false
% 2.72/1.02  --prop_solver_per_cl                    1000
% 2.72/1.02  --min_unsat_core                        false
% 2.72/1.02  --soft_assumptions                      false
% 2.72/1.02  --soft_lemma_size                       3
% 2.72/1.02  --prop_impl_unit_size                   0
% 2.72/1.02  --prop_impl_unit                        []
% 2.72/1.02  --share_sel_clauses                     true
% 2.72/1.02  --reset_solvers                         false
% 2.72/1.02  --bc_imp_inh                            [conj_cone]
% 2.72/1.02  --conj_cone_tolerance                   3.
% 2.72/1.02  --extra_neg_conj                        none
% 2.72/1.02  --large_theory_mode                     true
% 2.72/1.02  --prolific_symb_bound                   200
% 2.72/1.02  --lt_threshold                          2000
% 2.72/1.02  --clause_weak_htbl                      true
% 2.72/1.02  --gc_record_bc_elim                     false
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing Options
% 2.72/1.02  
% 2.72/1.02  --preprocessing_flag                    true
% 2.72/1.02  --time_out_prep_mult                    0.1
% 2.72/1.02  --splitting_mode                        input
% 2.72/1.02  --splitting_grd                         true
% 2.72/1.02  --splitting_cvd                         false
% 2.72/1.02  --splitting_cvd_svl                     false
% 2.72/1.02  --splitting_nvd                         32
% 2.72/1.02  --sub_typing                            true
% 2.72/1.02  --prep_gs_sim                           true
% 2.72/1.02  --prep_unflatten                        true
% 2.72/1.02  --prep_res_sim                          true
% 2.72/1.02  --prep_upred                            true
% 2.72/1.02  --prep_sem_filter                       exhaustive
% 2.72/1.02  --prep_sem_filter_out                   false
% 2.72/1.02  --pred_elim                             true
% 2.72/1.02  --res_sim_input                         true
% 2.72/1.02  --eq_ax_congr_red                       true
% 2.72/1.02  --pure_diseq_elim                       true
% 2.72/1.02  --brand_transform                       false
% 2.72/1.02  --non_eq_to_eq                          false
% 2.72/1.02  --prep_def_merge                        true
% 2.72/1.02  --prep_def_merge_prop_impl              false
% 2.72/1.02  --prep_def_merge_mbd                    true
% 2.72/1.02  --prep_def_merge_tr_red                 false
% 2.72/1.02  --prep_def_merge_tr_cl                  false
% 2.72/1.02  --smt_preprocessing                     true
% 2.72/1.02  --smt_ac_axioms                         fast
% 2.72/1.02  --preprocessed_out                      false
% 2.72/1.02  --preprocessed_stats                    false
% 2.72/1.02  
% 2.72/1.02  ------ Abstraction refinement Options
% 2.72/1.02  
% 2.72/1.02  --abstr_ref                             []
% 2.72/1.02  --abstr_ref_prep                        false
% 2.72/1.02  --abstr_ref_until_sat                   false
% 2.72/1.02  --abstr_ref_sig_restrict                funpre
% 2.72/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.72/1.02  --abstr_ref_under                       []
% 2.72/1.02  
% 2.72/1.02  ------ SAT Options
% 2.72/1.02  
% 2.72/1.02  --sat_mode                              false
% 2.72/1.02  --sat_fm_restart_options                ""
% 2.72/1.02  --sat_gr_def                            false
% 2.72/1.02  --sat_epr_types                         true
% 2.72/1.02  --sat_non_cyclic_types                  false
% 2.72/1.02  --sat_finite_models                     false
% 2.72/1.02  --sat_fm_lemmas                         false
% 2.72/1.02  --sat_fm_prep                           false
% 2.72/1.02  --sat_fm_uc_incr                        true
% 2.72/1.02  --sat_out_model                         small
% 2.72/1.02  --sat_out_clauses                       false
% 2.72/1.02  
% 2.72/1.02  ------ QBF Options
% 2.72/1.02  
% 2.72/1.02  --qbf_mode                              false
% 2.72/1.02  --qbf_elim_univ                         false
% 2.72/1.02  --qbf_dom_inst                          none
% 2.72/1.02  --qbf_dom_pre_inst                      false
% 2.72/1.02  --qbf_sk_in                             false
% 2.72/1.02  --qbf_pred_elim                         true
% 2.72/1.02  --qbf_split                             512
% 2.72/1.02  
% 2.72/1.02  ------ BMC1 Options
% 2.72/1.02  
% 2.72/1.02  --bmc1_incremental                      false
% 2.72/1.02  --bmc1_axioms                           reachable_all
% 2.72/1.02  --bmc1_min_bound                        0
% 2.72/1.02  --bmc1_max_bound                        -1
% 2.72/1.02  --bmc1_max_bound_default                -1
% 2.72/1.02  --bmc1_symbol_reachability              true
% 2.72/1.02  --bmc1_property_lemmas                  false
% 2.72/1.02  --bmc1_k_induction                      false
% 2.72/1.02  --bmc1_non_equiv_states                 false
% 2.72/1.02  --bmc1_deadlock                         false
% 2.72/1.02  --bmc1_ucm                              false
% 2.72/1.02  --bmc1_add_unsat_core                   none
% 2.72/1.02  --bmc1_unsat_core_children              false
% 2.72/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.72/1.02  --bmc1_out_stat                         full
% 2.72/1.02  --bmc1_ground_init                      false
% 2.72/1.02  --bmc1_pre_inst_next_state              false
% 2.72/1.02  --bmc1_pre_inst_state                   false
% 2.72/1.02  --bmc1_pre_inst_reach_state             false
% 2.72/1.02  --bmc1_out_unsat_core                   false
% 2.72/1.02  --bmc1_aig_witness_out                  false
% 2.72/1.02  --bmc1_verbose                          false
% 2.72/1.02  --bmc1_dump_clauses_tptp                false
% 2.72/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.72/1.02  --bmc1_dump_file                        -
% 2.72/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.72/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.72/1.02  --bmc1_ucm_extend_mode                  1
% 2.72/1.02  --bmc1_ucm_init_mode                    2
% 2.72/1.02  --bmc1_ucm_cone_mode                    none
% 2.72/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.72/1.02  --bmc1_ucm_relax_model                  4
% 2.72/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.72/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.72/1.02  --bmc1_ucm_layered_model                none
% 2.72/1.02  --bmc1_ucm_max_lemma_size               10
% 2.72/1.02  
% 2.72/1.02  ------ AIG Options
% 2.72/1.02  
% 2.72/1.02  --aig_mode                              false
% 2.72/1.02  
% 2.72/1.02  ------ Instantiation Options
% 2.72/1.02  
% 2.72/1.02  --instantiation_flag                    true
% 2.72/1.02  --inst_sos_flag                         false
% 2.72/1.02  --inst_sos_phase                        true
% 2.72/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.72/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.72/1.02  --inst_lit_sel_side                     none
% 2.72/1.02  --inst_solver_per_active                1400
% 2.72/1.02  --inst_solver_calls_frac                1.
% 2.72/1.02  --inst_passive_queue_type               priority_queues
% 2.72/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.72/1.02  --inst_passive_queues_freq              [25;2]
% 2.72/1.02  --inst_dismatching                      true
% 2.72/1.02  --inst_eager_unprocessed_to_passive     true
% 2.72/1.02  --inst_prop_sim_given                   true
% 2.72/1.02  --inst_prop_sim_new                     false
% 2.72/1.02  --inst_subs_new                         false
% 2.72/1.02  --inst_eq_res_simp                      false
% 2.72/1.02  --inst_subs_given                       false
% 2.72/1.02  --inst_orphan_elimination               true
% 2.72/1.02  --inst_learning_loop_flag               true
% 2.72/1.02  --inst_learning_start                   3000
% 2.72/1.02  --inst_learning_factor                  2
% 2.72/1.02  --inst_start_prop_sim_after_learn       3
% 2.72/1.02  --inst_sel_renew                        solver
% 2.72/1.02  --inst_lit_activity_flag                true
% 2.72/1.02  --inst_restr_to_given                   false
% 2.72/1.02  --inst_activity_threshold               500
% 2.72/1.02  --inst_out_proof                        true
% 2.72/1.02  
% 2.72/1.02  ------ Resolution Options
% 2.72/1.02  
% 2.72/1.02  --resolution_flag                       false
% 2.72/1.02  --res_lit_sel                           adaptive
% 2.72/1.02  --res_lit_sel_side                      none
% 2.72/1.02  --res_ordering                          kbo
% 2.72/1.02  --res_to_prop_solver                    active
% 2.72/1.02  --res_prop_simpl_new                    false
% 2.72/1.02  --res_prop_simpl_given                  true
% 2.72/1.02  --res_passive_queue_type                priority_queues
% 2.72/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.72/1.02  --res_passive_queues_freq               [15;5]
% 2.72/1.02  --res_forward_subs                      full
% 2.72/1.02  --res_backward_subs                     full
% 2.72/1.02  --res_forward_subs_resolution           true
% 2.72/1.02  --res_backward_subs_resolution          true
% 2.72/1.02  --res_orphan_elimination                true
% 2.72/1.02  --res_time_limit                        2.
% 2.72/1.02  --res_out_proof                         true
% 2.72/1.02  
% 2.72/1.02  ------ Superposition Options
% 2.72/1.02  
% 2.72/1.02  --superposition_flag                    true
% 2.72/1.02  --sup_passive_queue_type                priority_queues
% 2.72/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.72/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.72/1.02  --demod_completeness_check              fast
% 2.72/1.02  --demod_use_ground                      true
% 2.72/1.02  --sup_to_prop_solver                    passive
% 2.72/1.02  --sup_prop_simpl_new                    true
% 2.72/1.02  --sup_prop_simpl_given                  true
% 2.72/1.02  --sup_fun_splitting                     false
% 2.72/1.02  --sup_smt_interval                      50000
% 2.72/1.02  
% 2.72/1.02  ------ Superposition Simplification Setup
% 2.72/1.02  
% 2.72/1.02  --sup_indices_passive                   []
% 2.72/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.72/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.72/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_full_bw                           [BwDemod]
% 2.72/1.02  --sup_immed_triv                        [TrivRules]
% 2.72/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.72/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_immed_bw_main                     []
% 2.72/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.72/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.72/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.72/1.02  
% 2.72/1.02  ------ Combination Options
% 2.72/1.02  
% 2.72/1.02  --comb_res_mult                         3
% 2.72/1.02  --comb_sup_mult                         2
% 2.72/1.02  --comb_inst_mult                        10
% 2.72/1.02  
% 2.72/1.02  ------ Debug Options
% 2.72/1.02  
% 2.72/1.02  --dbg_backtrace                         false
% 2.72/1.02  --dbg_dump_prop_clauses                 false
% 2.72/1.02  --dbg_dump_prop_clauses_file            -
% 2.72/1.02  --dbg_out_stat                          false
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  ------ Proving...
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  % SZS status Theorem for theBenchmark.p
% 2.72/1.02  
% 2.72/1.02   Resolution empty clause
% 2.72/1.02  
% 2.72/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.72/1.02  
% 2.72/1.02  fof(f2,axiom,(
% 2.72/1.02    v1_xboole_0(k1_xboole_0)),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f50,plain,(
% 2.72/1.02    v1_xboole_0(k1_xboole_0)),
% 2.72/1.02    inference(cnf_transformation,[],[f2])).
% 2.72/1.02  
% 2.72/1.02  fof(f10,axiom,(
% 2.72/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f58,plain,(
% 2.72/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.72/1.02    inference(cnf_transformation,[],[f10])).
% 2.72/1.02  
% 2.72/1.02  fof(f9,axiom,(
% 2.72/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f24,plain,(
% 2.72/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.72/1.02    inference(ennf_transformation,[],[f9])).
% 2.72/1.02  
% 2.72/1.02  fof(f57,plain,(
% 2.72/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.72/1.02    inference(cnf_transformation,[],[f24])).
% 2.72/1.02  
% 2.72/1.02  fof(f8,axiom,(
% 2.72/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f23,plain,(
% 2.72/1.02    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.72/1.02    inference(ennf_transformation,[],[f8])).
% 2.72/1.02  
% 2.72/1.02  fof(f56,plain,(
% 2.72/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.72/1.02    inference(cnf_transformation,[],[f23])).
% 2.72/1.02  
% 2.72/1.02  fof(f1,axiom,(
% 2.72/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f36,plain,(
% 2.72/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.72/1.02    inference(nnf_transformation,[],[f1])).
% 2.72/1.02  
% 2.72/1.02  fof(f37,plain,(
% 2.72/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/1.02    inference(rectify,[],[f36])).
% 2.72/1.02  
% 2.72/1.02  fof(f38,plain,(
% 2.72/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.72/1.02    introduced(choice_axiom,[])).
% 2.72/1.02  
% 2.72/1.02  fof(f39,plain,(
% 2.72/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 2.72/1.02  
% 2.72/1.02  fof(f49,plain,(
% 2.72/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f39])).
% 2.72/1.02  
% 2.72/1.02  fof(f12,axiom,(
% 2.72/1.02    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f27,plain,(
% 2.72/1.02    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.72/1.02    inference(ennf_transformation,[],[f12])).
% 2.72/1.02  
% 2.72/1.02  fof(f60,plain,(
% 2.72/1.02    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f27])).
% 2.72/1.02  
% 2.72/1.02  fof(f3,axiom,(
% 2.72/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f20,plain,(
% 2.72/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.72/1.02    inference(ennf_transformation,[],[f3])).
% 2.72/1.02  
% 2.72/1.02  fof(f51,plain,(
% 2.72/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f20])).
% 2.72/1.02  
% 2.72/1.02  fof(f7,axiom,(
% 2.72/1.02    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f55,plain,(
% 2.72/1.02    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.72/1.02    inference(cnf_transformation,[],[f7])).
% 2.72/1.02  
% 2.72/1.02  fof(f6,axiom,(
% 2.72/1.02    ! [X0] : k2_subset_1(X0) = X0),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f54,plain,(
% 2.72/1.02    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.72/1.02    inference(cnf_transformation,[],[f6])).
% 2.72/1.02  
% 2.72/1.02  fof(f5,axiom,(
% 2.72/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f22,plain,(
% 2.72/1.02    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.72/1.02    inference(ennf_transformation,[],[f5])).
% 2.72/1.02  
% 2.72/1.02  fof(f53,plain,(
% 2.72/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.72/1.02    inference(cnf_transformation,[],[f22])).
% 2.72/1.02  
% 2.72/1.02  fof(f17,conjecture,(
% 2.72/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f18,negated_conjecture,(
% 2.72/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.72/1.02    inference(negated_conjecture,[],[f17])).
% 2.72/1.02  
% 2.72/1.02  fof(f19,plain,(
% 2.72/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.72/1.02    inference(pure_predicate_removal,[],[f18])).
% 2.72/1.02  
% 2.72/1.02  fof(f34,plain,(
% 2.72/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.72/1.02    inference(ennf_transformation,[],[f19])).
% 2.72/1.02  
% 2.72/1.02  fof(f35,plain,(
% 2.72/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.72/1.02    inference(flattening,[],[f34])).
% 2.72/1.02  
% 2.72/1.02  fof(f46,plain,(
% 2.72/1.02    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.72/1.02    introduced(choice_axiom,[])).
% 2.72/1.02  
% 2.72/1.02  fof(f45,plain,(
% 2.72/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.72/1.02    introduced(choice_axiom,[])).
% 2.72/1.02  
% 2.72/1.02  fof(f47,plain,(
% 2.72/1.02    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f46,f45])).
% 2.72/1.02  
% 2.72/1.02  fof(f72,plain,(
% 2.72/1.02    v1_xboole_0(sK4)),
% 2.72/1.02    inference(cnf_transformation,[],[f47])).
% 2.72/1.02  
% 2.72/1.02  fof(f74,plain,(
% 2.72/1.02    ~v2_tex_2(sK4,sK3)),
% 2.72/1.02    inference(cnf_transformation,[],[f47])).
% 2.72/1.02  
% 2.72/1.02  fof(f15,axiom,(
% 2.72/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f30,plain,(
% 2.72/1.02    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.72/1.02    inference(ennf_transformation,[],[f15])).
% 2.72/1.02  
% 2.72/1.02  fof(f31,plain,(
% 2.72/1.02    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.72/1.02    inference(flattening,[],[f30])).
% 2.72/1.02  
% 2.72/1.02  fof(f63,plain,(
% 2.72/1.02    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f31])).
% 2.72/1.02  
% 2.72/1.02  fof(f70,plain,(
% 2.72/1.02    v2_pre_topc(sK3)),
% 2.72/1.02    inference(cnf_transformation,[],[f47])).
% 2.72/1.02  
% 2.72/1.02  fof(f71,plain,(
% 2.72/1.02    l1_pre_topc(sK3)),
% 2.72/1.02    inference(cnf_transformation,[],[f47])).
% 2.72/1.02  
% 2.72/1.02  fof(f16,axiom,(
% 2.72/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f32,plain,(
% 2.72/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(ennf_transformation,[],[f16])).
% 2.72/1.02  
% 2.72/1.02  fof(f33,plain,(
% 2.72/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(flattening,[],[f32])).
% 2.72/1.02  
% 2.72/1.02  fof(f40,plain,(
% 2.72/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(nnf_transformation,[],[f33])).
% 2.72/1.02  
% 2.72/1.02  fof(f41,plain,(
% 2.72/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(rectify,[],[f40])).
% 2.72/1.02  
% 2.72/1.02  fof(f43,plain,(
% 2.72/1.02    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.72/1.02    introduced(choice_axiom,[])).
% 2.72/1.02  
% 2.72/1.02  fof(f42,plain,(
% 2.72/1.02    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.72/1.02    introduced(choice_axiom,[])).
% 2.72/1.02  
% 2.72/1.02  fof(f44,plain,(
% 2.72/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f43,f42])).
% 2.72/1.02  
% 2.72/1.02  fof(f69,plain,(
% 2.72/1.02    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f44])).
% 2.72/1.02  
% 2.72/1.02  fof(f73,plain,(
% 2.72/1.02    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.72/1.02    inference(cnf_transformation,[],[f47])).
% 2.72/1.02  
% 2.72/1.02  fof(f14,axiom,(
% 2.72/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f29,plain,(
% 2.72/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.72/1.02    inference(ennf_transformation,[],[f14])).
% 2.72/1.02  
% 2.72/1.02  fof(f62,plain,(
% 2.72/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f29])).
% 2.72/1.02  
% 2.72/1.02  fof(f13,axiom,(
% 2.72/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f28,plain,(
% 2.72/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.72/1.02    inference(ennf_transformation,[],[f13])).
% 2.72/1.02  
% 2.72/1.02  fof(f61,plain,(
% 2.72/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f28])).
% 2.72/1.02  
% 2.72/1.02  fof(f4,axiom,(
% 2.72/1.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.72/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.72/1.02  
% 2.72/1.02  fof(f21,plain,(
% 2.72/1.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.72/1.02    inference(ennf_transformation,[],[f4])).
% 2.72/1.02  
% 2.72/1.02  fof(f52,plain,(
% 2.72/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f21])).
% 2.72/1.02  
% 2.72/1.02  fof(f68,plain,(
% 2.72/1.02    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.72/1.02    inference(cnf_transformation,[],[f44])).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2,plain,
% 2.72/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1063,plain,
% 2.72/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_10,plain,
% 2.72/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.72/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1057,plain,
% 2.72/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_9,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1058,plain,
% 2.72/1.02      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 2.72/1.02      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1590,plain,
% 2.72/1.02      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1057,c_1058]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_8,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.72/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1059,plain,
% 2.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.72/1.02      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2047,plain,
% 2.72/1.02      ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top
% 2.72/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1590,c_1059]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2500,plain,
% 2.72/1.02      ( m1_subset_1(k3_xboole_0(X0,k1_xboole_0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.72/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_2047,c_1057]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_0,plain,
% 2.72/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_12,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | ~ r2_hidden(X2,X0)
% 2.72/1.02      | ~ v1_xboole_0(X1) ),
% 2.72/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_339,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | ~ v1_xboole_0(X1)
% 2.72/1.02      | v1_xboole_0(X2)
% 2.72/1.02      | X0 != X2
% 2.72/1.02      | sK0(X2) != X3 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_12]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_340,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | ~ v1_xboole_0(X1)
% 2.72/1.02      | v1_xboole_0(X0) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_339]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1053,plain,
% 2.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.72/1.02      | v1_xboole_0(X1) != iProver_top
% 2.72/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2508,plain,
% 2.72/1.02      ( v1_xboole_0(X0) != iProver_top
% 2.72/1.02      | v1_xboole_0(k3_xboole_0(X1,k1_xboole_0)) = iProver_top ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_2500,c_1053]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2628,plain,
% 2.72/1.02      ( v1_xboole_0(k3_xboole_0(X0,k1_xboole_0)) = iProver_top ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1063,c_2508]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_3,plain,
% 2.72/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.72/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1062,plain,
% 2.72/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2701,plain,
% 2.72/1.02      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_2628,c_1062]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_7,plain,
% 2.72/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.72/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1060,plain,
% 2.72/1.02      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_6,plain,
% 2.72/1.02      ( k2_subset_1(X0) = X0 ),
% 2.72/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1077,plain,
% 2.72/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.72/1.02      inference(light_normalisation,[status(thm)],[c_1060,c_6]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_5,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.72/1.02      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1061,plain,
% 2.72/1.02      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 2.72/1.02      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2099,plain,
% 2.72/1.02      ( k9_subset_1(X0,X0,X1) = k9_subset_1(X0,X1,X0) ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1077,c_1061]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1592,plain,
% 2.72/1.02      ( k9_subset_1(X0,X1,X0) = k3_xboole_0(X1,X0) ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1077,c_1058]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2101,plain,
% 2.72/1.02      ( k9_subset_1(X0,X0,X1) = k3_xboole_0(X1,X0) ),
% 2.72/1.02      inference(light_normalisation,[status(thm)],[c_2099,c_1592]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2345,plain,
% 2.72/1.02      ( k3_xboole_0(k1_xboole_0,X0) = k3_xboole_0(X0,k1_xboole_0) ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_2101,c_1590]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2713,plain,
% 2.72/1.02      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.72/1.02      inference(demodulation,[status(thm)],[c_2701,c_2345]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_24,negated_conjecture,
% 2.72/1.02      ( v1_xboole_0(sK4) ),
% 2.72/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1055,plain,
% 2.72/1.02      ( v1_xboole_0(sK4) = iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1549,plain,
% 2.72/1.02      ( sK4 = k1_xboole_0 ),
% 2.72/1.02      inference(superposition,[status(thm)],[c_1055,c_1062]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_22,negated_conjecture,
% 2.72/1.02      ( ~ v2_tex_2(sK4,sK3) ),
% 2.72/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_15,plain,
% 2.72/1.02      ( v4_pre_topc(k2_struct_0(X0),X0)
% 2.72/1.02      | ~ v2_pre_topc(X0)
% 2.72/1.02      | ~ l1_pre_topc(X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_26,negated_conjecture,
% 2.72/1.02      ( v2_pre_topc(sK3) ),
% 2.72/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_311,plain,
% 2.72/1.02      ( v4_pre_topc(k2_struct_0(X0),X0) | ~ l1_pre_topc(X0) | sK3 != X0 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_312,plain,
% 2.72/1.02      ( v4_pre_topc(k2_struct_0(sK3),sK3) | ~ l1_pre_topc(sK3) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_311]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_25,negated_conjecture,
% 2.72/1.02      ( l1_pre_topc(sK3) ),
% 2.72/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_314,plain,
% 2.72/1.02      ( v4_pre_topc(k2_struct_0(sK3),sK3) ),
% 2.72/1.02      inference(global_propositional_subsumption,[status(thm)],[c_312,c_25]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_16,plain,
% 2.72/1.02      ( v2_tex_2(X0,X1)
% 2.72/1.02      | ~ v4_pre_topc(X2,X1)
% 2.72/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | ~ l1_pre_topc(X1)
% 2.72/1.02      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_525,plain,
% 2.72/1.02      ( v2_tex_2(X0,X1)
% 2.72/1.02      | ~ v4_pre_topc(X2,X1)
% 2.72/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 2.72/1.02      | sK3 != X1 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_25]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_526,plain,
% 2.72/1.02      ( v2_tex_2(X0,sK3)
% 2.72/1.02      | ~ v4_pre_topc(X1,sK3)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_525]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_656,plain,
% 2.72/1.02      ( v2_tex_2(X0,sK3)
% 2.72/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 2.72/1.02      | k2_struct_0(sK3) != X1
% 2.72/1.02      | sK3 != sK3 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_314,c_526]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_657,plain,
% 2.72/1.02      ( v2_tex_2(X0,sK3)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) != sK1(sK3,X0) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_656]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_688,plain,
% 2.72/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),X0,k2_struct_0(sK3)) != sK1(sK3,X0)
% 2.72/1.02      | sK3 != sK3
% 2.72/1.02      | sK4 != X0 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_657]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_689,plain,
% 2.72/1.02      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_688]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_23,negated_conjecture,
% 2.72/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.72/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_691,plain,
% 2.72/1.02      ( ~ m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
% 2.72/1.02      inference(global_propositional_subsumption,[status(thm)],[c_689,c_23]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1051,plain,
% 2.72/1.02      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4)
% 2.72/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.72/1.02      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_14,plain,
% 2.72/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_13,plain,
% 2.72/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.72/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_297,plain,
% 2.72/1.02      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.72/1.02      inference(resolution,[status(thm)],[c_14,c_13]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_427,plain,
% 2.72/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_297,c_25]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_428,plain,
% 2.72/1.02      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_427]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1115,plain,
% 2.72/1.02      ( k9_subset_1(k2_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4)
% 2.72/1.02      | m1_subset_1(k2_struct_0(sK3),k1_zfmisc_1(k2_struct_0(sK3))) != iProver_top ),
% 2.72/1.02      inference(light_normalisation,[status(thm)],[c_1051,c_428]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1118,plain,
% 2.72/1.02      ( k9_subset_1(k2_struct_0(sK3),sK4,k2_struct_0(sK3)) != sK1(sK3,sK4) ),
% 2.72/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1115,c_1077]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1606,plain,
% 2.72/1.02      ( k9_subset_1(k2_struct_0(sK3),k1_xboole_0,k2_struct_0(sK3)) != sK1(sK3,k1_xboole_0) ),
% 2.72/1.02      inference(demodulation,[status(thm)],[c_1549,c_1118]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_4,plain,
% 2.72/1.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.72/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_17,plain,
% 2.72/1.02      ( v2_tex_2(X0,X1)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | r1_tarski(sK1(X1,X0),X0)
% 2.72/1.02      | ~ l1_pre_topc(X1) ),
% 2.72/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_510,plain,
% 2.72/1.02      ( v2_tex_2(X0,X1)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.72/1.02      | r1_tarski(sK1(X1,X0),X0)
% 2.72/1.02      | sK3 != X1 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_511,plain,
% 2.72/1.02      ( v2_tex_2(X0,sK3)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | r1_tarski(sK1(sK3,X0),X0) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_510]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_634,plain,
% 2.72/1.02      ( v2_tex_2(X0,sK3)
% 2.72/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | sK1(sK3,X0) != X1
% 2.72/1.02      | k1_xboole_0 != X0
% 2.72/1.02      | k1_xboole_0 = X1 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_511]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_635,plain,
% 2.72/1.02      ( v2_tex_2(k1_xboole_0,sK3)
% 2.72/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.72/1.02      | k1_xboole_0 = sK1(sK3,k1_xboole_0) ),
% 2.72/1.02      inference(unflattening,[status(thm)],[c_634]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_643,plain,
% 2.72/1.02      ( v2_tex_2(k1_xboole_0,sK3) | k1_xboole_0 = sK1(sK3,k1_xboole_0) ),
% 2.72/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_635,c_10]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_702,plain,
% 2.72/1.02      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 | sK3 != sK3 | sK4 != k1_xboole_0 ),
% 2.72/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_643]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_733,plain,
% 2.72/1.02      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 | sK4 != k1_xboole_0 ),
% 2.72/1.02      inference(equality_resolution_simp,[status(thm)],[c_702]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1607,plain,
% 2.72/1.02      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.72/1.02      inference(demodulation,[status(thm)],[c_1549,c_733]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1614,plain,
% 2.72/1.02      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.72/1.02      inference(equality_resolution_simp,[status(thm)],[c_1607]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1618,plain,
% 2.72/1.02      ( k9_subset_1(k2_struct_0(sK3),k1_xboole_0,k2_struct_0(sK3)) != k1_xboole_0 ),
% 2.72/1.02      inference(light_normalisation,[status(thm)],[c_1606,c_1614]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_1984,plain,
% 2.72/1.02      ( k3_xboole_0(k1_xboole_0,k2_struct_0(sK3)) != k1_xboole_0 ),
% 2.72/1.02      inference(demodulation,[status(thm)],[c_1592,c_1618]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2883,plain,
% 2.72/1.02      ( k1_xboole_0 != k1_xboole_0 ),
% 2.72/1.02      inference(demodulation,[status(thm)],[c_2713,c_1984]) ).
% 2.72/1.02  
% 2.72/1.02  cnf(c_2886,plain,
% 2.72/1.02      ( $false ),
% 2.72/1.02      inference(equality_resolution_simp,[status(thm)],[c_2883]) ).
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.72/1.02  
% 2.72/1.02  ------                               Statistics
% 2.72/1.02  
% 2.72/1.02  ------ General
% 2.72/1.02  
% 2.72/1.02  abstr_ref_over_cycles:                  0
% 2.72/1.02  abstr_ref_under_cycles:                 0
% 2.72/1.02  gc_basic_clause_elim:                   0
% 2.72/1.02  forced_gc_time:                         0
% 2.72/1.02  parsing_time:                           0.012
% 2.72/1.02  unif_index_cands_time:                  0.
% 2.72/1.02  unif_index_add_time:                    0.
% 2.72/1.02  orderings_time:                         0.
% 2.72/1.02  out_proof_time:                         0.012
% 2.72/1.02  total_time:                             0.15
% 2.72/1.02  num_of_symbols:                         52
% 2.72/1.02  num_of_terms:                           2385
% 2.72/1.02  
% 2.72/1.02  ------ Preprocessing
% 2.72/1.02  
% 2.72/1.02  num_of_splits:                          0
% 2.72/1.02  num_of_split_atoms:                     0
% 2.72/1.02  num_of_reused_defs:                     0
% 2.72/1.02  num_eq_ax_congr_red:                    22
% 2.72/1.02  num_of_sem_filtered_clauses:            1
% 2.72/1.02  num_of_subtypes:                        0
% 2.72/1.02  monotx_restored_types:                  0
% 2.72/1.02  sat_num_of_epr_types:                   0
% 2.72/1.02  sat_num_of_non_cyclic_types:            0
% 2.72/1.02  sat_guarded_non_collapsed_types:        0
% 2.72/1.02  num_pure_diseq_elim:                    0
% 2.72/1.02  simp_replaced_by:                       0
% 2.72/1.02  res_preprocessed:                       94
% 2.72/1.02  prep_upred:                             0
% 2.72/1.02  prep_unflattend:                        31
% 2.72/1.02  smt_new_axioms:                         0
% 2.72/1.02  pred_elim_cands:                        2
% 2.72/1.02  pred_elim:                              7
% 2.72/1.02  pred_elim_cl:                           11
% 2.72/1.02  pred_elim_cycles:                       11
% 2.72/1.02  merged_defs:                            0
% 2.72/1.02  merged_defs_ncl:                        0
% 2.72/1.02  bin_hyper_res:                          0
% 2.72/1.02  prep_cycles:                            4
% 2.72/1.02  pred_elim_time:                         0.013
% 2.72/1.02  splitting_time:                         0.
% 2.72/1.02  sem_filter_time:                        0.
% 2.72/1.02  monotx_time:                            0.001
% 2.72/1.02  subtype_inf_time:                       0.
% 2.72/1.02  
% 2.72/1.02  ------ Problem properties
% 2.72/1.02  
% 2.72/1.02  clauses:                                16
% 2.72/1.02  conjectures:                            2
% 2.72/1.02  epr:                                    3
% 2.72/1.02  horn:                                   15
% 2.72/1.02  ground:                                 7
% 2.72/1.02  unary:                                  8
% 2.72/1.02  binary:                                 6
% 2.72/1.02  lits:                                   26
% 2.72/1.02  lits_eq:                                8
% 2.72/1.02  fd_pure:                                0
% 2.72/1.02  fd_pseudo:                              0
% 2.72/1.02  fd_cond:                                1
% 2.72/1.02  fd_pseudo_cond:                         0
% 2.72/1.02  ac_symbols:                             0
% 2.72/1.02  
% 2.72/1.02  ------ Propositional Solver
% 2.72/1.02  
% 2.72/1.02  prop_solver_calls:                      28
% 2.72/1.02  prop_fast_solver_calls:                 535
% 2.72/1.02  smt_solver_calls:                       0
% 2.72/1.02  smt_fast_solver_calls:                  0
% 2.72/1.02  prop_num_of_clauses:                    944
% 2.72/1.02  prop_preprocess_simplified:             3331
% 2.72/1.02  prop_fo_subsumed:                       5
% 2.72/1.02  prop_solver_time:                       0.
% 2.72/1.02  smt_solver_time:                        0.
% 2.72/1.02  smt_fast_solver_time:                   0.
% 2.72/1.02  prop_fast_solver_time:                  0.
% 2.72/1.02  prop_unsat_core_time:                   0.
% 2.72/1.02  
% 2.72/1.02  ------ QBF
% 2.72/1.02  
% 2.72/1.02  qbf_q_res:                              0
% 2.72/1.02  qbf_num_tautologies:                    0
% 2.72/1.02  qbf_prep_cycles:                        0
% 2.72/1.02  
% 2.72/1.02  ------ BMC1
% 2.72/1.02  
% 2.72/1.02  bmc1_current_bound:                     -1
% 2.72/1.02  bmc1_last_solved_bound:                 -1
% 2.72/1.02  bmc1_unsat_core_size:                   -1
% 2.72/1.02  bmc1_unsat_core_parents_size:           -1
% 2.72/1.02  bmc1_merge_next_fun:                    0
% 2.72/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.72/1.02  
% 2.72/1.02  ------ Instantiation
% 2.72/1.02  
% 2.72/1.02  inst_num_of_clauses:                    285
% 2.72/1.02  inst_num_in_passive:                    67
% 2.72/1.02  inst_num_in_active:                     155
% 2.72/1.02  inst_num_in_unprocessed:                64
% 2.72/1.02  inst_num_of_loops:                      190
% 2.72/1.02  inst_num_of_learning_restarts:          0
% 2.72/1.02  inst_num_moves_active_passive:          32
% 2.72/1.02  inst_lit_activity:                      0
% 2.72/1.02  inst_lit_activity_moves:                0
% 2.72/1.02  inst_num_tautologies:                   0
% 2.72/1.02  inst_num_prop_implied:                  0
% 2.72/1.02  inst_num_existing_simplified:           0
% 2.72/1.02  inst_num_eq_res_simplified:             0
% 2.72/1.02  inst_num_child_elim:                    0
% 2.72/1.02  inst_num_of_dismatching_blockings:      117
% 2.72/1.02  inst_num_of_non_proper_insts:           264
% 2.72/1.02  inst_num_of_duplicates:                 0
% 2.72/1.02  inst_inst_num_from_inst_to_res:         0
% 2.72/1.02  inst_dismatching_checking_time:         0.
% 2.72/1.02  
% 2.72/1.02  ------ Resolution
% 2.72/1.02  
% 2.72/1.02  res_num_of_clauses:                     0
% 2.72/1.02  res_num_in_passive:                     0
% 2.72/1.02  res_num_in_active:                      0
% 2.72/1.02  res_num_of_loops:                       98
% 2.72/1.02  res_forward_subset_subsumed:            35
% 2.72/1.02  res_backward_subset_subsumed:           2
% 2.72/1.02  res_forward_subsumed:                   0
% 2.72/1.02  res_backward_subsumed:                  0
% 2.72/1.02  res_forward_subsumption_resolution:     3
% 2.72/1.02  res_backward_subsumption_resolution:    0
% 2.72/1.02  res_clause_to_clause_subsumption:       189
% 2.72/1.02  res_orphan_elimination:                 0
% 2.72/1.02  res_tautology_del:                      29
% 2.72/1.02  res_num_eq_res_simplified:              1
% 2.72/1.02  res_num_sel_changes:                    0
% 2.72/1.02  res_moves_from_active_to_pass:          0
% 2.72/1.02  
% 2.72/1.02  ------ Superposition
% 2.72/1.02  
% 2.72/1.02  sup_time_total:                         0.
% 2.72/1.02  sup_time_generating:                    0.
% 2.72/1.02  sup_time_sim_full:                      0.
% 2.72/1.02  sup_time_sim_immed:                     0.
% 2.72/1.02  
% 2.72/1.02  sup_num_of_clauses:                     45
% 2.72/1.02  sup_num_in_active:                      18
% 2.72/1.02  sup_num_in_passive:                     27
% 2.72/1.02  sup_num_of_loops:                       37
% 2.72/1.02  sup_fw_superposition:                   30
% 2.72/1.02  sup_bw_superposition:                   33
% 2.72/1.02  sup_immediate_simplified:               25
% 2.72/1.02  sup_given_eliminated:                   1
% 2.72/1.02  comparisons_done:                       0
% 2.72/1.02  comparisons_avoided:                    0
% 2.72/1.02  
% 2.72/1.02  ------ Simplifications
% 2.72/1.02  
% 2.72/1.02  
% 2.72/1.02  sim_fw_subset_subsumed:                 5
% 2.72/1.02  sim_bw_subset_subsumed:                 0
% 2.72/1.02  sim_fw_subsumed:                        6
% 2.72/1.02  sim_bw_subsumed:                        4
% 2.72/1.02  sim_fw_subsumption_res:                 2
% 2.72/1.02  sim_bw_subsumption_res:                 0
% 2.72/1.02  sim_tautology_del:                      1
% 2.72/1.02  sim_eq_tautology_del:                   1
% 2.72/1.02  sim_eq_res_simp:                        1
% 2.72/1.02  sim_fw_demodulated:                     3
% 2.72/1.02  sim_bw_demodulated:                     20
% 2.72/1.02  sim_light_normalised:                   14
% 2.72/1.02  sim_joinable_taut:                      0
% 2.72/1.02  sim_joinable_simp:                      0
% 2.72/1.02  sim_ac_normalised:                      0
% 2.72/1.02  sim_smt_subsumption:                    0
% 2.72/1.02  
%------------------------------------------------------------------------------
