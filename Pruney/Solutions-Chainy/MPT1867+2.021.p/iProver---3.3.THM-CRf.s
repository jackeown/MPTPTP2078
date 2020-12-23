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
% DateTime   : Thu Dec  3 12:26:10 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :  201 (1558 expanded)
%              Number of clauses        :  143 ( 525 expanded)
%              Number of leaves         :   19 ( 341 expanded)
%              Depth                    :   27
%              Number of atoms          :  619 (6259 expanded)
%              Number of equality atoms :  228 ( 792 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f37,f36])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
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
                            & v3_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( ? [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ? [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) = X2
                      & v3_pre_topc(X3,X0)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
                      | ~ v3_pre_topc(X3,X0)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ? [X5] :
                      ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
                      & v3_pre_topc(X5,X0)
                      & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f31])).

fof(f34,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v3_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f14])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f61,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f63,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f39])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f52,plain,(
    ! [X0] :
      ( v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f58,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2375,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_16,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_617,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_23])).

cnf(c_618,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_2367,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_6,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2379,plain,
    ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(X1,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2378,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_704,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_705,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK5)) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_2373,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_3120,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_2373])).

cnf(c_3684,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X2,X0) = iProver_top
    | r1_tarski(X2,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_3120])).

cnf(c_8768,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X1,sK2(sK4,X0)) = iProver_top
    | r1_tarski(X1,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2367,c_3684])).

cnf(c_10069,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK2(sK4,sK5)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_8768])).

cnf(c_28,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_29,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_76,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_80,plain,
    ( ~ r1_tarski(sK4,sK4)
    | sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1836,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1847,plain,
    ( u1_struct_0(sK4) = u1_struct_0(sK4)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1836])).

cnf(c_2880,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2881,plain,
    ( X0 = sK5
    | r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2880])).

cnf(c_1832,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_4726,plain,
    ( u1_struct_0(sK4) != u1_struct_0(sK4)
    | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_1832])).

cnf(c_1833,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2590,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | X0 != X2
    | X1 != k1_zfmisc_1(X3) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2923,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X0
    | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_2590])).

cnf(c_3652,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | X1 != X0
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2923])).

cnf(c_7550,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_3652])).

cnf(c_7551,plain,
    ( X0 != sK5
    | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7550])).

cnf(c_13,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_540,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_23])).

cnf(c_541,plain,
    ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_540])).

cnf(c_2371,plain,
    ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_541])).

cnf(c_8766,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(X0,sK1(sK4)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_3684])).

cnf(c_9159,plain,
    ( r1_tarski(sK5,sK1(sK4)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_8766])).

cnf(c_26,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_48,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_50,plain,
    ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_2580,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK5))
    | ~ r1_tarski(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2720,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK5))
    | ~ r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2580])).

cnf(c_2722,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2720])).

cnf(c_2721,plain,
    ( r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2724,plain,
    ( r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2721])).

cnf(c_2834,plain,
    ( r2_hidden(sK0(X0,X1,sK1(sK4)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(X0))
    | r1_tarski(X1,sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3853,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),X0,sK1(sK4)),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_4735,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5)
    | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK5,sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_3853])).

cnf(c_4736,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5) = iProver_top
    | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK5,sK1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4735])).

cnf(c_2943,plain,
    ( ~ r2_hidden(X0,sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_6836,plain,
    ( ~ r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
    inference(instantiation,[status(thm)],[c_2943])).

cnf(c_6837,plain,
    ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6836])).

cnf(c_9241,plain,
    ( r1_tarski(sK5,sK1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9159,c_26,c_28,c_50,c_2722,c_2724,c_4736,c_6837])).

cnf(c_2382,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( ~ l1_pre_topc(X0)
    | v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_547,plain,
    ( v1_xboole_0(sK1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_23])).

cnf(c_548,plain,
    ( v1_xboole_0(sK1(sK4)) ),
    inference(unflattening,[status(thm)],[c_547])).

cnf(c_714,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | sK1(sK4) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_548])).

cnf(c_715,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(sK1(sK4))) ),
    inference(unflattening,[status(thm)],[c_714])).

cnf(c_2364,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(sK1(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_3675,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,sK1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_2364])).

cnf(c_3907,plain,
    ( r2_hidden(X0,sK1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_3675])).

cnf(c_4814,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK1(sK4),k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2379,c_3907])).

cnf(c_5922,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_4814])).

cnf(c_6145,plain,
    ( r1_tarski(sK1(sK4),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_5922])).

cnf(c_2383,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6184,plain,
    ( sK1(sK4) = sK5
    | r1_tarski(sK5,sK1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6145,c_2383])).

cnf(c_9251,plain,
    ( sK1(sK4) = sK5 ),
    inference(superposition,[status(thm)],[c_9241,c_6184])).

cnf(c_5921,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(sK1(sK4),X1) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_4814])).

cnf(c_7261,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK1(sK4),X1) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2378,c_5921])).

cnf(c_8007,plain,
    ( r1_tarski(X0,sK1(sK4)) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2382,c_7261])).

cnf(c_9268,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9251,c_8007])).

cnf(c_10134,plain,
    ( r1_tarski(X0,sK2(sK4,sK5)) = iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10069,c_28,c_29,c_76,c_80,c_1847,c_2881,c_4726,c_7551,c_9268])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_632,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_633,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_632])).

cnf(c_2366,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_3279,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_2366])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_633])).

cnf(c_1133,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_1132])).

cnf(c_1134,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1133])).

cnf(c_3426,plain,
    ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3279,c_28,c_1134])).

cnf(c_3780,plain,
    ( sK2(sK4,sK5) = sK5
    | r1_tarski(sK5,sK2(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3426,c_2383])).

cnf(c_10145,plain,
    ( sK2(sK4,sK5) = sK5
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_10134,c_3780])).

cnf(c_3280,plain,
    ( v2_tex_2(sK1(sK4),sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_2366])).

cnf(c_5438,plain,
    ( sK2(sK4,sK1(sK4)) = sK1(sK4)
    | v2_tex_2(sK1(sK4),sK4) = iProver_top
    | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3280,c_2383])).

cnf(c_2558,plain,
    ( v2_tex_2(sK1(sK4),sK4)
    | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_2559,plain,
    ( v2_tex_2(sK1(sK4),sK4) = iProver_top
    | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2558])).

cnf(c_3009,plain,
    ( ~ r1_tarski(X0,sK1(sK4))
    | ~ r1_tarski(sK1(sK4),X0)
    | X0 = sK1(sK4) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3934,plain,
    ( ~ r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4))
    | ~ r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4)))
    | sK2(sK4,sK1(sK4)) = sK1(sK4) ),
    inference(instantiation,[status(thm)],[c_3009])).

cnf(c_3935,plain,
    ( sK2(sK4,sK1(sK4)) = sK1(sK4)
    | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) != iProver_top
    | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3934])).

cnf(c_8064,plain,
    ( v2_tex_2(sK1(sK4),sK4) = iProver_top
    | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3280,c_8007])).

cnf(c_8117,plain,
    ( v2_tex_2(sK1(sK4),sK4) = iProver_top
    | sK2(sK4,sK1(sK4)) = sK1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5438,c_26,c_50,c_2559,c_3935,c_8064])).

cnf(c_8118,plain,
    ( sK2(sK4,sK1(sK4)) = sK1(sK4)
    | v2_tex_2(sK1(sK4),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_8117])).

cnf(c_9267,plain,
    ( sK2(sK4,sK5) = sK5
    | v2_tex_2(sK5,sK4) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9251,c_8118])).

cnf(c_10336,plain,
    ( sK2(sK4,sK5) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10145,c_29,c_9267])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2377,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2967,plain,
    ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_2377])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_188,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_188])).

cnf(c_234,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_189])).

cnf(c_2374,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_234])).

cnf(c_5720,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,sK5) = k3_xboole_0(X0,sK5) ),
    inference(superposition,[status(thm)],[c_2967,c_2374])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_647,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_648,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v3_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_2365,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_6017,plain,
    ( sK2(sK4,X0) != k3_xboole_0(X0,sK5)
    | v2_tex_2(X0,sK4) = iProver_top
    | v3_pre_topc(sK5,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5720,c_2365])).

cnf(c_11,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_326,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_24])).

cnf(c_327,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_331,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_23])).

cnf(c_332,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_331])).

cnf(c_393,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_332,c_22])).

cnf(c_394,plain,
    ( v3_pre_topc(sK5,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_395,plain,
    ( v3_pre_topc(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_6786,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sK2(sK4,X0) != k3_xboole_0(X0,sK5)
    | v2_tex_2(X0,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6017,c_28,c_395])).

cnf(c_6787,plain,
    ( sK2(sK4,X0) != k3_xboole_0(X0,sK5)
    | v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_6786])).

cnf(c_10365,plain,
    ( k3_xboole_0(sK5,sK5) != sK5
    | v2_tex_2(sK5,sK4) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_10336,c_6787])).

cnf(c_15606,plain,
    ( k3_xboole_0(sK5,sK5) != sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10365,c_28,c_29])).

cnf(c_3,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2381,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8009,plain,
    ( r1_tarski(X0,sK5) != iProver_top
    | r1_tarski(sK1(sK4),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6145,c_7261])).

cnf(c_8188,plain,
    ( sK1(sK4) = X0
    | r1_tarski(X0,sK1(sK4)) != iProver_top
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_8009,c_2383])).

cnf(c_3995,plain,
    ( ~ r1_tarski(X0,sK1(sK4))
    | ~ r1_tarski(sK1(sK4),X0)
    | sK1(sK4) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3996,plain,
    ( sK1(sK4) = X0
    | r1_tarski(X0,sK1(sK4)) != iProver_top
    | r1_tarski(sK1(sK4),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3995])).

cnf(c_8818,plain,
    ( r1_tarski(X0,sK1(sK4)) != iProver_top
    | sK1(sK4) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8188,c_3996,c_8007])).

cnf(c_8819,plain,
    ( sK1(sK4) = X0
    | r1_tarski(X0,sK1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8818])).

cnf(c_9263,plain,
    ( sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9251,c_8819])).

cnf(c_13391,plain,
    ( k3_xboole_0(sK5,X0) = sK5 ),
    inference(superposition,[status(thm)],[c_2381,c_9263])).

cnf(c_15608,plain,
    ( sK5 != sK5 ),
    inference(demodulation,[status(thm)],[c_15606,c_13391])).

cnf(c_15609,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_15608])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:07:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.85/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.02  
% 3.85/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.85/1.02  
% 3.85/1.02  ------  iProver source info
% 3.85/1.02  
% 3.85/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.85/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.85/1.02  git: non_committed_changes: false
% 3.85/1.02  git: last_make_outside_of_git: false
% 3.85/1.02  
% 3.85/1.02  ------ 
% 3.85/1.02  
% 3.85/1.02  ------ Input Options
% 3.85/1.02  
% 3.85/1.02  --out_options                           all
% 3.85/1.02  --tptp_safe_out                         true
% 3.85/1.02  --problem_path                          ""
% 3.85/1.02  --include_path                          ""
% 3.85/1.02  --clausifier                            res/vclausify_rel
% 3.85/1.02  --clausifier_options                    --mode clausify
% 3.85/1.02  --stdin                                 false
% 3.85/1.02  --stats_out                             all
% 3.85/1.02  
% 3.85/1.02  ------ General Options
% 3.85/1.02  
% 3.85/1.02  --fof                                   false
% 3.85/1.02  --time_out_real                         305.
% 3.85/1.02  --time_out_virtual                      -1.
% 3.85/1.02  --symbol_type_check                     false
% 3.85/1.02  --clausify_out                          false
% 3.85/1.02  --sig_cnt_out                           false
% 3.85/1.02  --trig_cnt_out                          false
% 3.85/1.02  --trig_cnt_out_tolerance                1.
% 3.85/1.02  --trig_cnt_out_sk_spl                   false
% 3.85/1.02  --abstr_cl_out                          false
% 3.85/1.02  
% 3.85/1.02  ------ Global Options
% 3.85/1.02  
% 3.85/1.02  --schedule                              default
% 3.85/1.02  --add_important_lit                     false
% 3.85/1.02  --prop_solver_per_cl                    1000
% 3.85/1.02  --min_unsat_core                        false
% 3.85/1.02  --soft_assumptions                      false
% 3.85/1.02  --soft_lemma_size                       3
% 3.85/1.02  --prop_impl_unit_size                   0
% 3.85/1.02  --prop_impl_unit                        []
% 3.85/1.02  --share_sel_clauses                     true
% 3.85/1.02  --reset_solvers                         false
% 3.85/1.02  --bc_imp_inh                            [conj_cone]
% 3.85/1.02  --conj_cone_tolerance                   3.
% 3.85/1.02  --extra_neg_conj                        none
% 3.85/1.02  --large_theory_mode                     true
% 3.85/1.02  --prolific_symb_bound                   200
% 3.85/1.02  --lt_threshold                          2000
% 3.85/1.02  --clause_weak_htbl                      true
% 3.85/1.02  --gc_record_bc_elim                     false
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing Options
% 3.85/1.02  
% 3.85/1.02  --preprocessing_flag                    true
% 3.85/1.02  --time_out_prep_mult                    0.1
% 3.85/1.02  --splitting_mode                        input
% 3.85/1.02  --splitting_grd                         true
% 3.85/1.02  --splitting_cvd                         false
% 3.85/1.02  --splitting_cvd_svl                     false
% 3.85/1.02  --splitting_nvd                         32
% 3.85/1.02  --sub_typing                            true
% 3.85/1.02  --prep_gs_sim                           true
% 3.85/1.02  --prep_unflatten                        true
% 3.85/1.02  --prep_res_sim                          true
% 3.85/1.02  --prep_upred                            true
% 3.85/1.02  --prep_sem_filter                       exhaustive
% 3.85/1.02  --prep_sem_filter_out                   false
% 3.85/1.02  --pred_elim                             true
% 3.85/1.02  --res_sim_input                         true
% 3.85/1.02  --eq_ax_congr_red                       true
% 3.85/1.02  --pure_diseq_elim                       true
% 3.85/1.02  --brand_transform                       false
% 3.85/1.02  --non_eq_to_eq                          false
% 3.85/1.02  --prep_def_merge                        true
% 3.85/1.02  --prep_def_merge_prop_impl              false
% 3.85/1.02  --prep_def_merge_mbd                    true
% 3.85/1.02  --prep_def_merge_tr_red                 false
% 3.85/1.02  --prep_def_merge_tr_cl                  false
% 3.85/1.02  --smt_preprocessing                     true
% 3.85/1.02  --smt_ac_axioms                         fast
% 3.85/1.02  --preprocessed_out                      false
% 3.85/1.02  --preprocessed_stats                    false
% 3.85/1.02  
% 3.85/1.02  ------ Abstraction refinement Options
% 3.85/1.02  
% 3.85/1.02  --abstr_ref                             []
% 3.85/1.02  --abstr_ref_prep                        false
% 3.85/1.02  --abstr_ref_until_sat                   false
% 3.85/1.02  --abstr_ref_sig_restrict                funpre
% 3.85/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.02  --abstr_ref_under                       []
% 3.85/1.02  
% 3.85/1.02  ------ SAT Options
% 3.85/1.02  
% 3.85/1.02  --sat_mode                              false
% 3.85/1.02  --sat_fm_restart_options                ""
% 3.85/1.02  --sat_gr_def                            false
% 3.85/1.02  --sat_epr_types                         true
% 3.85/1.02  --sat_non_cyclic_types                  false
% 3.85/1.02  --sat_finite_models                     false
% 3.85/1.02  --sat_fm_lemmas                         false
% 3.85/1.02  --sat_fm_prep                           false
% 3.85/1.02  --sat_fm_uc_incr                        true
% 3.85/1.02  --sat_out_model                         small
% 3.85/1.02  --sat_out_clauses                       false
% 3.85/1.02  
% 3.85/1.02  ------ QBF Options
% 3.85/1.02  
% 3.85/1.02  --qbf_mode                              false
% 3.85/1.02  --qbf_elim_univ                         false
% 3.85/1.02  --qbf_dom_inst                          none
% 3.85/1.02  --qbf_dom_pre_inst                      false
% 3.85/1.02  --qbf_sk_in                             false
% 3.85/1.02  --qbf_pred_elim                         true
% 3.85/1.02  --qbf_split                             512
% 3.85/1.02  
% 3.85/1.02  ------ BMC1 Options
% 3.85/1.02  
% 3.85/1.02  --bmc1_incremental                      false
% 3.85/1.02  --bmc1_axioms                           reachable_all
% 3.85/1.02  --bmc1_min_bound                        0
% 3.85/1.02  --bmc1_max_bound                        -1
% 3.85/1.02  --bmc1_max_bound_default                -1
% 3.85/1.02  --bmc1_symbol_reachability              true
% 3.85/1.02  --bmc1_property_lemmas                  false
% 3.85/1.02  --bmc1_k_induction                      false
% 3.85/1.02  --bmc1_non_equiv_states                 false
% 3.85/1.02  --bmc1_deadlock                         false
% 3.85/1.02  --bmc1_ucm                              false
% 3.85/1.02  --bmc1_add_unsat_core                   none
% 3.85/1.02  --bmc1_unsat_core_children              false
% 3.85/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.02  --bmc1_out_stat                         full
% 3.85/1.02  --bmc1_ground_init                      false
% 3.85/1.02  --bmc1_pre_inst_next_state              false
% 3.85/1.02  --bmc1_pre_inst_state                   false
% 3.85/1.02  --bmc1_pre_inst_reach_state             false
% 3.85/1.02  --bmc1_out_unsat_core                   false
% 3.85/1.02  --bmc1_aig_witness_out                  false
% 3.85/1.02  --bmc1_verbose                          false
% 3.85/1.02  --bmc1_dump_clauses_tptp                false
% 3.85/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.02  --bmc1_dump_file                        -
% 3.85/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.02  --bmc1_ucm_extend_mode                  1
% 3.85/1.02  --bmc1_ucm_init_mode                    2
% 3.85/1.02  --bmc1_ucm_cone_mode                    none
% 3.85/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.02  --bmc1_ucm_relax_model                  4
% 3.85/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.02  --bmc1_ucm_layered_model                none
% 3.85/1.02  --bmc1_ucm_max_lemma_size               10
% 3.85/1.02  
% 3.85/1.02  ------ AIG Options
% 3.85/1.02  
% 3.85/1.02  --aig_mode                              false
% 3.85/1.02  
% 3.85/1.02  ------ Instantiation Options
% 3.85/1.02  
% 3.85/1.02  --instantiation_flag                    true
% 3.85/1.02  --inst_sos_flag                         false
% 3.85/1.02  --inst_sos_phase                        true
% 3.85/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.02  --inst_lit_sel_side                     num_symb
% 3.85/1.02  --inst_solver_per_active                1400
% 3.85/1.02  --inst_solver_calls_frac                1.
% 3.85/1.02  --inst_passive_queue_type               priority_queues
% 3.85/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.02  --inst_passive_queues_freq              [25;2]
% 3.85/1.02  --inst_dismatching                      true
% 3.85/1.02  --inst_eager_unprocessed_to_passive     true
% 3.85/1.02  --inst_prop_sim_given                   true
% 3.85/1.02  --inst_prop_sim_new                     false
% 3.85/1.02  --inst_subs_new                         false
% 3.85/1.02  --inst_eq_res_simp                      false
% 3.85/1.02  --inst_subs_given                       false
% 3.85/1.02  --inst_orphan_elimination               true
% 3.85/1.02  --inst_learning_loop_flag               true
% 3.85/1.02  --inst_learning_start                   3000
% 3.85/1.02  --inst_learning_factor                  2
% 3.85/1.02  --inst_start_prop_sim_after_learn       3
% 3.85/1.02  --inst_sel_renew                        solver
% 3.85/1.02  --inst_lit_activity_flag                true
% 3.85/1.02  --inst_restr_to_given                   false
% 3.85/1.02  --inst_activity_threshold               500
% 3.85/1.02  --inst_out_proof                        true
% 3.85/1.02  
% 3.85/1.02  ------ Resolution Options
% 3.85/1.02  
% 3.85/1.02  --resolution_flag                       true
% 3.85/1.02  --res_lit_sel                           adaptive
% 3.85/1.02  --res_lit_sel_side                      none
% 3.85/1.02  --res_ordering                          kbo
% 3.85/1.02  --res_to_prop_solver                    active
% 3.85/1.02  --res_prop_simpl_new                    false
% 3.85/1.02  --res_prop_simpl_given                  true
% 3.85/1.02  --res_passive_queue_type                priority_queues
% 3.85/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.02  --res_passive_queues_freq               [15;5]
% 3.85/1.02  --res_forward_subs                      full
% 3.85/1.02  --res_backward_subs                     full
% 3.85/1.02  --res_forward_subs_resolution           true
% 3.85/1.02  --res_backward_subs_resolution          true
% 3.85/1.02  --res_orphan_elimination                true
% 3.85/1.02  --res_time_limit                        2.
% 3.85/1.02  --res_out_proof                         true
% 3.85/1.02  
% 3.85/1.02  ------ Superposition Options
% 3.85/1.02  
% 3.85/1.02  --superposition_flag                    true
% 3.85/1.02  --sup_passive_queue_type                priority_queues
% 3.85/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.02  --demod_completeness_check              fast
% 3.85/1.02  --demod_use_ground                      true
% 3.85/1.02  --sup_to_prop_solver                    passive
% 3.85/1.02  --sup_prop_simpl_new                    true
% 3.85/1.02  --sup_prop_simpl_given                  true
% 3.85/1.02  --sup_fun_splitting                     false
% 3.85/1.02  --sup_smt_interval                      50000
% 3.85/1.02  
% 3.85/1.02  ------ Superposition Simplification Setup
% 3.85/1.02  
% 3.85/1.02  --sup_indices_passive                   []
% 3.85/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.02  --sup_full_bw                           [BwDemod]
% 3.85/1.02  --sup_immed_triv                        [TrivRules]
% 3.85/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.02  --sup_immed_bw_main                     []
% 3.85/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.02  
% 3.85/1.02  ------ Combination Options
% 3.85/1.02  
% 3.85/1.02  --comb_res_mult                         3
% 3.85/1.02  --comb_sup_mult                         2
% 3.85/1.02  --comb_inst_mult                        10
% 3.85/1.02  
% 3.85/1.02  ------ Debug Options
% 3.85/1.02  
% 3.85/1.02  --dbg_backtrace                         false
% 3.85/1.02  --dbg_dump_prop_clauses                 false
% 3.85/1.02  --dbg_dump_prop_clauses_file            -
% 3.85/1.02  --dbg_out_stat                          false
% 3.85/1.02  ------ Parsing...
% 3.85/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.85/1.02  
% 3.85/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.85/1.02  ------ Proving...
% 3.85/1.02  ------ Problem Properties 
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  clauses                                 22
% 3.85/1.02  conjectures                             2
% 3.85/1.02  EPR                                     4
% 3.85/1.02  Horn                                    18
% 3.85/1.02  unary                                   7
% 3.85/1.02  binary                                  5
% 3.85/1.02  lits                                    58
% 3.85/1.02  lits eq                                 4
% 3.85/1.02  fd_pure                                 0
% 3.85/1.02  fd_pseudo                               0
% 3.85/1.02  fd_cond                                 0
% 3.85/1.02  fd_pseudo_cond                          1
% 3.85/1.02  AC symbols                              0
% 3.85/1.02  
% 3.85/1.02  ------ Schedule dynamic 5 is on 
% 3.85/1.02  
% 3.85/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.85/1.02  
% 3.85/1.02  
% 3.85/1.02  ------ 
% 3.85/1.02  Current options:
% 3.85/1.02  ------ 
% 3.85/1.02  
% 3.85/1.02  ------ Input Options
% 3.85/1.02  
% 3.85/1.02  --out_options                           all
% 3.85/1.02  --tptp_safe_out                         true
% 3.85/1.02  --problem_path                          ""
% 3.85/1.02  --include_path                          ""
% 3.85/1.02  --clausifier                            res/vclausify_rel
% 3.85/1.02  --clausifier_options                    --mode clausify
% 3.85/1.02  --stdin                                 false
% 3.85/1.02  --stats_out                             all
% 3.85/1.02  
% 3.85/1.02  ------ General Options
% 3.85/1.02  
% 3.85/1.02  --fof                                   false
% 3.85/1.02  --time_out_real                         305.
% 3.85/1.02  --time_out_virtual                      -1.
% 3.85/1.02  --symbol_type_check                     false
% 3.85/1.02  --clausify_out                          false
% 3.85/1.02  --sig_cnt_out                           false
% 3.85/1.02  --trig_cnt_out                          false
% 3.85/1.02  --trig_cnt_out_tolerance                1.
% 3.85/1.02  --trig_cnt_out_sk_spl                   false
% 3.85/1.02  --abstr_cl_out                          false
% 3.85/1.02  
% 3.85/1.02  ------ Global Options
% 3.85/1.02  
% 3.85/1.02  --schedule                              default
% 3.85/1.02  --add_important_lit                     false
% 3.85/1.02  --prop_solver_per_cl                    1000
% 3.85/1.02  --min_unsat_core                        false
% 3.85/1.02  --soft_assumptions                      false
% 3.85/1.02  --soft_lemma_size                       3
% 3.85/1.02  --prop_impl_unit_size                   0
% 3.85/1.02  --prop_impl_unit                        []
% 3.85/1.02  --share_sel_clauses                     true
% 3.85/1.02  --reset_solvers                         false
% 3.85/1.02  --bc_imp_inh                            [conj_cone]
% 3.85/1.02  --conj_cone_tolerance                   3.
% 3.85/1.03  --extra_neg_conj                        none
% 3.85/1.03  --large_theory_mode                     true
% 3.85/1.03  --prolific_symb_bound                   200
% 3.85/1.03  --lt_threshold                          2000
% 3.85/1.03  --clause_weak_htbl                      true
% 3.85/1.03  --gc_record_bc_elim                     false
% 3.85/1.03  
% 3.85/1.03  ------ Preprocessing Options
% 3.85/1.03  
% 3.85/1.03  --preprocessing_flag                    true
% 3.85/1.03  --time_out_prep_mult                    0.1
% 3.85/1.03  --splitting_mode                        input
% 3.85/1.03  --splitting_grd                         true
% 3.85/1.03  --splitting_cvd                         false
% 3.85/1.03  --splitting_cvd_svl                     false
% 3.85/1.03  --splitting_nvd                         32
% 3.85/1.03  --sub_typing                            true
% 3.85/1.03  --prep_gs_sim                           true
% 3.85/1.03  --prep_unflatten                        true
% 3.85/1.03  --prep_res_sim                          true
% 3.85/1.03  --prep_upred                            true
% 3.85/1.03  --prep_sem_filter                       exhaustive
% 3.85/1.03  --prep_sem_filter_out                   false
% 3.85/1.03  --pred_elim                             true
% 3.85/1.03  --res_sim_input                         true
% 3.85/1.03  --eq_ax_congr_red                       true
% 3.85/1.03  --pure_diseq_elim                       true
% 3.85/1.03  --brand_transform                       false
% 3.85/1.03  --non_eq_to_eq                          false
% 3.85/1.03  --prep_def_merge                        true
% 3.85/1.03  --prep_def_merge_prop_impl              false
% 3.85/1.03  --prep_def_merge_mbd                    true
% 3.85/1.03  --prep_def_merge_tr_red                 false
% 3.85/1.03  --prep_def_merge_tr_cl                  false
% 3.85/1.03  --smt_preprocessing                     true
% 3.85/1.03  --smt_ac_axioms                         fast
% 3.85/1.03  --preprocessed_out                      false
% 3.85/1.03  --preprocessed_stats                    false
% 3.85/1.03  
% 3.85/1.03  ------ Abstraction refinement Options
% 3.85/1.03  
% 3.85/1.03  --abstr_ref                             []
% 3.85/1.03  --abstr_ref_prep                        false
% 3.85/1.03  --abstr_ref_until_sat                   false
% 3.85/1.03  --abstr_ref_sig_restrict                funpre
% 3.85/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.85/1.03  --abstr_ref_under                       []
% 3.85/1.03  
% 3.85/1.03  ------ SAT Options
% 3.85/1.03  
% 3.85/1.03  --sat_mode                              false
% 3.85/1.03  --sat_fm_restart_options                ""
% 3.85/1.03  --sat_gr_def                            false
% 3.85/1.03  --sat_epr_types                         true
% 3.85/1.03  --sat_non_cyclic_types                  false
% 3.85/1.03  --sat_finite_models                     false
% 3.85/1.03  --sat_fm_lemmas                         false
% 3.85/1.03  --sat_fm_prep                           false
% 3.85/1.03  --sat_fm_uc_incr                        true
% 3.85/1.03  --sat_out_model                         small
% 3.85/1.03  --sat_out_clauses                       false
% 3.85/1.03  
% 3.85/1.03  ------ QBF Options
% 3.85/1.03  
% 3.85/1.03  --qbf_mode                              false
% 3.85/1.03  --qbf_elim_univ                         false
% 3.85/1.03  --qbf_dom_inst                          none
% 3.85/1.03  --qbf_dom_pre_inst                      false
% 3.85/1.03  --qbf_sk_in                             false
% 3.85/1.03  --qbf_pred_elim                         true
% 3.85/1.03  --qbf_split                             512
% 3.85/1.03  
% 3.85/1.03  ------ BMC1 Options
% 3.85/1.03  
% 3.85/1.03  --bmc1_incremental                      false
% 3.85/1.03  --bmc1_axioms                           reachable_all
% 3.85/1.03  --bmc1_min_bound                        0
% 3.85/1.03  --bmc1_max_bound                        -1
% 3.85/1.03  --bmc1_max_bound_default                -1
% 3.85/1.03  --bmc1_symbol_reachability              true
% 3.85/1.03  --bmc1_property_lemmas                  false
% 3.85/1.03  --bmc1_k_induction                      false
% 3.85/1.03  --bmc1_non_equiv_states                 false
% 3.85/1.03  --bmc1_deadlock                         false
% 3.85/1.03  --bmc1_ucm                              false
% 3.85/1.03  --bmc1_add_unsat_core                   none
% 3.85/1.03  --bmc1_unsat_core_children              false
% 3.85/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.85/1.03  --bmc1_out_stat                         full
% 3.85/1.03  --bmc1_ground_init                      false
% 3.85/1.03  --bmc1_pre_inst_next_state              false
% 3.85/1.03  --bmc1_pre_inst_state                   false
% 3.85/1.03  --bmc1_pre_inst_reach_state             false
% 3.85/1.03  --bmc1_out_unsat_core                   false
% 3.85/1.03  --bmc1_aig_witness_out                  false
% 3.85/1.03  --bmc1_verbose                          false
% 3.85/1.03  --bmc1_dump_clauses_tptp                false
% 3.85/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.85/1.03  --bmc1_dump_file                        -
% 3.85/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.85/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.85/1.03  --bmc1_ucm_extend_mode                  1
% 3.85/1.03  --bmc1_ucm_init_mode                    2
% 3.85/1.03  --bmc1_ucm_cone_mode                    none
% 3.85/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.85/1.03  --bmc1_ucm_relax_model                  4
% 3.85/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.85/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.85/1.03  --bmc1_ucm_layered_model                none
% 3.85/1.03  --bmc1_ucm_max_lemma_size               10
% 3.85/1.03  
% 3.85/1.03  ------ AIG Options
% 3.85/1.03  
% 3.85/1.03  --aig_mode                              false
% 3.85/1.03  
% 3.85/1.03  ------ Instantiation Options
% 3.85/1.03  
% 3.85/1.03  --instantiation_flag                    true
% 3.85/1.03  --inst_sos_flag                         false
% 3.85/1.03  --inst_sos_phase                        true
% 3.85/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.85/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.85/1.03  --inst_lit_sel_side                     none
% 3.85/1.03  --inst_solver_per_active                1400
% 3.85/1.03  --inst_solver_calls_frac                1.
% 3.85/1.03  --inst_passive_queue_type               priority_queues
% 3.85/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.85/1.03  --inst_passive_queues_freq              [25;2]
% 3.85/1.03  --inst_dismatching                      true
% 3.85/1.03  --inst_eager_unprocessed_to_passive     true
% 3.85/1.03  --inst_prop_sim_given                   true
% 3.85/1.03  --inst_prop_sim_new                     false
% 3.85/1.03  --inst_subs_new                         false
% 3.85/1.03  --inst_eq_res_simp                      false
% 3.85/1.03  --inst_subs_given                       false
% 3.85/1.03  --inst_orphan_elimination               true
% 3.85/1.03  --inst_learning_loop_flag               true
% 3.85/1.03  --inst_learning_start                   3000
% 3.85/1.03  --inst_learning_factor                  2
% 3.85/1.03  --inst_start_prop_sim_after_learn       3
% 3.85/1.03  --inst_sel_renew                        solver
% 3.85/1.03  --inst_lit_activity_flag                true
% 3.85/1.03  --inst_restr_to_given                   false
% 3.85/1.03  --inst_activity_threshold               500
% 3.85/1.03  --inst_out_proof                        true
% 3.85/1.03  
% 3.85/1.03  ------ Resolution Options
% 3.85/1.03  
% 3.85/1.03  --resolution_flag                       false
% 3.85/1.03  --res_lit_sel                           adaptive
% 3.85/1.03  --res_lit_sel_side                      none
% 3.85/1.03  --res_ordering                          kbo
% 3.85/1.03  --res_to_prop_solver                    active
% 3.85/1.03  --res_prop_simpl_new                    false
% 3.85/1.03  --res_prop_simpl_given                  true
% 3.85/1.03  --res_passive_queue_type                priority_queues
% 3.85/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.85/1.03  --res_passive_queues_freq               [15;5]
% 3.85/1.03  --res_forward_subs                      full
% 3.85/1.03  --res_backward_subs                     full
% 3.85/1.03  --res_forward_subs_resolution           true
% 3.85/1.03  --res_backward_subs_resolution          true
% 3.85/1.03  --res_orphan_elimination                true
% 3.85/1.03  --res_time_limit                        2.
% 3.85/1.03  --res_out_proof                         true
% 3.85/1.03  
% 3.85/1.03  ------ Superposition Options
% 3.85/1.03  
% 3.85/1.03  --superposition_flag                    true
% 3.85/1.03  --sup_passive_queue_type                priority_queues
% 3.85/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.85/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.85/1.03  --demod_completeness_check              fast
% 3.85/1.03  --demod_use_ground                      true
% 3.85/1.03  --sup_to_prop_solver                    passive
% 3.85/1.03  --sup_prop_simpl_new                    true
% 3.85/1.03  --sup_prop_simpl_given                  true
% 3.85/1.03  --sup_fun_splitting                     false
% 3.85/1.03  --sup_smt_interval                      50000
% 3.85/1.03  
% 3.85/1.03  ------ Superposition Simplification Setup
% 3.85/1.03  
% 3.85/1.03  --sup_indices_passive                   []
% 3.85/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.85/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.85/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.03  --sup_full_bw                           [BwDemod]
% 3.85/1.03  --sup_immed_triv                        [TrivRules]
% 3.85/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.85/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.03  --sup_immed_bw_main                     []
% 3.85/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.85/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.85/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.85/1.03  
% 3.85/1.03  ------ Combination Options
% 3.85/1.03  
% 3.85/1.03  --comb_res_mult                         3
% 3.85/1.03  --comb_sup_mult                         2
% 3.85/1.03  --comb_inst_mult                        10
% 3.85/1.03  
% 3.85/1.03  ------ Debug Options
% 3.85/1.03  
% 3.85/1.03  --dbg_backtrace                         false
% 3.85/1.03  --dbg_dump_prop_clauses                 false
% 3.85/1.03  --dbg_dump_prop_clauses_file            -
% 3.85/1.03  --dbg_out_stat                          false
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  ------ Proving...
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  % SZS status Theorem for theBenchmark.p
% 3.85/1.03  
% 3.85/1.03   Resolution empty clause
% 3.85/1.03  
% 3.85/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.85/1.03  
% 3.85/1.03  fof(f10,conjecture,(
% 3.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f11,negated_conjecture,(
% 3.85/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.85/1.03    inference(negated_conjecture,[],[f10])).
% 3.85/1.03  
% 3.85/1.03  fof(f12,plain,(
% 3.85/1.03    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 3.85/1.03    inference(pure_predicate_removal,[],[f11])).
% 3.85/1.03  
% 3.85/1.03  fof(f22,plain,(
% 3.85/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.85/1.03    inference(ennf_transformation,[],[f12])).
% 3.85/1.03  
% 3.85/1.03  fof(f23,plain,(
% 3.85/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.85/1.03    inference(flattening,[],[f22])).
% 3.85/1.03  
% 3.85/1.03  fof(f37,plain,(
% 3.85/1.03    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f36,plain,(
% 3.85/1.03    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f38,plain,(
% 3.85/1.03    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 3.85/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f23,f37,f36])).
% 3.85/1.03  
% 3.85/1.03  fof(f62,plain,(
% 3.85/1.03    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 3.85/1.03    inference(cnf_transformation,[],[f38])).
% 3.85/1.03  
% 3.85/1.03  fof(f9,axiom,(
% 3.85/1.03    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f20,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(ennf_transformation,[],[f9])).
% 3.85/1.03  
% 3.85/1.03  fof(f21,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(flattening,[],[f20])).
% 3.85/1.03  
% 3.85/1.03  fof(f31,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(nnf_transformation,[],[f21])).
% 3.85/1.03  
% 3.85/1.03  fof(f32,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(rectify,[],[f31])).
% 3.85/1.03  
% 3.85/1.03  fof(f34,plain,(
% 3.85/1.03    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f33,plain,(
% 3.85/1.03    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f35,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).
% 3.85/1.03  
% 3.85/1.03  fof(f56,plain,(
% 3.85/1.03    ( ! [X0,X1] : (v2_tex_2(X1,X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f35])).
% 3.85/1.03  
% 3.85/1.03  fof(f60,plain,(
% 3.85/1.03    l1_pre_topc(sK4)),
% 3.85/1.03    inference(cnf_transformation,[],[f38])).
% 3.85/1.03  
% 3.85/1.03  fof(f4,axiom,(
% 3.85/1.03    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f14,plain,(
% 3.85/1.03    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/1.03    inference(ennf_transformation,[],[f4])).
% 3.85/1.03  
% 3.85/1.03  fof(f15,plain,(
% 3.85/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/1.03    inference(flattening,[],[f14])).
% 3.85/1.03  
% 3.85/1.03  fof(f26,plain,(
% 3.85/1.03    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f27,plain,(
% 3.85/1.03    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.85/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f15,f26])).
% 3.85/1.03  
% 3.85/1.03  fof(f45,plain,(
% 3.85/1.03    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.85/1.03    inference(cnf_transformation,[],[f27])).
% 3.85/1.03  
% 3.85/1.03  fof(f5,axiom,(
% 3.85/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f28,plain,(
% 3.85/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.85/1.03    inference(nnf_transformation,[],[f5])).
% 3.85/1.03  
% 3.85/1.03  fof(f48,plain,(
% 3.85/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f28])).
% 3.85/1.03  
% 3.85/1.03  fof(f6,axiom,(
% 3.85/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f16,plain,(
% 3.85/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.85/1.03    inference(ennf_transformation,[],[f6])).
% 3.85/1.03  
% 3.85/1.03  fof(f49,plain,(
% 3.85/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f16])).
% 3.85/1.03  
% 3.85/1.03  fof(f61,plain,(
% 3.85/1.03    v1_xboole_0(sK5)),
% 3.85/1.03    inference(cnf_transformation,[],[f38])).
% 3.85/1.03  
% 3.85/1.03  fof(f63,plain,(
% 3.85/1.03    ~v2_tex_2(sK5,sK4)),
% 3.85/1.03    inference(cnf_transformation,[],[f38])).
% 3.85/1.03  
% 3.85/1.03  fof(f1,axiom,(
% 3.85/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f24,plain,(
% 3.85/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/1.03    inference(nnf_transformation,[],[f1])).
% 3.85/1.03  
% 3.85/1.03  fof(f25,plain,(
% 3.85/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.85/1.03    inference(flattening,[],[f24])).
% 3.85/1.03  
% 3.85/1.03  fof(f39,plain,(
% 3.85/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.85/1.03    inference(cnf_transformation,[],[f25])).
% 3.85/1.03  
% 3.85/1.03  fof(f65,plain,(
% 3.85/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.85/1.03    inference(equality_resolution,[],[f39])).
% 3.85/1.03  
% 3.85/1.03  fof(f41,plain,(
% 3.85/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f25])).
% 3.85/1.03  
% 3.85/1.03  fof(f8,axiom,(
% 3.85/1.03    ! [X0] : (l1_pre_topc(X0) => ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f19,plain,(
% 3.85/1.03    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(ennf_transformation,[],[f8])).
% 3.85/1.03  
% 3.85/1.03  fof(f29,plain,(
% 3.85/1.03    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.85/1.03    introduced(choice_axiom,[])).
% 3.85/1.03  
% 3.85/1.03  fof(f30,plain,(
% 3.85/1.03    ! [X0] : ((v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.85/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f19,f29])).
% 3.85/1.03  
% 3.85/1.03  fof(f51,plain,(
% 3.85/1.03    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f30])).
% 3.85/1.03  
% 3.85/1.03  fof(f52,plain,(
% 3.85/1.03    ( ! [X0] : (v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f30])).
% 3.85/1.03  
% 3.85/1.03  fof(f57,plain,(
% 3.85/1.03    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f35])).
% 3.85/1.03  
% 3.85/1.03  fof(f47,plain,(
% 3.85/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.85/1.03    inference(cnf_transformation,[],[f28])).
% 3.85/1.03  
% 3.85/1.03  fof(f3,axiom,(
% 3.85/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f13,plain,(
% 3.85/1.03    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.85/1.03    inference(ennf_transformation,[],[f3])).
% 3.85/1.03  
% 3.85/1.03  fof(f43,plain,(
% 3.85/1.03    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.85/1.03    inference(cnf_transformation,[],[f13])).
% 3.85/1.03  
% 3.85/1.03  fof(f58,plain,(
% 3.85/1.03    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f35])).
% 3.85/1.03  
% 3.85/1.03  fof(f7,axiom,(
% 3.85/1.03    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f17,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.85/1.03    inference(ennf_transformation,[],[f7])).
% 3.85/1.03  
% 3.85/1.03  fof(f18,plain,(
% 3.85/1.03    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.85/1.03    inference(flattening,[],[f17])).
% 3.85/1.03  
% 3.85/1.03  fof(f50,plain,(
% 3.85/1.03    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f18])).
% 3.85/1.03  
% 3.85/1.03  fof(f59,plain,(
% 3.85/1.03    v2_pre_topc(sK4)),
% 3.85/1.03    inference(cnf_transformation,[],[f38])).
% 3.85/1.03  
% 3.85/1.03  fof(f2,axiom,(
% 3.85/1.03    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.85/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.85/1.03  
% 3.85/1.03  fof(f42,plain,(
% 3.85/1.03    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.85/1.03    inference(cnf_transformation,[],[f2])).
% 3.85/1.03  
% 3.85/1.03  cnf(c_21,negated_conjecture,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.85/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2375,plain,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_16,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ l1_pre_topc(X1) ),
% 3.85/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_23,negated_conjecture,
% 3.85/1.03      ( l1_pre_topc(sK4) ),
% 3.85/1.03      inference(cnf_transformation,[],[f60]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_617,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | m1_subset_1(sK2(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | sK4 != X1 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_16,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_618,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_617]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2367,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | m1_subset_1(sK2(sK4,X0),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6,plain,
% 3.85/1.03      ( r2_hidden(sK0(X0,X1,X2),X1)
% 3.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.85/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.85/1.03      | r1_tarski(X1,X2) ),
% 3.85/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2379,plain,
% 3.85/1.03      ( r2_hidden(sK0(X0,X1,X2),X1) = iProver_top
% 3.85/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top
% 3.85/1.03      | r1_tarski(X1,X2) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2378,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.85/1.03      | r1_tarski(X0,X1) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.85/1.03      | ~ v1_xboole_0(X2) ),
% 3.85/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_22,negated_conjecture,
% 3.85/1.03      ( v1_xboole_0(sK5) ),
% 3.85/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_704,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) | sK5 != X2 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_705,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(sK5)) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_704]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2373,plain,
% 3.85/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(sK5)) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3120,plain,
% 3.85/1.03      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2378,c_2373]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3684,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | r1_tarski(X2,X0) = iProver_top
% 3.85/1.03      | r1_tarski(X2,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2379,c_3120]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8768,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(X1,sK2(sK4,X0)) = iProver_top
% 3.85/1.03      | r1_tarski(X1,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2367,c_3684]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10069,plain,
% 3.85/1.03      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(X0,sK2(sK4,sK5)) = iProver_top
% 3.85/1.03      | r1_tarski(X0,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2375,c_8768]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_28,plain,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_20,negated_conjecture,
% 3.85/1.03      ( ~ v2_tex_2(sK5,sK4) ),
% 3.85/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_29,plain,
% 3.85/1.03      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f65]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_76,plain,
% 3.85/1.03      ( r1_tarski(sK4,sK4) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_0,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.85/1.03      inference(cnf_transformation,[],[f41]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_80,plain,
% 3.85/1.03      ( ~ r1_tarski(sK4,sK4) | sK4 = sK4 ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1836,plain,
% 3.85/1.03      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.85/1.03      theory(equality) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1847,plain,
% 3.85/1.03      ( u1_struct_0(sK4) = u1_struct_0(sK4) | sK4 != sK4 ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_1836]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2880,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2881,plain,
% 3.85/1.03      ( X0 = sK5
% 3.85/1.03      | r1_tarski(X0,sK5) != iProver_top
% 3.85/1.03      | r1_tarski(sK5,X0) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2880]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1832,plain,
% 3.85/1.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.85/1.03      theory(equality) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_4726,plain,
% 3.85/1.03      ( u1_struct_0(sK4) != u1_struct_0(sK4)
% 3.85/1.03      | k1_zfmisc_1(u1_struct_0(sK4)) = k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_1832]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1833,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.85/1.03      theory(equality) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2590,plain,
% 3.85/1.03      ( m1_subset_1(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
% 3.85/1.03      | X0 != X2
% 3.85/1.03      | X1 != k1_zfmisc_1(X3) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_1833]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2923,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/1.03      | m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.85/1.03      | X2 != X0
% 3.85/1.03      | k1_zfmisc_1(X1) != k1_zfmisc_1(X1) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2590]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3652,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | X1 != X0
% 3.85/1.03      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2923]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_7550,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | X0 != sK5
% 3.85/1.03      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_3652]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_7551,plain,
% 3.85/1.03      ( X0 != sK5
% 3.85/1.03      | k1_zfmisc_1(u1_struct_0(sK4)) != k1_zfmisc_1(u1_struct_0(sK4))
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_7550]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_13,plain,
% 3.85/1.03      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~ l1_pre_topc(X0) ),
% 3.85/1.03      inference(cnf_transformation,[],[f51]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_540,plain,
% 3.85/1.03      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | sK4 != X0 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_541,plain,
% 3.85/1.03      ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_540]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2371,plain,
% 3.85/1.03      ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_541]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8766,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(X0,sK1(sK4)) = iProver_top
% 3.85/1.03      | r1_tarski(X0,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2371,c_3684]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9159,plain,
% 3.85/1.03      ( r1_tarski(sK5,sK1(sK4)) = iProver_top
% 3.85/1.03      | r1_tarski(sK5,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2375,c_8766]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_26,plain,
% 3.85/1.03      ( l1_pre_topc(sK4) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_48,plain,
% 3.85/1.03      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 3.85/1.03      | l1_pre_topc(X0) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_50,plain,
% 3.85/1.03      ( m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 3.85/1.03      | l1_pre_topc(sK4) != iProver_top ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_48]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2580,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(sK5)) | ~ r1_tarski(X0,sK5) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_8]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2720,plain,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) | ~ r1_tarski(sK5,sK5) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2580]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2722,plain,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(sK5)) = iProver_top
% 3.85/1.03      | r1_tarski(sK5,sK5) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2720]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2721,plain,
% 3.85/1.03      ( r1_tarski(sK5,sK5) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2724,plain,
% 3.85/1.03      ( r1_tarski(sK5,sK5) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2721]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2834,plain,
% 3.85/1.03      ( r2_hidden(sK0(X0,X1,sK1(sK4)),X1)
% 3.85/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 3.85/1.03      | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(X0))
% 3.85/1.03      | r1_tarski(X1,sK1(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3853,plain,
% 3.85/1.03      ( r2_hidden(sK0(u1_struct_0(sK4),X0,sK1(sK4)),X0)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(X0,sK1(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2834]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_4735,plain,
% 3.85/1.03      ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5)
% 3.85/1.03      | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(sK5,sK1(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_3853]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_4736,plain,
% 3.85/1.03      ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5) = iProver_top
% 3.85/1.03      | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(sK5,sK1(sK4)) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_4735]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2943,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,sK5) | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_705]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6836,plain,
% 3.85/1.03      ( ~ r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5)
% 3.85/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(sK5)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_2943]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6837,plain,
% 3.85/1.03      ( r2_hidden(sK0(u1_struct_0(sK4),sK5,sK1(sK4)),sK5) != iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(sK5)) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_6836]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9241,plain,
% 3.85/1.03      ( r1_tarski(sK5,sK1(sK4)) = iProver_top ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_9159,c_26,c_28,c_50,c_2722,c_2724,c_4736,c_6837]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2382,plain,
% 3.85/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_12,plain,
% 3.85/1.03      ( ~ l1_pre_topc(X0) | v1_xboole_0(sK1(X0)) ),
% 3.85/1.03      inference(cnf_transformation,[],[f52]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_547,plain,
% 3.85/1.03      ( v1_xboole_0(sK1(X0)) | sK4 != X0 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_548,plain,
% 3.85/1.03      ( v1_xboole_0(sK1(sK4)) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_547]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_714,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.85/1.03      | sK1(sK4) != X2 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_548]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_715,plain,
% 3.85/1.03      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(sK1(sK4))) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_714]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2364,plain,
% 3.85/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(sK1(sK4))) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3675,plain,
% 3.85/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.85/1.03      | r1_tarski(X1,sK1(sK4)) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2378,c_2364]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3907,plain,
% 3.85/1.03      ( r2_hidden(X0,sK1(sK4)) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2382,c_3675]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_4814,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | m1_subset_1(sK1(sK4),k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2379,c_3907]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_5922,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2371,c_4814]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6145,plain,
% 3.85/1.03      ( r1_tarski(sK1(sK4),sK5) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2375,c_5922]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2383,plain,
% 3.85/1.03      ( X0 = X1
% 3.85/1.03      | r1_tarski(X0,X1) != iProver_top
% 3.85/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6184,plain,
% 3.85/1.03      ( sK1(sK4) = sK5 | r1_tarski(sK5,sK1(sK4)) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_6145,c_2383]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9251,plain,
% 3.85/1.03      ( sK1(sK4) = sK5 ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_9241,c_6184]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_5921,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X1) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2378,c_4814]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_7261,plain,
% 3.85/1.03      ( r1_tarski(X0,X1) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X1) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2378,c_5921]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8007,plain,
% 3.85/1.03      ( r1_tarski(X0,sK1(sK4)) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2382,c_7261]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9268,plain,
% 3.85/1.03      ( r1_tarski(X0,sK5) != iProver_top | r1_tarski(sK5,X0) = iProver_top ),
% 3.85/1.03      inference(demodulation,[status(thm)],[c_9251,c_8007]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10134,plain,
% 3.85/1.03      ( r1_tarski(X0,sK2(sK4,sK5)) = iProver_top
% 3.85/1.03      | r1_tarski(X0,sK5) != iProver_top ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_10069,c_28,c_29,c_76,c_80,c_1847,c_2881,c_4726,c_7551,
% 3.85/1.03                 c_9268]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_15,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | r1_tarski(sK2(X1,X0),X0)
% 3.85/1.03      | ~ l1_pre_topc(X1) ),
% 3.85/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_632,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | r1_tarski(sK2(X1,X0),X0)
% 3.85/1.03      | sK4 != X1 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_633,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(sK2(sK4,X0),X0) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_632]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2366,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3279,plain,
% 3.85/1.03      ( v2_tex_2(sK5,sK4) = iProver_top
% 3.85/1.03      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2375,c_2366]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1132,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(sK2(sK4,X0),X0)
% 3.85/1.03      | sK4 != sK4
% 3.85/1.03      | sK5 != X0 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_633]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1133,plain,
% 3.85/1.03      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(sK2(sK4,sK5),sK5) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_1132]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_1134,plain,
% 3.85/1.03      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_1133]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3426,plain,
% 3.85/1.03      ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_3279,c_28,c_1134]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3780,plain,
% 3.85/1.03      ( sK2(sK4,sK5) = sK5 | r1_tarski(sK5,sK2(sK4,sK5)) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_3426,c_2383]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10145,plain,
% 3.85/1.03      ( sK2(sK4,sK5) = sK5 | r1_tarski(sK5,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_10134,c_3780]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3280,plain,
% 3.85/1.03      ( v2_tex_2(sK1(sK4),sK4) = iProver_top
% 3.85/1.03      | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2371,c_2366]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_5438,plain,
% 3.85/1.03      ( sK2(sK4,sK1(sK4)) = sK1(sK4)
% 3.85/1.03      | v2_tex_2(sK1(sK4),sK4) = iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_3280,c_2383]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2558,plain,
% 3.85/1.03      ( v2_tex_2(sK1(sK4),sK4)
% 3.85/1.03      | ~ m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_633]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2559,plain,
% 3.85/1.03      ( v2_tex_2(sK1(sK4),sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(sK1(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_2558]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3009,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,sK1(sK4)) | ~ r1_tarski(sK1(sK4),X0) | X0 = sK1(sK4) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3934,plain,
% 3.85/1.03      ( ~ r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4))
% 3.85/1.03      | ~ r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4)))
% 3.85/1.03      | sK2(sK4,sK1(sK4)) = sK1(sK4) ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_3009]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3935,plain,
% 3.85/1.03      ( sK2(sK4,sK1(sK4)) = sK1(sK4)
% 3.85/1.03      | r1_tarski(sK2(sK4,sK1(sK4)),sK1(sK4)) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_3934]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8064,plain,
% 3.85/1.03      ( v2_tex_2(sK1(sK4),sK4) = iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),sK2(sK4,sK1(sK4))) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_3280,c_8007]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8117,plain,
% 3.85/1.03      ( v2_tex_2(sK1(sK4),sK4) = iProver_top | sK2(sK4,sK1(sK4)) = sK1(sK4) ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_5438,c_26,c_50,c_2559,c_3935,c_8064]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8118,plain,
% 3.85/1.03      ( sK2(sK4,sK1(sK4)) = sK1(sK4) | v2_tex_2(sK1(sK4),sK4) = iProver_top ),
% 3.85/1.03      inference(renaming,[status(thm)],[c_8117]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9267,plain,
% 3.85/1.03      ( sK2(sK4,sK5) = sK5 | v2_tex_2(sK5,sK4) = iProver_top ),
% 3.85/1.03      inference(demodulation,[status(thm)],[c_9251,c_8118]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10336,plain,
% 3.85/1.03      ( sK2(sK4,sK5) = sK5 ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_10145,c_29,c_9267]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.85/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2377,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.85/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2967,plain,
% 3.85/1.03      ( r1_tarski(sK5,u1_struct_0(sK4)) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2375,c_2377]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_4,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.85/1.03      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.85/1.03      inference(cnf_transformation,[],[f43]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_188,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.85/1.03      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_189,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.85/1.03      inference(renaming,[status(thm)],[c_188]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_234,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.85/1.03      inference(bin_hyper_res,[status(thm)],[c_4,c_189]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2374,plain,
% 3.85/1.03      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.85/1.03      | r1_tarski(X2,X0) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_234]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_5720,plain,
% 3.85/1.03      ( k9_subset_1(u1_struct_0(sK4),X0,sK5) = k3_xboole_0(X0,sK5) ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2967,c_2374]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_14,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ v3_pre_topc(X2,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ l1_pre_topc(X1)
% 3.85/1.03      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 3.85/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_647,plain,
% 3.85/1.03      ( v2_tex_2(X0,X1)
% 3.85/1.03      | ~ v3_pre_topc(X2,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 3.85/1.03      | sK4 != X1 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_648,plain,
% 3.85/1.03      ( v2_tex_2(X0,sK4)
% 3.85/1.03      | ~ v3_pre_topc(X1,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_647]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2365,plain,
% 3.85/1.03      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
% 3.85/1.03      | v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | v3_pre_topc(X1,sK4) != iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6017,plain,
% 3.85/1.03      ( sK2(sK4,X0) != k3_xboole_0(X0,sK5)
% 3.85/1.03      | v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | v3_pre_topc(sK5,sK4) != iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_5720,c_2365]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_11,plain,
% 3.85/1.03      ( v3_pre_topc(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ v2_pre_topc(X1)
% 3.85/1.03      | ~ l1_pre_topc(X1)
% 3.85/1.03      | ~ v1_xboole_0(X0) ),
% 3.85/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_24,negated_conjecture,
% 3.85/1.03      ( v2_pre_topc(sK4) ),
% 3.85/1.03      inference(cnf_transformation,[],[f59]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_326,plain,
% 3.85/1.03      ( v3_pre_topc(X0,X1)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.85/1.03      | ~ l1_pre_topc(X1)
% 3.85/1.03      | ~ v1_xboole_0(X0)
% 3.85/1.03      | sK4 != X1 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_24]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_327,plain,
% 3.85/1.03      ( v3_pre_topc(X0,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ l1_pre_topc(sK4)
% 3.85/1.03      | ~ v1_xboole_0(X0) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_326]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_331,plain,
% 3.85/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | v3_pre_topc(X0,sK4)
% 3.85/1.03      | ~ v1_xboole_0(X0) ),
% 3.85/1.03      inference(global_propositional_subsumption,[status(thm)],[c_327,c_23]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_332,plain,
% 3.85/1.03      ( v3_pre_topc(X0,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | ~ v1_xboole_0(X0) ),
% 3.85/1.03      inference(renaming,[status(thm)],[c_331]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_393,plain,
% 3.85/1.03      ( v3_pre_topc(X0,sK4)
% 3.85/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 3.85/1.03      | sK5 != X0 ),
% 3.85/1.03      inference(resolution_lifted,[status(thm)],[c_332,c_22]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_394,plain,
% 3.85/1.03      ( v3_pre_topc(sK5,sK4)
% 3.85/1.03      | ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 3.85/1.03      inference(unflattening,[status(thm)],[c_393]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_395,plain,
% 3.85/1.03      ( v3_pre_topc(sK5,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6786,plain,
% 3.85/1.03      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 3.85/1.03      | sK2(sK4,X0) != k3_xboole_0(X0,sK5)
% 3.85/1.03      | v2_tex_2(X0,sK4) = iProver_top ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_6017,c_28,c_395]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_6787,plain,
% 3.85/1.03      ( sK2(sK4,X0) != k3_xboole_0(X0,sK5)
% 3.85/1.03      | v2_tex_2(X0,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(renaming,[status(thm)],[c_6786]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_10365,plain,
% 3.85/1.03      ( k3_xboole_0(sK5,sK5) != sK5
% 3.85/1.03      | v2_tex_2(sK5,sK4) = iProver_top
% 3.85/1.03      | m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_10336,c_6787]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_15606,plain,
% 3.85/1.03      ( k3_xboole_0(sK5,sK5) != sK5 ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_10365,c_28,c_29]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3,plain,
% 3.85/1.03      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.85/1.03      inference(cnf_transformation,[],[f42]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_2381,plain,
% 3.85/1.03      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8009,plain,
% 3.85/1.03      ( r1_tarski(X0,sK5) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) = iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_6145,c_7261]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8188,plain,
% 3.85/1.03      ( sK1(sK4) = X0
% 3.85/1.03      | r1_tarski(X0,sK1(sK4)) != iProver_top
% 3.85/1.03      | r1_tarski(X0,sK5) != iProver_top ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_8009,c_2383]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3995,plain,
% 3.85/1.03      ( ~ r1_tarski(X0,sK1(sK4)) | ~ r1_tarski(sK1(sK4),X0) | sK1(sK4) = X0 ),
% 3.85/1.03      inference(instantiation,[status(thm)],[c_0]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_3996,plain,
% 3.85/1.03      ( sK1(sK4) = X0
% 3.85/1.03      | r1_tarski(X0,sK1(sK4)) != iProver_top
% 3.85/1.03      | r1_tarski(sK1(sK4),X0) != iProver_top ),
% 3.85/1.03      inference(predicate_to_equality,[status(thm)],[c_3995]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8818,plain,
% 3.85/1.03      ( r1_tarski(X0,sK1(sK4)) != iProver_top | sK1(sK4) = X0 ),
% 3.85/1.03      inference(global_propositional_subsumption,
% 3.85/1.03                [status(thm)],
% 3.85/1.03                [c_8188,c_3996,c_8007]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_8819,plain,
% 3.85/1.03      ( sK1(sK4) = X0 | r1_tarski(X0,sK1(sK4)) != iProver_top ),
% 3.85/1.03      inference(renaming,[status(thm)],[c_8818]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_9263,plain,
% 3.85/1.03      ( sK5 = X0 | r1_tarski(X0,sK5) != iProver_top ),
% 3.85/1.03      inference(demodulation,[status(thm)],[c_9251,c_8819]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_13391,plain,
% 3.85/1.03      ( k3_xboole_0(sK5,X0) = sK5 ),
% 3.85/1.03      inference(superposition,[status(thm)],[c_2381,c_9263]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_15608,plain,
% 3.85/1.03      ( sK5 != sK5 ),
% 3.85/1.03      inference(demodulation,[status(thm)],[c_15606,c_13391]) ).
% 3.85/1.03  
% 3.85/1.03  cnf(c_15609,plain,
% 3.85/1.03      ( $false ),
% 3.85/1.03      inference(equality_resolution_simp,[status(thm)],[c_15608]) ).
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.85/1.03  
% 3.85/1.03  ------                               Statistics
% 3.85/1.03  
% 3.85/1.03  ------ General
% 3.85/1.03  
% 3.85/1.03  abstr_ref_over_cycles:                  0
% 3.85/1.03  abstr_ref_under_cycles:                 0
% 3.85/1.03  gc_basic_clause_elim:                   0
% 3.85/1.03  forced_gc_time:                         0
% 3.85/1.03  parsing_time:                           0.012
% 3.85/1.03  unif_index_cands_time:                  0.
% 3.85/1.03  unif_index_add_time:                    0.
% 3.85/1.03  orderings_time:                         0.
% 3.85/1.03  out_proof_time:                         0.014
% 3.85/1.03  total_time:                             0.43
% 3.85/1.03  num_of_symbols:                         49
% 3.85/1.03  num_of_terms:                           12053
% 3.85/1.03  
% 3.85/1.03  ------ Preprocessing
% 3.85/1.03  
% 3.85/1.03  num_of_splits:                          0
% 3.85/1.03  num_of_split_atoms:                     0
% 3.85/1.03  num_of_reused_defs:                     0
% 3.85/1.03  num_eq_ax_congr_red:                    37
% 3.85/1.03  num_of_sem_filtered_clauses:            1
% 3.85/1.03  num_of_subtypes:                        0
% 3.85/1.03  monotx_restored_types:                  0
% 3.85/1.03  sat_num_of_epr_types:                   0
% 3.85/1.03  sat_num_of_non_cyclic_types:            0
% 3.85/1.03  sat_guarded_non_collapsed_types:        0
% 3.85/1.03  num_pure_diseq_elim:                    0
% 3.85/1.03  simp_replaced_by:                       0
% 3.85/1.03  res_preprocessed:                       117
% 3.85/1.03  prep_upred:                             0
% 3.85/1.03  prep_unflattend:                        46
% 3.85/1.03  smt_new_axioms:                         0
% 3.85/1.03  pred_elim_cands:                        5
% 3.85/1.03  pred_elim:                              3
% 3.85/1.03  pred_elim_cl:                           2
% 3.85/1.03  pred_elim_cycles:                       12
% 3.85/1.03  merged_defs:                            8
% 3.85/1.03  merged_defs_ncl:                        0
% 3.85/1.03  bin_hyper_res:                          11
% 3.85/1.03  prep_cycles:                            4
% 3.85/1.03  pred_elim_time:                         0.035
% 3.85/1.03  splitting_time:                         0.
% 3.85/1.03  sem_filter_time:                        0.
% 3.85/1.03  monotx_time:                            0.001
% 3.85/1.03  subtype_inf_time:                       0.
% 3.85/1.03  
% 3.85/1.03  ------ Problem properties
% 3.85/1.03  
% 3.85/1.03  clauses:                                22
% 3.85/1.03  conjectures:                            2
% 3.85/1.03  epr:                                    4
% 3.85/1.03  horn:                                   18
% 3.85/1.03  ground:                                 5
% 3.85/1.03  unary:                                  7
% 3.85/1.03  binary:                                 5
% 3.85/1.03  lits:                                   58
% 3.85/1.03  lits_eq:                                4
% 3.85/1.03  fd_pure:                                0
% 3.85/1.03  fd_pseudo:                              0
% 3.85/1.03  fd_cond:                                0
% 3.85/1.03  fd_pseudo_cond:                         1
% 3.85/1.03  ac_symbols:                             0
% 3.85/1.03  
% 3.85/1.03  ------ Propositional Solver
% 3.85/1.03  
% 3.85/1.03  prop_solver_calls:                      29
% 3.85/1.03  prop_fast_solver_calls:                 1579
% 3.85/1.03  smt_solver_calls:                       0
% 3.85/1.03  smt_fast_solver_calls:                  0
% 3.85/1.03  prop_num_of_clauses:                    5204
% 3.85/1.03  prop_preprocess_simplified:             13249
% 3.85/1.03  prop_fo_subsumed:                       51
% 3.85/1.03  prop_solver_time:                       0.
% 3.85/1.03  smt_solver_time:                        0.
% 3.85/1.03  smt_fast_solver_time:                   0.
% 3.85/1.03  prop_fast_solver_time:                  0.
% 3.85/1.03  prop_unsat_core_time:                   0.
% 3.85/1.03  
% 3.85/1.03  ------ QBF
% 3.85/1.03  
% 3.85/1.03  qbf_q_res:                              0
% 3.85/1.03  qbf_num_tautologies:                    0
% 3.85/1.03  qbf_prep_cycles:                        0
% 3.85/1.03  
% 3.85/1.03  ------ BMC1
% 3.85/1.03  
% 3.85/1.03  bmc1_current_bound:                     -1
% 3.85/1.03  bmc1_last_solved_bound:                 -1
% 3.85/1.03  bmc1_unsat_core_size:                   -1
% 3.85/1.03  bmc1_unsat_core_parents_size:           -1
% 3.85/1.03  bmc1_merge_next_fun:                    0
% 3.85/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.85/1.03  
% 3.85/1.03  ------ Instantiation
% 3.85/1.03  
% 3.85/1.03  inst_num_of_clauses:                    1537
% 3.85/1.03  inst_num_in_passive:                    613
% 3.85/1.03  inst_num_in_active:                     572
% 3.85/1.03  inst_num_in_unprocessed:                352
% 3.85/1.03  inst_num_of_loops:                      720
% 3.85/1.03  inst_num_of_learning_restarts:          0
% 3.85/1.03  inst_num_moves_active_passive:          146
% 3.85/1.03  inst_lit_activity:                      0
% 3.85/1.03  inst_lit_activity_moves:                0
% 3.85/1.03  inst_num_tautologies:                   0
% 3.85/1.03  inst_num_prop_implied:                  0
% 3.85/1.03  inst_num_existing_simplified:           0
% 3.85/1.03  inst_num_eq_res_simplified:             0
% 3.85/1.03  inst_num_child_elim:                    0
% 3.85/1.03  inst_num_of_dismatching_blockings:      490
% 3.85/1.03  inst_num_of_non_proper_insts:           1882
% 3.85/1.03  inst_num_of_duplicates:                 0
% 3.85/1.03  inst_inst_num_from_inst_to_res:         0
% 3.85/1.03  inst_dismatching_checking_time:         0.
% 3.85/1.03  
% 3.85/1.03  ------ Resolution
% 3.85/1.03  
% 3.85/1.03  res_num_of_clauses:                     0
% 3.85/1.03  res_num_in_passive:                     0
% 3.85/1.03  res_num_in_active:                      0
% 3.85/1.03  res_num_of_loops:                       121
% 3.85/1.03  res_forward_subset_subsumed:            183
% 3.85/1.03  res_backward_subset_subsumed:           2
% 3.85/1.03  res_forward_subsumed:                   0
% 3.85/1.03  res_backward_subsumed:                  0
% 3.85/1.03  res_forward_subsumption_resolution:     2
% 3.85/1.03  res_backward_subsumption_resolution:    0
% 3.85/1.03  res_clause_to_clause_subsumption:       2964
% 3.85/1.03  res_orphan_elimination:                 0
% 3.85/1.03  res_tautology_del:                      167
% 3.85/1.03  res_num_eq_res_simplified:              0
% 3.85/1.03  res_num_sel_changes:                    0
% 3.85/1.03  res_moves_from_active_to_pass:          0
% 3.85/1.03  
% 3.85/1.03  ------ Superposition
% 3.85/1.03  
% 3.85/1.03  sup_time_total:                         0.
% 3.85/1.03  sup_time_generating:                    0.
% 3.85/1.03  sup_time_sim_full:                      0.
% 3.85/1.03  sup_time_sim_immed:                     0.
% 3.85/1.03  
% 3.85/1.03  sup_num_of_clauses:                     221
% 3.85/1.03  sup_num_in_active:                      85
% 3.85/1.03  sup_num_in_passive:                     136
% 3.85/1.03  sup_num_of_loops:                       142
% 3.85/1.03  sup_fw_superposition:                   253
% 3.85/1.03  sup_bw_superposition:                   153
% 3.85/1.03  sup_immediate_simplified:               93
% 3.85/1.03  sup_given_eliminated:                   3
% 3.85/1.03  comparisons_done:                       0
% 3.85/1.03  comparisons_avoided:                    3
% 3.85/1.03  
% 3.85/1.03  ------ Simplifications
% 3.85/1.03  
% 3.85/1.03  
% 3.85/1.03  sim_fw_subset_subsumed:                 41
% 3.85/1.03  sim_bw_subset_subsumed:                 7
% 3.85/1.03  sim_fw_subsumed:                        41
% 3.85/1.03  sim_bw_subsumed:                        3
% 3.85/1.03  sim_fw_subsumption_res:                 2
% 3.85/1.03  sim_bw_subsumption_res:                 2
% 3.85/1.03  sim_tautology_del:                      31
% 3.85/1.03  sim_eq_tautology_del:                   7
% 3.85/1.03  sim_eq_res_simp:                        2
% 3.85/1.03  sim_fw_demodulated:                     5
% 3.85/1.03  sim_bw_demodulated:                     54
% 3.85/1.03  sim_light_normalised:                   33
% 3.85/1.03  sim_joinable_taut:                      0
% 3.85/1.03  sim_joinable_simp:                      0
% 3.85/1.03  sim_ac_normalised:                      0
% 3.85/1.03  sim_smt_subsumption:                    0
% 3.85/1.03  
%------------------------------------------------------------------------------
