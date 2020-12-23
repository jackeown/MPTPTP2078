%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:13 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 376 expanded)
%              Number of clauses        :   73 ( 135 expanded)
%              Number of leaves         :   18 (  83 expanded)
%              Depth                    :   19
%              Number of atoms          :  392 (1413 expanded)
%              Number of equality atoms :  106 ( 198 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
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

fof(f42,plain,
    ( ~ v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f41,f40])).

fof(f65,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f36,plain,(
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
    inference(rectify,[],[f35])).

fof(f38,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4
        & v4_pre_topc(sK2(X0,X1,X4),X0)
        & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f66,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f67,plain,(
    ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f63,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2390,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_2397,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2392,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_319,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_22])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r2_hidden(X1,X0) ),
    inference(unflattening,[status(thm)],[c_319])).

cnf(c_2384,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_320])).

cnf(c_3867,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r2_hidden(X1,k9_subset_1(sK4,X2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2392,c_2384])).

cnf(c_4067,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k9_subset_1(sK4,X1,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_3867])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2393,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2411,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2393,c_6])).

cnf(c_2964,plain,
    ( r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2411,c_2384])).

cnf(c_3723,plain,
    ( r1_tarski(sK4,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2397,c_2964])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2395,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_5449,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3723,c_2395])).

cnf(c_7891,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k9_subset_1(k1_xboole_0,X1,X0),X2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4067,c_5449])).

cnf(c_7901,plain,
    ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7891,c_2395])).

cnf(c_7925,plain,
    ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2390,c_7901])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2391,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3824,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2390,c_2391])).

cnf(c_8717,plain,
    ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7925,c_3824])).

cnf(c_8726,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8717])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_2394,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4668,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_2390,c_2394])).

cnf(c_6175,plain,
    ( k9_subset_1(X0,k1_xboole_0,X1) = k3_xboole_0(X1,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_4668,c_3824])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_535,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_23])).

cnf(c_536,plain,
    ( v2_tex_2(X0,sK3)
    | ~ v4_pre_topc(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_535])).

cnf(c_2377,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
    | v2_tex_2(X0,sK3) = iProver_top
    | v4_pre_topc(X1,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_536])).

cnf(c_6182,plain,
    ( k3_xboole_0(X0,k1_xboole_0) != sK1(sK3,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6175,c_2377])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2387,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_520,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK1(X1,X0),X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_521,plain,
    ( v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_2378,plain,
    ( v2_tex_2(X0,sK3) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2813,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top
    | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2387,c_2378])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_20,negated_conjecture,
    ( ~ v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,X0),X0)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_521])).

cnf(c_1140,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK1(sK3,sK4),sK4) ),
    inference(unflattening,[status(thm)],[c_1139])).

cnf(c_1141,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1140])).

cnf(c_3047,plain,
    ( r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2813,c_28,c_1141])).

cnf(c_5464,plain,
    ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5449,c_3047])).

cnf(c_5647,plain,
    ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5464,c_2395])).

cnf(c_6191,plain,
    ( k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | v4_pre_topc(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6182,c_5647])).

cnf(c_6215,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK3) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6191])).

cnf(c_2388,plain,
    ( v2_tex_2(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5468,plain,
    ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5449,c_2388])).

cnf(c_2575,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2579,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2575])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_13,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_272,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_24])).

cnf(c_273,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_277,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(X0,sK3)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_273,c_23])).

cnf(c_278,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_277])).

cnf(c_309,plain,
    ( v4_pre_topc(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_278])).

cnf(c_310,plain,
    ( v4_pre_topc(k1_xboole_0,sK3)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(unflattening,[status(thm)],[c_309])).

cnf(c_316,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_310,c_10])).

cnf(c_318,plain,
    ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8726,c_6215,c_5468,c_2579,c_318])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.85/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.85/1.01  
% 2.85/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.85/1.01  
% 2.85/1.01  ------  iProver source info
% 2.85/1.01  
% 2.85/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.85/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.85/1.01  git: non_committed_changes: false
% 2.85/1.01  git: last_make_outside_of_git: false
% 2.85/1.01  
% 2.85/1.01  ------ 
% 2.85/1.01  
% 2.85/1.01  ------ Input Options
% 2.85/1.01  
% 2.85/1.01  --out_options                           all
% 2.85/1.01  --tptp_safe_out                         true
% 2.85/1.01  --problem_path                          ""
% 2.85/1.01  --include_path                          ""
% 2.85/1.01  --clausifier                            res/vclausify_rel
% 2.85/1.01  --clausifier_options                    --mode clausify
% 2.85/1.01  --stdin                                 false
% 2.85/1.01  --stats_out                             all
% 2.85/1.01  
% 2.85/1.01  ------ General Options
% 2.85/1.01  
% 2.85/1.01  --fof                                   false
% 2.85/1.01  --time_out_real                         305.
% 2.85/1.01  --time_out_virtual                      -1.
% 2.85/1.01  --symbol_type_check                     false
% 2.85/1.01  --clausify_out                          false
% 2.85/1.01  --sig_cnt_out                           false
% 2.85/1.01  --trig_cnt_out                          false
% 2.85/1.01  --trig_cnt_out_tolerance                1.
% 2.85/1.01  --trig_cnt_out_sk_spl                   false
% 2.85/1.01  --abstr_cl_out                          false
% 2.85/1.01  
% 2.85/1.01  ------ Global Options
% 2.85/1.01  
% 2.85/1.01  --schedule                              default
% 2.85/1.01  --add_important_lit                     false
% 2.85/1.01  --prop_solver_per_cl                    1000
% 2.85/1.01  --min_unsat_core                        false
% 2.85/1.01  --soft_assumptions                      false
% 2.85/1.01  --soft_lemma_size                       3
% 2.85/1.01  --prop_impl_unit_size                   0
% 2.85/1.01  --prop_impl_unit                        []
% 2.85/1.01  --share_sel_clauses                     true
% 2.85/1.01  --reset_solvers                         false
% 2.85/1.01  --bc_imp_inh                            [conj_cone]
% 2.85/1.01  --conj_cone_tolerance                   3.
% 2.85/1.01  --extra_neg_conj                        none
% 2.85/1.01  --large_theory_mode                     true
% 2.85/1.01  --prolific_symb_bound                   200
% 2.85/1.01  --lt_threshold                          2000
% 2.85/1.01  --clause_weak_htbl                      true
% 2.85/1.01  --gc_record_bc_elim                     false
% 2.85/1.01  
% 2.85/1.01  ------ Preprocessing Options
% 2.85/1.01  
% 2.85/1.01  --preprocessing_flag                    true
% 2.85/1.01  --time_out_prep_mult                    0.1
% 2.85/1.01  --splitting_mode                        input
% 2.85/1.01  --splitting_grd                         true
% 2.85/1.01  --splitting_cvd                         false
% 2.85/1.01  --splitting_cvd_svl                     false
% 2.85/1.01  --splitting_nvd                         32
% 2.85/1.01  --sub_typing                            true
% 2.85/1.01  --prep_gs_sim                           true
% 2.85/1.01  --prep_unflatten                        true
% 2.85/1.01  --prep_res_sim                          true
% 2.85/1.01  --prep_upred                            true
% 2.85/1.01  --prep_sem_filter                       exhaustive
% 2.85/1.01  --prep_sem_filter_out                   false
% 2.85/1.01  --pred_elim                             true
% 2.85/1.01  --res_sim_input                         true
% 2.85/1.01  --eq_ax_congr_red                       true
% 2.85/1.01  --pure_diseq_elim                       true
% 2.85/1.01  --brand_transform                       false
% 2.85/1.01  --non_eq_to_eq                          false
% 2.85/1.01  --prep_def_merge                        true
% 2.85/1.01  --prep_def_merge_prop_impl              false
% 2.85/1.01  --prep_def_merge_mbd                    true
% 2.85/1.01  --prep_def_merge_tr_red                 false
% 2.85/1.01  --prep_def_merge_tr_cl                  false
% 2.85/1.01  --smt_preprocessing                     true
% 2.85/1.01  --smt_ac_axioms                         fast
% 2.85/1.01  --preprocessed_out                      false
% 2.85/1.01  --preprocessed_stats                    false
% 2.85/1.01  
% 2.85/1.01  ------ Abstraction refinement Options
% 2.85/1.01  
% 2.85/1.01  --abstr_ref                             []
% 2.85/1.01  --abstr_ref_prep                        false
% 2.85/1.01  --abstr_ref_until_sat                   false
% 2.85/1.01  --abstr_ref_sig_restrict                funpre
% 2.85/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/1.01  --abstr_ref_under                       []
% 2.85/1.01  
% 2.85/1.01  ------ SAT Options
% 2.85/1.01  
% 2.85/1.01  --sat_mode                              false
% 2.85/1.01  --sat_fm_restart_options                ""
% 2.85/1.01  --sat_gr_def                            false
% 2.85/1.01  --sat_epr_types                         true
% 2.85/1.01  --sat_non_cyclic_types                  false
% 2.85/1.01  --sat_finite_models                     false
% 2.85/1.01  --sat_fm_lemmas                         false
% 2.85/1.01  --sat_fm_prep                           false
% 2.85/1.01  --sat_fm_uc_incr                        true
% 2.85/1.01  --sat_out_model                         small
% 2.85/1.01  --sat_out_clauses                       false
% 2.85/1.01  
% 2.85/1.01  ------ QBF Options
% 2.85/1.01  
% 2.85/1.01  --qbf_mode                              false
% 2.85/1.01  --qbf_elim_univ                         false
% 2.85/1.01  --qbf_dom_inst                          none
% 2.85/1.01  --qbf_dom_pre_inst                      false
% 2.85/1.01  --qbf_sk_in                             false
% 2.85/1.01  --qbf_pred_elim                         true
% 2.85/1.01  --qbf_split                             512
% 2.85/1.01  
% 2.85/1.01  ------ BMC1 Options
% 2.85/1.01  
% 2.85/1.01  --bmc1_incremental                      false
% 2.85/1.01  --bmc1_axioms                           reachable_all
% 2.85/1.01  --bmc1_min_bound                        0
% 2.85/1.01  --bmc1_max_bound                        -1
% 2.85/1.01  --bmc1_max_bound_default                -1
% 2.85/1.01  --bmc1_symbol_reachability              true
% 2.85/1.01  --bmc1_property_lemmas                  false
% 2.85/1.01  --bmc1_k_induction                      false
% 2.85/1.01  --bmc1_non_equiv_states                 false
% 2.85/1.01  --bmc1_deadlock                         false
% 2.85/1.01  --bmc1_ucm                              false
% 2.85/1.01  --bmc1_add_unsat_core                   none
% 2.85/1.01  --bmc1_unsat_core_children              false
% 2.85/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/1.01  --bmc1_out_stat                         full
% 2.85/1.01  --bmc1_ground_init                      false
% 2.85/1.01  --bmc1_pre_inst_next_state              false
% 2.85/1.01  --bmc1_pre_inst_state                   false
% 2.85/1.01  --bmc1_pre_inst_reach_state             false
% 2.85/1.01  --bmc1_out_unsat_core                   false
% 2.85/1.01  --bmc1_aig_witness_out                  false
% 2.85/1.01  --bmc1_verbose                          false
% 2.85/1.01  --bmc1_dump_clauses_tptp                false
% 2.85/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.85/1.01  --bmc1_dump_file                        -
% 2.85/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.85/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.85/1.01  --bmc1_ucm_extend_mode                  1
% 2.85/1.01  --bmc1_ucm_init_mode                    2
% 2.85/1.01  --bmc1_ucm_cone_mode                    none
% 2.85/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.85/1.01  --bmc1_ucm_relax_model                  4
% 2.85/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.85/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/1.01  --bmc1_ucm_layered_model                none
% 2.85/1.01  --bmc1_ucm_max_lemma_size               10
% 2.85/1.01  
% 2.85/1.01  ------ AIG Options
% 2.85/1.01  
% 2.85/1.01  --aig_mode                              false
% 2.85/1.01  
% 2.85/1.01  ------ Instantiation Options
% 2.85/1.01  
% 2.85/1.01  --instantiation_flag                    true
% 2.85/1.01  --inst_sos_flag                         false
% 2.85/1.01  --inst_sos_phase                        true
% 2.85/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/1.01  --inst_lit_sel_side                     num_symb
% 2.85/1.01  --inst_solver_per_active                1400
% 2.85/1.01  --inst_solver_calls_frac                1.
% 2.85/1.01  --inst_passive_queue_type               priority_queues
% 2.85/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/1.01  --inst_passive_queues_freq              [25;2]
% 2.85/1.01  --inst_dismatching                      true
% 2.85/1.01  --inst_eager_unprocessed_to_passive     true
% 2.85/1.01  --inst_prop_sim_given                   true
% 2.85/1.01  --inst_prop_sim_new                     false
% 2.85/1.01  --inst_subs_new                         false
% 2.85/1.01  --inst_eq_res_simp                      false
% 2.85/1.01  --inst_subs_given                       false
% 2.85/1.01  --inst_orphan_elimination               true
% 2.85/1.01  --inst_learning_loop_flag               true
% 2.85/1.01  --inst_learning_start                   3000
% 2.85/1.01  --inst_learning_factor                  2
% 2.85/1.01  --inst_start_prop_sim_after_learn       3
% 2.85/1.01  --inst_sel_renew                        solver
% 2.85/1.01  --inst_lit_activity_flag                true
% 2.85/1.01  --inst_restr_to_given                   false
% 2.85/1.01  --inst_activity_threshold               500
% 2.85/1.01  --inst_out_proof                        true
% 2.85/1.01  
% 2.85/1.01  ------ Resolution Options
% 2.85/1.01  
% 2.85/1.01  --resolution_flag                       true
% 2.85/1.01  --res_lit_sel                           adaptive
% 2.85/1.01  --res_lit_sel_side                      none
% 2.85/1.01  --res_ordering                          kbo
% 2.85/1.01  --res_to_prop_solver                    active
% 2.85/1.01  --res_prop_simpl_new                    false
% 2.85/1.01  --res_prop_simpl_given                  true
% 2.85/1.01  --res_passive_queue_type                priority_queues
% 2.85/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/1.01  --res_passive_queues_freq               [15;5]
% 2.85/1.01  --res_forward_subs                      full
% 2.85/1.01  --res_backward_subs                     full
% 2.85/1.01  --res_forward_subs_resolution           true
% 2.85/1.01  --res_backward_subs_resolution          true
% 2.85/1.01  --res_orphan_elimination                true
% 2.85/1.01  --res_time_limit                        2.
% 2.85/1.01  --res_out_proof                         true
% 2.85/1.01  
% 2.85/1.01  ------ Superposition Options
% 2.85/1.01  
% 2.85/1.01  --superposition_flag                    true
% 2.85/1.01  --sup_passive_queue_type                priority_queues
% 2.85/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.85/1.01  --demod_completeness_check              fast
% 2.85/1.01  --demod_use_ground                      true
% 2.85/1.01  --sup_to_prop_solver                    passive
% 2.85/1.01  --sup_prop_simpl_new                    true
% 2.85/1.01  --sup_prop_simpl_given                  true
% 2.85/1.01  --sup_fun_splitting                     false
% 2.85/1.01  --sup_smt_interval                      50000
% 2.85/1.01  
% 2.85/1.01  ------ Superposition Simplification Setup
% 2.85/1.01  
% 2.85/1.01  --sup_indices_passive                   []
% 2.85/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_full_bw                           [BwDemod]
% 2.85/1.01  --sup_immed_triv                        [TrivRules]
% 2.85/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_immed_bw_main                     []
% 2.85/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.01  
% 2.85/1.01  ------ Combination Options
% 2.85/1.01  
% 2.85/1.01  --comb_res_mult                         3
% 2.85/1.01  --comb_sup_mult                         2
% 2.85/1.01  --comb_inst_mult                        10
% 2.85/1.01  
% 2.85/1.01  ------ Debug Options
% 2.85/1.01  
% 2.85/1.01  --dbg_backtrace                         false
% 2.85/1.01  --dbg_dump_prop_clauses                 false
% 2.85/1.01  --dbg_dump_prop_clauses_file            -
% 2.85/1.01  --dbg_out_stat                          false
% 2.85/1.01  ------ Parsing...
% 2.85/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.85/1.01  
% 2.85/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.85/1.01  
% 2.85/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.85/1.01  
% 2.85/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.85/1.01  ------ Proving...
% 2.85/1.01  ------ Problem Properties 
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  clauses                                 23
% 2.85/1.01  conjectures                             2
% 2.85/1.01  EPR                                     5
% 2.85/1.01  Horn                                    20
% 2.85/1.01  unary                                   7
% 2.85/1.01  binary                                  8
% 2.85/1.01  lits                                    55
% 2.85/1.01  lits eq                                 6
% 2.85/1.01  fd_pure                                 0
% 2.85/1.01  fd_pseudo                               0
% 2.85/1.01  fd_cond                                 1
% 2.85/1.01  fd_pseudo_cond                          0
% 2.85/1.01  AC symbols                              0
% 2.85/1.01  
% 2.85/1.01  ------ Schedule dynamic 5 is on 
% 2.85/1.01  
% 2.85/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  ------ 
% 2.85/1.01  Current options:
% 2.85/1.01  ------ 
% 2.85/1.01  
% 2.85/1.01  ------ Input Options
% 2.85/1.01  
% 2.85/1.01  --out_options                           all
% 2.85/1.01  --tptp_safe_out                         true
% 2.85/1.01  --problem_path                          ""
% 2.85/1.01  --include_path                          ""
% 2.85/1.01  --clausifier                            res/vclausify_rel
% 2.85/1.01  --clausifier_options                    --mode clausify
% 2.85/1.01  --stdin                                 false
% 2.85/1.01  --stats_out                             all
% 2.85/1.01  
% 2.85/1.01  ------ General Options
% 2.85/1.01  
% 2.85/1.01  --fof                                   false
% 2.85/1.01  --time_out_real                         305.
% 2.85/1.01  --time_out_virtual                      -1.
% 2.85/1.01  --symbol_type_check                     false
% 2.85/1.01  --clausify_out                          false
% 2.85/1.01  --sig_cnt_out                           false
% 2.85/1.01  --trig_cnt_out                          false
% 2.85/1.01  --trig_cnt_out_tolerance                1.
% 2.85/1.01  --trig_cnt_out_sk_spl                   false
% 2.85/1.01  --abstr_cl_out                          false
% 2.85/1.01  
% 2.85/1.01  ------ Global Options
% 2.85/1.01  
% 2.85/1.01  --schedule                              default
% 2.85/1.01  --add_important_lit                     false
% 2.85/1.01  --prop_solver_per_cl                    1000
% 2.85/1.01  --min_unsat_core                        false
% 2.85/1.01  --soft_assumptions                      false
% 2.85/1.01  --soft_lemma_size                       3
% 2.85/1.01  --prop_impl_unit_size                   0
% 2.85/1.01  --prop_impl_unit                        []
% 2.85/1.01  --share_sel_clauses                     true
% 2.85/1.01  --reset_solvers                         false
% 2.85/1.01  --bc_imp_inh                            [conj_cone]
% 2.85/1.01  --conj_cone_tolerance                   3.
% 2.85/1.01  --extra_neg_conj                        none
% 2.85/1.01  --large_theory_mode                     true
% 2.85/1.01  --prolific_symb_bound                   200
% 2.85/1.01  --lt_threshold                          2000
% 2.85/1.01  --clause_weak_htbl                      true
% 2.85/1.01  --gc_record_bc_elim                     false
% 2.85/1.01  
% 2.85/1.01  ------ Preprocessing Options
% 2.85/1.01  
% 2.85/1.01  --preprocessing_flag                    true
% 2.85/1.01  --time_out_prep_mult                    0.1
% 2.85/1.01  --splitting_mode                        input
% 2.85/1.01  --splitting_grd                         true
% 2.85/1.01  --splitting_cvd                         false
% 2.85/1.01  --splitting_cvd_svl                     false
% 2.85/1.01  --splitting_nvd                         32
% 2.85/1.01  --sub_typing                            true
% 2.85/1.01  --prep_gs_sim                           true
% 2.85/1.01  --prep_unflatten                        true
% 2.85/1.01  --prep_res_sim                          true
% 2.85/1.01  --prep_upred                            true
% 2.85/1.01  --prep_sem_filter                       exhaustive
% 2.85/1.01  --prep_sem_filter_out                   false
% 2.85/1.01  --pred_elim                             true
% 2.85/1.01  --res_sim_input                         true
% 2.85/1.01  --eq_ax_congr_red                       true
% 2.85/1.01  --pure_diseq_elim                       true
% 2.85/1.01  --brand_transform                       false
% 2.85/1.01  --non_eq_to_eq                          false
% 2.85/1.01  --prep_def_merge                        true
% 2.85/1.01  --prep_def_merge_prop_impl              false
% 2.85/1.01  --prep_def_merge_mbd                    true
% 2.85/1.01  --prep_def_merge_tr_red                 false
% 2.85/1.01  --prep_def_merge_tr_cl                  false
% 2.85/1.01  --smt_preprocessing                     true
% 2.85/1.01  --smt_ac_axioms                         fast
% 2.85/1.01  --preprocessed_out                      false
% 2.85/1.01  --preprocessed_stats                    false
% 2.85/1.01  
% 2.85/1.01  ------ Abstraction refinement Options
% 2.85/1.01  
% 2.85/1.01  --abstr_ref                             []
% 2.85/1.01  --abstr_ref_prep                        false
% 2.85/1.01  --abstr_ref_until_sat                   false
% 2.85/1.01  --abstr_ref_sig_restrict                funpre
% 2.85/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.85/1.01  --abstr_ref_under                       []
% 2.85/1.01  
% 2.85/1.01  ------ SAT Options
% 2.85/1.01  
% 2.85/1.01  --sat_mode                              false
% 2.85/1.01  --sat_fm_restart_options                ""
% 2.85/1.01  --sat_gr_def                            false
% 2.85/1.01  --sat_epr_types                         true
% 2.85/1.01  --sat_non_cyclic_types                  false
% 2.85/1.01  --sat_finite_models                     false
% 2.85/1.01  --sat_fm_lemmas                         false
% 2.85/1.01  --sat_fm_prep                           false
% 2.85/1.01  --sat_fm_uc_incr                        true
% 2.85/1.01  --sat_out_model                         small
% 2.85/1.01  --sat_out_clauses                       false
% 2.85/1.01  
% 2.85/1.01  ------ QBF Options
% 2.85/1.01  
% 2.85/1.01  --qbf_mode                              false
% 2.85/1.01  --qbf_elim_univ                         false
% 2.85/1.01  --qbf_dom_inst                          none
% 2.85/1.01  --qbf_dom_pre_inst                      false
% 2.85/1.01  --qbf_sk_in                             false
% 2.85/1.01  --qbf_pred_elim                         true
% 2.85/1.01  --qbf_split                             512
% 2.85/1.01  
% 2.85/1.01  ------ BMC1 Options
% 2.85/1.01  
% 2.85/1.01  --bmc1_incremental                      false
% 2.85/1.01  --bmc1_axioms                           reachable_all
% 2.85/1.01  --bmc1_min_bound                        0
% 2.85/1.01  --bmc1_max_bound                        -1
% 2.85/1.01  --bmc1_max_bound_default                -1
% 2.85/1.01  --bmc1_symbol_reachability              true
% 2.85/1.01  --bmc1_property_lemmas                  false
% 2.85/1.01  --bmc1_k_induction                      false
% 2.85/1.01  --bmc1_non_equiv_states                 false
% 2.85/1.01  --bmc1_deadlock                         false
% 2.85/1.01  --bmc1_ucm                              false
% 2.85/1.01  --bmc1_add_unsat_core                   none
% 2.85/1.01  --bmc1_unsat_core_children              false
% 2.85/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.85/1.01  --bmc1_out_stat                         full
% 2.85/1.01  --bmc1_ground_init                      false
% 2.85/1.01  --bmc1_pre_inst_next_state              false
% 2.85/1.01  --bmc1_pre_inst_state                   false
% 2.85/1.01  --bmc1_pre_inst_reach_state             false
% 2.85/1.01  --bmc1_out_unsat_core                   false
% 2.85/1.01  --bmc1_aig_witness_out                  false
% 2.85/1.01  --bmc1_verbose                          false
% 2.85/1.01  --bmc1_dump_clauses_tptp                false
% 2.85/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.85/1.01  --bmc1_dump_file                        -
% 2.85/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.85/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.85/1.01  --bmc1_ucm_extend_mode                  1
% 2.85/1.01  --bmc1_ucm_init_mode                    2
% 2.85/1.01  --bmc1_ucm_cone_mode                    none
% 2.85/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.85/1.01  --bmc1_ucm_relax_model                  4
% 2.85/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.85/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.85/1.01  --bmc1_ucm_layered_model                none
% 2.85/1.01  --bmc1_ucm_max_lemma_size               10
% 2.85/1.01  
% 2.85/1.01  ------ AIG Options
% 2.85/1.01  
% 2.85/1.01  --aig_mode                              false
% 2.85/1.01  
% 2.85/1.01  ------ Instantiation Options
% 2.85/1.01  
% 2.85/1.01  --instantiation_flag                    true
% 2.85/1.01  --inst_sos_flag                         false
% 2.85/1.01  --inst_sos_phase                        true
% 2.85/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.85/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.85/1.01  --inst_lit_sel_side                     none
% 2.85/1.01  --inst_solver_per_active                1400
% 2.85/1.01  --inst_solver_calls_frac                1.
% 2.85/1.01  --inst_passive_queue_type               priority_queues
% 2.85/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.85/1.01  --inst_passive_queues_freq              [25;2]
% 2.85/1.01  --inst_dismatching                      true
% 2.85/1.01  --inst_eager_unprocessed_to_passive     true
% 2.85/1.01  --inst_prop_sim_given                   true
% 2.85/1.01  --inst_prop_sim_new                     false
% 2.85/1.01  --inst_subs_new                         false
% 2.85/1.01  --inst_eq_res_simp                      false
% 2.85/1.01  --inst_subs_given                       false
% 2.85/1.01  --inst_orphan_elimination               true
% 2.85/1.01  --inst_learning_loop_flag               true
% 2.85/1.01  --inst_learning_start                   3000
% 2.85/1.01  --inst_learning_factor                  2
% 2.85/1.01  --inst_start_prop_sim_after_learn       3
% 2.85/1.01  --inst_sel_renew                        solver
% 2.85/1.01  --inst_lit_activity_flag                true
% 2.85/1.01  --inst_restr_to_given                   false
% 2.85/1.01  --inst_activity_threshold               500
% 2.85/1.01  --inst_out_proof                        true
% 2.85/1.01  
% 2.85/1.01  ------ Resolution Options
% 2.85/1.01  
% 2.85/1.01  --resolution_flag                       false
% 2.85/1.01  --res_lit_sel                           adaptive
% 2.85/1.01  --res_lit_sel_side                      none
% 2.85/1.01  --res_ordering                          kbo
% 2.85/1.01  --res_to_prop_solver                    active
% 2.85/1.01  --res_prop_simpl_new                    false
% 2.85/1.01  --res_prop_simpl_given                  true
% 2.85/1.01  --res_passive_queue_type                priority_queues
% 2.85/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.85/1.01  --res_passive_queues_freq               [15;5]
% 2.85/1.01  --res_forward_subs                      full
% 2.85/1.01  --res_backward_subs                     full
% 2.85/1.01  --res_forward_subs_resolution           true
% 2.85/1.01  --res_backward_subs_resolution          true
% 2.85/1.01  --res_orphan_elimination                true
% 2.85/1.01  --res_time_limit                        2.
% 2.85/1.01  --res_out_proof                         true
% 2.85/1.01  
% 2.85/1.01  ------ Superposition Options
% 2.85/1.01  
% 2.85/1.01  --superposition_flag                    true
% 2.85/1.01  --sup_passive_queue_type                priority_queues
% 2.85/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.85/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.85/1.01  --demod_completeness_check              fast
% 2.85/1.01  --demod_use_ground                      true
% 2.85/1.01  --sup_to_prop_solver                    passive
% 2.85/1.01  --sup_prop_simpl_new                    true
% 2.85/1.01  --sup_prop_simpl_given                  true
% 2.85/1.01  --sup_fun_splitting                     false
% 2.85/1.01  --sup_smt_interval                      50000
% 2.85/1.01  
% 2.85/1.01  ------ Superposition Simplification Setup
% 2.85/1.01  
% 2.85/1.01  --sup_indices_passive                   []
% 2.85/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.85/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.85/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_full_bw                           [BwDemod]
% 2.85/1.01  --sup_immed_triv                        [TrivRules]
% 2.85/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.85/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_immed_bw_main                     []
% 2.85/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.85/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.85/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.85/1.01  
% 2.85/1.01  ------ Combination Options
% 2.85/1.01  
% 2.85/1.01  --comb_res_mult                         3
% 2.85/1.01  --comb_sup_mult                         2
% 2.85/1.01  --comb_inst_mult                        10
% 2.85/1.01  
% 2.85/1.01  ------ Debug Options
% 2.85/1.01  
% 2.85/1.01  --dbg_backtrace                         false
% 2.85/1.01  --dbg_dump_prop_clauses                 false
% 2.85/1.01  --dbg_dump_prop_clauses_file            -
% 2.85/1.01  --dbg_out_stat                          false
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  ------ Proving...
% 2.85/1.01  
% 2.85/1.01  
% 2.85/1.01  % SZS status Theorem for theBenchmark.p
% 2.85/1.01  
% 2.85/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.85/1.01  
% 2.85/1.01  fof(f9,axiom,(
% 2.85/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f53,plain,(
% 2.85/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.85/1.01    inference(cnf_transformation,[],[f9])).
% 2.85/1.01  
% 2.85/1.01  fof(f1,axiom,(
% 2.85/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f17,plain,(
% 2.85/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f1])).
% 2.85/1.01  
% 2.85/1.01  fof(f31,plain,(
% 2.85/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/1.01    inference(nnf_transformation,[],[f17])).
% 2.85/1.01  
% 2.85/1.01  fof(f32,plain,(
% 2.85/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/1.01    inference(rectify,[],[f31])).
% 2.85/1.01  
% 2.85/1.01  fof(f33,plain,(
% 2.85/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.85/1.01    introduced(choice_axiom,[])).
% 2.85/1.01  
% 2.85/1.01  fof(f34,plain,(
% 2.85/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 2.85/1.01  
% 2.85/1.01  fof(f44,plain,(
% 2.85/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f34])).
% 2.85/1.01  
% 2.85/1.01  fof(f7,axiom,(
% 2.85/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f20,plain,(
% 2.85/1.01    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f7])).
% 2.85/1.01  
% 2.85/1.01  fof(f51,plain,(
% 2.85/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.85/1.01    inference(cnf_transformation,[],[f20])).
% 2.85/1.01  
% 2.85/1.01  fof(f11,axiom,(
% 2.85/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f24,plain,(
% 2.85/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.85/1.01    inference(ennf_transformation,[],[f11])).
% 2.85/1.01  
% 2.85/1.01  fof(f55,plain,(
% 2.85/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f24])).
% 2.85/1.01  
% 2.85/1.01  fof(f14,conjecture,(
% 2.85/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f15,negated_conjecture,(
% 2.85/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.85/1.01    inference(negated_conjecture,[],[f14])).
% 2.85/1.01  
% 2.85/1.01  fof(f16,plain,(
% 2.85/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.85/1.01    inference(pure_predicate_removal,[],[f15])).
% 2.85/1.01  
% 2.85/1.01  fof(f29,plain,(
% 2.85/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f16])).
% 2.85/1.01  
% 2.85/1.01  fof(f30,plain,(
% 2.85/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.85/1.01    inference(flattening,[],[f29])).
% 2.85/1.01  
% 2.85/1.01  fof(f41,plain,(
% 2.85/1.01    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.85/1.01    introduced(choice_axiom,[])).
% 2.85/1.01  
% 2.85/1.01  fof(f40,plain,(
% 2.85/1.01    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3))),
% 2.85/1.01    introduced(choice_axiom,[])).
% 2.85/1.01  
% 2.85/1.01  fof(f42,plain,(
% 2.85/1.01    (~v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3)),
% 2.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f30,f41,f40])).
% 2.85/1.01  
% 2.85/1.01  fof(f65,plain,(
% 2.85/1.01    v1_xboole_0(sK4)),
% 2.85/1.01    inference(cnf_transformation,[],[f42])).
% 2.85/1.01  
% 2.85/1.01  fof(f6,axiom,(
% 2.85/1.01    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f50,plain,(
% 2.85/1.01    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.85/1.01    inference(cnf_transformation,[],[f6])).
% 2.85/1.01  
% 2.85/1.01  fof(f5,axiom,(
% 2.85/1.01    ! [X0] : k2_subset_1(X0) = X0),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f49,plain,(
% 2.85/1.01    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.85/1.01    inference(cnf_transformation,[],[f5])).
% 2.85/1.01  
% 2.85/1.01  fof(f3,axiom,(
% 2.85/1.01    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f18,plain,(
% 2.85/1.01    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.85/1.01    inference(ennf_transformation,[],[f3])).
% 2.85/1.01  
% 2.85/1.01  fof(f47,plain,(
% 2.85/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f18])).
% 2.85/1.01  
% 2.85/1.01  fof(f8,axiom,(
% 2.85/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f21,plain,(
% 2.85/1.01    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f8])).
% 2.85/1.01  
% 2.85/1.01  fof(f52,plain,(
% 2.85/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.85/1.01    inference(cnf_transformation,[],[f21])).
% 2.85/1.01  
% 2.85/1.01  fof(f4,axiom,(
% 2.85/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f19,plain,(
% 2.85/1.01    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f4])).
% 2.85/1.01  
% 2.85/1.01  fof(f48,plain,(
% 2.85/1.01    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.85/1.01    inference(cnf_transformation,[],[f19])).
% 2.85/1.01  
% 2.85/1.01  fof(f13,axiom,(
% 2.85/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f27,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/1.01    inference(ennf_transformation,[],[f13])).
% 2.85/1.01  
% 2.85/1.01  fof(f28,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/1.01    inference(flattening,[],[f27])).
% 2.85/1.01  
% 2.85/1.01  fof(f35,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/1.01    inference(nnf_transformation,[],[f28])).
% 2.85/1.01  
% 2.85/1.01  fof(f36,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/1.01    inference(rectify,[],[f35])).
% 2.85/1.01  
% 2.85/1.01  fof(f38,plain,(
% 2.85/1.01    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.85/1.01    introduced(choice_axiom,[])).
% 2.85/1.01  
% 2.85/1.01  fof(f37,plain,(
% 2.85/1.01    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.85/1.01    introduced(choice_axiom,[])).
% 2.85/1.01  
% 2.85/1.01  fof(f39,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK2(X0,X1,X4)) = X4 & v4_pre_topc(sK2(X0,X1,X4),X0) & m1_subset_1(sK2(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.85/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f36,f38,f37])).
% 2.85/1.01  
% 2.85/1.01  fof(f62,plain,(
% 2.85/1.01    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK1(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f39])).
% 2.85/1.01  
% 2.85/1.01  fof(f64,plain,(
% 2.85/1.01    l1_pre_topc(sK3)),
% 2.85/1.01    inference(cnf_transformation,[],[f42])).
% 2.85/1.01  
% 2.85/1.01  fof(f66,plain,(
% 2.85/1.01    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.85/1.01    inference(cnf_transformation,[],[f42])).
% 2.85/1.01  
% 2.85/1.01  fof(f61,plain,(
% 2.85/1.01    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f39])).
% 2.85/1.01  
% 2.85/1.01  fof(f67,plain,(
% 2.85/1.01    ~v2_tex_2(sK4,sK3)),
% 2.85/1.01    inference(cnf_transformation,[],[f42])).
% 2.85/1.01  
% 2.85/1.01  fof(f2,axiom,(
% 2.85/1.01    v1_xboole_0(k1_xboole_0)),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f46,plain,(
% 2.85/1.01    v1_xboole_0(k1_xboole_0)),
% 2.85/1.01    inference(cnf_transformation,[],[f2])).
% 2.85/1.01  
% 2.85/1.01  fof(f12,axiom,(
% 2.85/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 2.85/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.85/1.01  
% 2.85/1.01  fof(f25,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.85/1.01    inference(ennf_transformation,[],[f12])).
% 2.85/1.01  
% 2.85/1.01  fof(f26,plain,(
% 2.85/1.01    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.85/1.01    inference(flattening,[],[f25])).
% 2.85/1.01  
% 2.85/1.01  fof(f56,plain,(
% 2.85/1.01    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.85/1.01    inference(cnf_transformation,[],[f26])).
% 2.85/1.01  
% 2.85/1.01  fof(f63,plain,(
% 2.85/1.01    v2_pre_topc(sK3)),
% 2.85/1.01    inference(cnf_transformation,[],[f42])).
% 2.85/1.01  
% 2.85/1.01  cnf(c_10,plain,
% 2.85/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.85/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2390,plain,
% 2.85/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_1,plain,
% 2.85/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.85/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2397,plain,
% 2.85/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.85/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_8,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.85/1.01      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 2.85/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2392,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.85/1.01      | m1_subset_1(k9_subset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_12,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.85/1.01      | ~ r2_hidden(X2,X0)
% 2.85/1.01      | ~ v1_xboole_0(X1) ),
% 2.85/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_22,negated_conjecture,
% 2.85/1.01      ( v1_xboole_0(sK4) ),
% 2.85/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_319,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.85/1.01      | ~ r2_hidden(X2,X0)
% 2.85/1.01      | sK4 != X1 ),
% 2.85/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_22]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_320,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4)) | ~ r2_hidden(X1,X0) ),
% 2.85/1.01      inference(unflattening,[status(thm)],[c_319]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2384,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.85/1.01      | r2_hidden(X1,X0) != iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_320]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_3867,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.85/1.01      | r2_hidden(X1,k9_subset_1(sK4,X2,X0)) != iProver_top ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2392,c_2384]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_4067,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(sK4)) != iProver_top
% 2.85/1.01      | r1_tarski(k9_subset_1(sK4,X1,X0),X2) = iProver_top ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2397,c_3867]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_7,plain,
% 2.85/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.85/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2393,plain,
% 2.85/1.01      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_6,plain,
% 2.85/1.01      ( k2_subset_1(X0) = X0 ),
% 2.85/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2411,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.85/1.01      inference(light_normalisation,[status(thm)],[c_2393,c_6]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2964,plain,
% 2.85/1.01      ( r2_hidden(X0,sK4) != iProver_top ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2411,c_2384]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_3723,plain,
% 2.85/1.01      ( r1_tarski(sK4,X0) = iProver_top ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2397,c_2964]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_4,plain,
% 2.85/1.01      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.85/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2395,plain,
% 2.85/1.01      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_5449,plain,
% 2.85/1.01      ( sK4 = k1_xboole_0 ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_3723,c_2395]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_7891,plain,
% 2.85/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.85/1.01      | r1_tarski(k9_subset_1(k1_xboole_0,X1,X0),X2) = iProver_top ),
% 2.85/1.01      inference(light_normalisation,[status(thm)],[c_4067,c_5449]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_7901,plain,
% 2.85/1.01      ( k9_subset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 2.85/1.01      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_7891,c_2395]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_7925,plain,
% 2.85/1.01      ( k9_subset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2390,c_7901]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_9,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.85/1.01      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 2.85/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2391,plain,
% 2.85/1.01      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 2.85/1.01      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_3824,plain,
% 2.85/1.01      ( k9_subset_1(X0,X1,k1_xboole_0) = k3_xboole_0(X1,k1_xboole_0) ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2390,c_2391]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_8717,plain,
% 2.85/1.01      ( k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_7925,c_3824]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_8726,plain,
% 2.85/1.01      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.85/1.01      inference(instantiation,[status(thm)],[c_8717]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_5,plain,
% 2.85/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.85/1.01      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 2.85/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2394,plain,
% 2.85/1.01      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 2.85/1.01      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 2.85/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_4668,plain,
% 2.85/1.01      ( k9_subset_1(X0,k1_xboole_0,X1) = k9_subset_1(X0,X1,k1_xboole_0) ),
% 2.85/1.01      inference(superposition,[status(thm)],[c_2390,c_2394]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_6175,plain,
% 2.85/1.01      ( k9_subset_1(X0,k1_xboole_0,X1) = k3_xboole_0(X1,k1_xboole_0) ),
% 2.85/1.01      inference(light_normalisation,[status(thm)],[c_4668,c_3824]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_14,plain,
% 2.85/1.01      ( v2_tex_2(X0,X1)
% 2.85/1.01      | ~ v4_pre_topc(X2,X1)
% 2.85/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.01      | ~ l1_pre_topc(X1)
% 2.85/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0) ),
% 2.85/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_23,negated_conjecture,
% 2.85/1.01      ( l1_pre_topc(sK3) ),
% 2.85/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_535,plain,
% 2.85/1.01      ( v2_tex_2(X0,X1)
% 2.85/1.01      | ~ v4_pre_topc(X2,X1)
% 2.85/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.01      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK1(X1,X0)
% 2.85/1.01      | sK3 != X1 ),
% 2.85/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_23]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_536,plain,
% 2.85/1.01      ( v2_tex_2(X0,sK3)
% 2.85/1.01      | ~ v4_pre_topc(X1,sK3)
% 2.85/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.01      | k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0) ),
% 2.85/1.01      inference(unflattening,[status(thm)],[c_535]) ).
% 2.85/1.01  
% 2.85/1.01  cnf(c_2377,plain,
% 2.85/1.01      ( k9_subset_1(u1_struct_0(sK3),X0,X1) != sK1(sK3,X0)
% 2.85/1.01      | v2_tex_2(X0,sK3) = iProver_top
% 2.85/1.01      | v4_pre_topc(X1,sK3) != iProver_top
% 2.85/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.85/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_536]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_6182,plain,
% 2.85/1.02      ( k3_xboole_0(X0,k1_xboole_0) != sK1(sK3,k1_xboole_0)
% 2.85/1.02      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.85/1.02      | v4_pre_topc(X0,sK3) != iProver_top
% 2.85/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.85/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.85/1.02      inference(superposition,[status(thm)],[c_6175,c_2377]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_21,negated_conjecture,
% 2.85/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.85/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2387,plain,
% 2.85/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_15,plain,
% 2.85/1.02      ( v2_tex_2(X0,X1)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.02      | r1_tarski(sK1(X1,X0),X0)
% 2.85/1.02      | ~ l1_pre_topc(X1) ),
% 2.85/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_520,plain,
% 2.85/1.02      ( v2_tex_2(X0,X1)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.02      | r1_tarski(sK1(X1,X0),X0)
% 2.85/1.02      | sK3 != X1 ),
% 2.85/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_521,plain,
% 2.85/1.02      ( v2_tex_2(X0,sK3)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | r1_tarski(sK1(sK3,X0),X0) ),
% 2.85/1.02      inference(unflattening,[status(thm)],[c_520]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2378,plain,
% 2.85/1.02      ( v2_tex_2(X0,sK3) = iProver_top
% 2.85/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.85/1.02      | r1_tarski(sK1(sK3,X0),X0) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2813,plain,
% 2.85/1.02      ( v2_tex_2(sK4,sK3) = iProver_top
% 2.85/1.02      | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 2.85/1.02      inference(superposition,[status(thm)],[c_2387,c_2378]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_28,plain,
% 2.85/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_20,negated_conjecture,
% 2.85/1.02      ( ~ v2_tex_2(sK4,sK3) ),
% 2.85/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_1139,plain,
% 2.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | r1_tarski(sK1(sK3,X0),X0)
% 2.85/1.02      | sK3 != sK3
% 2.85/1.02      | sK4 != X0 ),
% 2.85/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_521]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_1140,plain,
% 2.85/1.02      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | r1_tarski(sK1(sK3,sK4),sK4) ),
% 2.85/1.02      inference(unflattening,[status(thm)],[c_1139]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_1141,plain,
% 2.85/1.02      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.85/1.02      | r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_1140]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_3047,plain,
% 2.85/1.02      ( r1_tarski(sK1(sK3,sK4),sK4) = iProver_top ),
% 2.85/1.02      inference(global_propositional_subsumption,
% 2.85/1.02                [status(thm)],
% 2.85/1.02                [c_2813,c_28,c_1141]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_5464,plain,
% 2.85/1.02      ( r1_tarski(sK1(sK3,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.85/1.02      inference(demodulation,[status(thm)],[c_5449,c_3047]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_5647,plain,
% 2.85/1.02      ( sK1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.85/1.02      inference(superposition,[status(thm)],[c_5464,c_2395]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_6191,plain,
% 2.85/1.02      ( k3_xboole_0(X0,k1_xboole_0) != k1_xboole_0
% 2.85/1.02      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.85/1.02      | v4_pre_topc(X0,sK3) != iProver_top
% 2.85/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.85/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.85/1.02      inference(light_normalisation,[status(thm)],[c_6182,c_5647]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_6215,plain,
% 2.85/1.02      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.85/1.02      | v2_tex_2(k1_xboole_0,sK3) = iProver_top
% 2.85/1.02      | v4_pre_topc(k1_xboole_0,sK3) != iProver_top
% 2.85/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.85/1.02      inference(instantiation,[status(thm)],[c_6191]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2388,plain,
% 2.85/1.02      ( v2_tex_2(sK4,sK3) != iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_5468,plain,
% 2.85/1.02      ( v2_tex_2(k1_xboole_0,sK3) != iProver_top ),
% 2.85/1.02      inference(demodulation,[status(thm)],[c_5449,c_2388]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2575,plain,
% 2.85/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.85/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_2579,plain,
% 2.85/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_2575]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_3,plain,
% 2.85/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.85/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_13,plain,
% 2.85/1.02      ( v4_pre_topc(X0,X1)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.02      | ~ v2_pre_topc(X1)
% 2.85/1.02      | ~ l1_pre_topc(X1)
% 2.85/1.02      | ~ v1_xboole_0(X0) ),
% 2.85/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_24,negated_conjecture,
% 2.85/1.02      ( v2_pre_topc(sK3) ),
% 2.85/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_272,plain,
% 2.85/1.02      ( v4_pre_topc(X0,X1)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.85/1.02      | ~ l1_pre_topc(X1)
% 2.85/1.02      | ~ v1_xboole_0(X0)
% 2.85/1.02      | sK3 != X1 ),
% 2.85/1.02      inference(resolution_lifted,[status(thm)],[c_13,c_24]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_273,plain,
% 2.85/1.02      ( v4_pre_topc(X0,sK3)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | ~ l1_pre_topc(sK3)
% 2.85/1.02      | ~ v1_xboole_0(X0) ),
% 2.85/1.02      inference(unflattening,[status(thm)],[c_272]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_277,plain,
% 2.85/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | v4_pre_topc(X0,sK3)
% 2.85/1.02      | ~ v1_xboole_0(X0) ),
% 2.85/1.02      inference(global_propositional_subsumption,
% 2.85/1.02                [status(thm)],
% 2.85/1.02                [c_273,c_23]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_278,plain,
% 2.85/1.02      ( v4_pre_topc(X0,sK3)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | ~ v1_xboole_0(X0) ),
% 2.85/1.02      inference(renaming,[status(thm)],[c_277]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_309,plain,
% 2.85/1.02      ( v4_pre_topc(X0,sK3)
% 2.85/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.85/1.02      | k1_xboole_0 != X0 ),
% 2.85/1.02      inference(resolution_lifted,[status(thm)],[c_3,c_278]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_310,plain,
% 2.85/1.02      ( v4_pre_topc(k1_xboole_0,sK3)
% 2.85/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.85/1.02      inference(unflattening,[status(thm)],[c_309]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_316,plain,
% 2.85/1.02      ( v4_pre_topc(k1_xboole_0,sK3) ),
% 2.85/1.02      inference(forward_subsumption_resolution,
% 2.85/1.02                [status(thm)],
% 2.85/1.02                [c_310,c_10]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(c_318,plain,
% 2.85/1.02      ( v4_pre_topc(k1_xboole_0,sK3) = iProver_top ),
% 2.85/1.02      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 2.85/1.02  
% 2.85/1.02  cnf(contradiction,plain,
% 2.85/1.02      ( $false ),
% 2.85/1.02      inference(minisat,[status(thm)],[c_8726,c_6215,c_5468,c_2579,c_318]) ).
% 2.85/1.02  
% 2.85/1.02  
% 2.85/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.85/1.02  
% 2.85/1.02  ------                               Statistics
% 2.85/1.02  
% 2.85/1.02  ------ General
% 2.85/1.02  
% 2.85/1.02  abstr_ref_over_cycles:                  0
% 2.85/1.02  abstr_ref_under_cycles:                 0
% 2.85/1.02  gc_basic_clause_elim:                   0
% 2.85/1.02  forced_gc_time:                         0
% 2.85/1.02  parsing_time:                           0.01
% 2.85/1.02  unif_index_cands_time:                  0.
% 2.85/1.02  unif_index_add_time:                    0.
% 2.85/1.02  orderings_time:                         0.
% 2.85/1.02  out_proof_time:                         0.008
% 2.85/1.02  total_time:                             0.257
% 2.85/1.02  num_of_symbols:                         50
% 2.85/1.02  num_of_terms:                           6477
% 2.85/1.02  
% 2.85/1.02  ------ Preprocessing
% 2.85/1.02  
% 2.85/1.02  num_of_splits:                          0
% 2.85/1.02  num_of_split_atoms:                     0
% 2.85/1.02  num_of_reused_defs:                     0
% 2.85/1.02  num_eq_ax_congr_red:                    33
% 2.85/1.02  num_of_sem_filtered_clauses:            1
% 2.85/1.02  num_of_subtypes:                        0
% 2.85/1.02  monotx_restored_types:                  0
% 2.85/1.02  sat_num_of_epr_types:                   0
% 2.85/1.02  sat_num_of_non_cyclic_types:            0
% 2.85/1.02  sat_guarded_non_collapsed_types:        0
% 2.85/1.02  num_pure_diseq_elim:                    0
% 2.85/1.02  simp_replaced_by:                       0
% 2.85/1.02  res_preprocessed:                       119
% 2.85/1.02  prep_upred:                             0
% 2.85/1.02  prep_unflattend:                        89
% 2.85/1.02  smt_new_axioms:                         0
% 2.85/1.02  pred_elim_cands:                        5
% 2.85/1.02  pred_elim:                              3
% 2.85/1.02  pred_elim_cl:                           2
% 2.85/1.02  pred_elim_cycles:                       10
% 2.85/1.02  merged_defs:                            0
% 2.85/1.02  merged_defs_ncl:                        0
% 2.85/1.02  bin_hyper_res:                          0
% 2.85/1.02  prep_cycles:                            4
% 2.85/1.02  pred_elim_time:                         0.031
% 2.85/1.02  splitting_time:                         0.
% 2.85/1.02  sem_filter_time:                        0.
% 2.85/1.02  monotx_time:                            0.001
% 2.85/1.02  subtype_inf_time:                       0.
% 2.85/1.02  
% 2.85/1.02  ------ Problem properties
% 2.85/1.02  
% 2.85/1.02  clauses:                                23
% 2.85/1.02  conjectures:                            2
% 2.85/1.02  epr:                                    5
% 2.85/1.02  horn:                                   20
% 2.85/1.02  ground:                                 4
% 2.85/1.02  unary:                                  7
% 2.85/1.02  binary:                                 8
% 2.85/1.02  lits:                                   55
% 2.85/1.02  lits_eq:                                6
% 2.85/1.02  fd_pure:                                0
% 2.85/1.02  fd_pseudo:                              0
% 2.85/1.02  fd_cond:                                1
% 2.85/1.02  fd_pseudo_cond:                         0
% 2.85/1.02  ac_symbols:                             0
% 2.85/1.02  
% 2.85/1.02  ------ Propositional Solver
% 2.85/1.02  
% 2.85/1.02  prop_solver_calls:                      30
% 2.85/1.02  prop_fast_solver_calls:                 1317
% 2.85/1.02  smt_solver_calls:                       0
% 2.85/1.02  smt_fast_solver_calls:                  0
% 2.85/1.02  prop_num_of_clauses:                    2628
% 2.85/1.02  prop_preprocess_simplified:             6521
% 2.85/1.02  prop_fo_subsumed:                       34
% 2.85/1.02  prop_solver_time:                       0.
% 2.85/1.02  smt_solver_time:                        0.
% 2.85/1.02  smt_fast_solver_time:                   0.
% 2.85/1.02  prop_fast_solver_time:                  0.
% 2.85/1.02  prop_unsat_core_time:                   0.
% 2.85/1.02  
% 2.85/1.02  ------ QBF
% 2.85/1.02  
% 2.85/1.02  qbf_q_res:                              0
% 2.85/1.02  qbf_num_tautologies:                    0
% 2.85/1.02  qbf_prep_cycles:                        0
% 2.85/1.02  
% 2.85/1.02  ------ BMC1
% 2.85/1.02  
% 2.85/1.02  bmc1_current_bound:                     -1
% 2.85/1.02  bmc1_last_solved_bound:                 -1
% 2.85/1.02  bmc1_unsat_core_size:                   -1
% 2.85/1.02  bmc1_unsat_core_parents_size:           -1
% 2.85/1.02  bmc1_merge_next_fun:                    0
% 2.85/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.85/1.02  
% 2.85/1.02  ------ Instantiation
% 2.85/1.02  
% 2.85/1.02  inst_num_of_clauses:                    686
% 2.85/1.02  inst_num_in_passive:                    256
% 2.85/1.02  inst_num_in_active:                     380
% 2.85/1.02  inst_num_in_unprocessed:                51
% 2.85/1.02  inst_num_of_loops:                      480
% 2.85/1.02  inst_num_of_learning_restarts:          0
% 2.85/1.02  inst_num_moves_active_passive:          96
% 2.85/1.02  inst_lit_activity:                      0
% 2.85/1.02  inst_lit_activity_moves:                0
% 2.85/1.02  inst_num_tautologies:                   0
% 2.85/1.02  inst_num_prop_implied:                  0
% 2.85/1.02  inst_num_existing_simplified:           0
% 2.85/1.02  inst_num_eq_res_simplified:             0
% 2.85/1.02  inst_num_child_elim:                    0
% 2.85/1.02  inst_num_of_dismatching_blockings:      267
% 2.85/1.02  inst_num_of_non_proper_insts:           597
% 2.85/1.02  inst_num_of_duplicates:                 0
% 2.85/1.02  inst_inst_num_from_inst_to_res:         0
% 2.85/1.02  inst_dismatching_checking_time:         0.
% 2.85/1.02  
% 2.85/1.02  ------ Resolution
% 2.85/1.02  
% 2.85/1.02  res_num_of_clauses:                     0
% 2.85/1.02  res_num_in_passive:                     0
% 2.85/1.02  res_num_in_active:                      0
% 2.85/1.02  res_num_of_loops:                       123
% 2.85/1.02  res_forward_subset_subsumed:            26
% 2.85/1.02  res_backward_subset_subsumed:           2
% 2.85/1.02  res_forward_subsumed:                   0
% 2.85/1.02  res_backward_subsumed:                  0
% 2.85/1.02  res_forward_subsumption_resolution:     5
% 2.85/1.02  res_backward_subsumption_resolution:    0
% 2.85/1.02  res_clause_to_clause_subsumption:       1246
% 2.85/1.02  res_orphan_elimination:                 0
% 2.85/1.02  res_tautology_del:                      42
% 2.85/1.02  res_num_eq_res_simplified:              0
% 2.85/1.02  res_num_sel_changes:                    0
% 2.85/1.02  res_moves_from_active_to_pass:          0
% 2.85/1.02  
% 2.85/1.02  ------ Superposition
% 2.85/1.02  
% 2.85/1.02  sup_time_total:                         0.
% 2.85/1.02  sup_time_generating:                    0.
% 2.85/1.02  sup_time_sim_full:                      0.
% 2.85/1.02  sup_time_sim_immed:                     0.
% 2.85/1.02  
% 2.85/1.02  sup_num_of_clauses:                     178
% 2.85/1.02  sup_num_in_active:                      70
% 2.85/1.02  sup_num_in_passive:                     108
% 2.85/1.02  sup_num_of_loops:                       94
% 2.85/1.02  sup_fw_superposition:                   140
% 2.85/1.02  sup_bw_superposition:                   94
% 2.85/1.02  sup_immediate_simplified:               39
% 2.85/1.02  sup_given_eliminated:                   0
% 2.85/1.02  comparisons_done:                       0
% 2.85/1.02  comparisons_avoided:                    0
% 2.85/1.02  
% 2.85/1.02  ------ Simplifications
% 2.85/1.02  
% 2.85/1.02  
% 2.85/1.02  sim_fw_subset_subsumed:                 10
% 2.85/1.02  sim_bw_subset_subsumed:                 0
% 2.85/1.02  sim_fw_subsumed:                        11
% 2.85/1.02  sim_bw_subsumed:                        1
% 2.85/1.02  sim_fw_subsumption_res:                 3
% 2.85/1.02  sim_bw_subsumption_res:                 0
% 2.85/1.02  sim_tautology_del:                      3
% 2.85/1.02  sim_eq_tautology_del:                   7
% 2.85/1.02  sim_eq_res_simp:                        0
% 2.85/1.02  sim_fw_demodulated:                     10
% 2.85/1.02  sim_bw_demodulated:                     25
% 2.85/1.02  sim_light_normalised:                   30
% 2.85/1.02  sim_joinable_taut:                      0
% 2.85/1.02  sim_joinable_simp:                      0
% 2.85/1.02  sim_ac_normalised:                      0
% 2.85/1.02  sim_smt_subsumption:                    0
% 2.85/1.02  
%------------------------------------------------------------------------------
