%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:20 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 224 expanded)
%              Number of clauses        :   71 (  82 expanded)
%              Number of leaves         :   22 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  339 ( 794 expanded)
%              Number of equality atoms :  131 ( 164 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

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

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ~ v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39,f38])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f50,f46])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f41,f46,f46])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f22])).

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

fof(f29,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v4_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v4_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_7,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_617,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_638,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_617,c_6])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_604,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_618,plain,
    ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2019,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
    inference(superposition,[status(thm)],[c_604,c_618])).

cnf(c_21,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_603,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_621,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1280,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_603,c_621])).

cnf(c_6869,plain,
    ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) = k9_subset_1(u1_struct_0(sK2),X0,k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_2019,c_1280])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_615,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_616,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2320,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_615,c_616])).

cnf(c_3,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_620,plain,
    ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1222,plain,
    ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_0,c_620])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_619,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1716,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1222,c_619])).

cnf(c_1719,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1716,c_3])).

cnf(c_2350,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2320,c_3,c_1719])).

cnf(c_6870,plain,
    ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6869,c_2350])).

cnf(c_13,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_611,plain,
    ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK0(X0,X1)
    | v2_tex_2(X1,X0) = iProver_top
    | v4_pre_topc(X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6873,plain,
    ( sK0(sK2,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6870,c_611])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_14,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_836,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0),X0)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_837,plain,
    ( v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),X0) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_836])).

cnf(c_839,plain,
    ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_837])).

cnf(c_1000,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1003,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1000])).

cnf(c_3223,plain,
    ( ~ r1_tarski(sK0(sK2,X0),k1_xboole_0)
    | k1_xboole_0 = sK0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3231,plain,
    ( k1_xboole_0 = sK0(sK2,X0)
    | r1_tarski(sK0(sK2,X0),k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3223])).

cnf(c_3233,plain,
    ( k1_xboole_0 = sK0(sK2,k1_xboole_0)
    | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3231])).

cnf(c_206,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3250,plain,
    ( sK0(sK2,X0) = sK0(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_206])).

cnf(c_3255,plain,
    ( sK0(sK2,k1_xboole_0) = sK0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3250])).

cnf(c_19,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_605,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3754,plain,
    ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1280,c_605])).

cnf(c_207,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7474,plain,
    ( X0 != X1
    | sK0(sK2,X2) != X1
    | sK0(sK2,X2) = X0 ),
    inference(instantiation,[status(thm)],[c_207])).

cnf(c_11659,plain,
    ( X0 != sK0(sK2,X1)
    | sK0(sK2,X1) = X0
    | sK0(sK2,X1) != sK0(sK2,X1) ),
    inference(instantiation,[status(thm)],[c_7474])).

cnf(c_11660,plain,
    ( sK0(sK2,k1_xboole_0) != sK0(sK2,k1_xboole_0)
    | sK0(sK2,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != sK0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_11659])).

cnf(c_25882,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6873,c_25,c_839,c_1003,c_3233,c_3255,c_3754,c_11660])).

cnf(c_602,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_613,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1620,plain,
    ( l1_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_602,c_613])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_614,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4294,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(superposition,[status(thm)],[c_1620,c_614])).

cnf(c_25888,plain,
    ( v4_pre_topc(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_25882,c_4294])).

cnf(c_25895,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_638,c_25888])).

cnf(c_12,plain,
    ( v4_pre_topc(k2_struct_0(X0),X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_818,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_819,plain,
    ( v4_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
    | v2_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_818])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( v2_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_25895,c_819,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:15:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.63/1.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.50  
% 7.63/1.50  ------  iProver source info
% 7.63/1.50  
% 7.63/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.50  git: non_committed_changes: false
% 7.63/1.50  git: last_make_outside_of_git: false
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    --mode clausify
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             sel
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         604.99
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              none
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           false
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             false
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         false
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     num_symb
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       true
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     false
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   []
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_full_bw                           [BwDemod]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  ------ Parsing...
% 7.63/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.50  ------ Proving...
% 7.63/1.50  ------ Problem Properties 
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  clauses                                 24
% 7.63/1.50  conjectures                             5
% 7.63/1.50  EPR                                     7
% 7.63/1.50  Horn                                    22
% 7.63/1.50  unary                                   11
% 7.63/1.50  binary                                  6
% 7.63/1.50  lits                                    58
% 7.63/1.50  lits eq                                 10
% 7.63/1.50  fd_pure                                 0
% 7.63/1.50  fd_pseudo                               0
% 7.63/1.50  fd_cond                                 2
% 7.63/1.50  fd_pseudo_cond                          0
% 7.63/1.50  AC symbols                              0
% 7.63/1.50  
% 7.63/1.50  ------ Input Options Time Limit: Unbounded
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ 
% 7.63/1.50  Current options:
% 7.63/1.50  ------ 
% 7.63/1.50  
% 7.63/1.50  ------ Input Options
% 7.63/1.50  
% 7.63/1.50  --out_options                           all
% 7.63/1.50  --tptp_safe_out                         true
% 7.63/1.50  --problem_path                          ""
% 7.63/1.50  --include_path                          ""
% 7.63/1.50  --clausifier                            res/vclausify_rel
% 7.63/1.50  --clausifier_options                    --mode clausify
% 7.63/1.50  --stdin                                 false
% 7.63/1.50  --stats_out                             sel
% 7.63/1.50  
% 7.63/1.50  ------ General Options
% 7.63/1.50  
% 7.63/1.50  --fof                                   false
% 7.63/1.50  --time_out_real                         604.99
% 7.63/1.50  --time_out_virtual                      -1.
% 7.63/1.50  --symbol_type_check                     false
% 7.63/1.50  --clausify_out                          false
% 7.63/1.50  --sig_cnt_out                           false
% 7.63/1.50  --trig_cnt_out                          false
% 7.63/1.50  --trig_cnt_out_tolerance                1.
% 7.63/1.50  --trig_cnt_out_sk_spl                   false
% 7.63/1.50  --abstr_cl_out                          false
% 7.63/1.50  
% 7.63/1.50  ------ Global Options
% 7.63/1.50  
% 7.63/1.50  --schedule                              none
% 7.63/1.50  --add_important_lit                     false
% 7.63/1.50  --prop_solver_per_cl                    1000
% 7.63/1.50  --min_unsat_core                        false
% 7.63/1.50  --soft_assumptions                      false
% 7.63/1.50  --soft_lemma_size                       3
% 7.63/1.50  --prop_impl_unit_size                   0
% 7.63/1.50  --prop_impl_unit                        []
% 7.63/1.50  --share_sel_clauses                     true
% 7.63/1.50  --reset_solvers                         false
% 7.63/1.50  --bc_imp_inh                            [conj_cone]
% 7.63/1.50  --conj_cone_tolerance                   3.
% 7.63/1.50  --extra_neg_conj                        none
% 7.63/1.50  --large_theory_mode                     true
% 7.63/1.50  --prolific_symb_bound                   200
% 7.63/1.50  --lt_threshold                          2000
% 7.63/1.50  --clause_weak_htbl                      true
% 7.63/1.50  --gc_record_bc_elim                     false
% 7.63/1.50  
% 7.63/1.50  ------ Preprocessing Options
% 7.63/1.50  
% 7.63/1.50  --preprocessing_flag                    true
% 7.63/1.50  --time_out_prep_mult                    0.1
% 7.63/1.50  --splitting_mode                        input
% 7.63/1.50  --splitting_grd                         true
% 7.63/1.50  --splitting_cvd                         false
% 7.63/1.50  --splitting_cvd_svl                     false
% 7.63/1.50  --splitting_nvd                         32
% 7.63/1.50  --sub_typing                            true
% 7.63/1.50  --prep_gs_sim                           false
% 7.63/1.50  --prep_unflatten                        true
% 7.63/1.50  --prep_res_sim                          true
% 7.63/1.50  --prep_upred                            true
% 7.63/1.50  --prep_sem_filter                       exhaustive
% 7.63/1.50  --prep_sem_filter_out                   false
% 7.63/1.50  --pred_elim                             false
% 7.63/1.50  --res_sim_input                         true
% 7.63/1.50  --eq_ax_congr_red                       true
% 7.63/1.50  --pure_diseq_elim                       true
% 7.63/1.50  --brand_transform                       false
% 7.63/1.50  --non_eq_to_eq                          false
% 7.63/1.50  --prep_def_merge                        true
% 7.63/1.50  --prep_def_merge_prop_impl              false
% 7.63/1.50  --prep_def_merge_mbd                    true
% 7.63/1.50  --prep_def_merge_tr_red                 false
% 7.63/1.50  --prep_def_merge_tr_cl                  false
% 7.63/1.50  --smt_preprocessing                     true
% 7.63/1.50  --smt_ac_axioms                         fast
% 7.63/1.50  --preprocessed_out                      false
% 7.63/1.50  --preprocessed_stats                    false
% 7.63/1.50  
% 7.63/1.50  ------ Abstraction refinement Options
% 7.63/1.50  
% 7.63/1.50  --abstr_ref                             []
% 7.63/1.50  --abstr_ref_prep                        false
% 7.63/1.50  --abstr_ref_until_sat                   false
% 7.63/1.50  --abstr_ref_sig_restrict                funpre
% 7.63/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.50  --abstr_ref_under                       []
% 7.63/1.50  
% 7.63/1.50  ------ SAT Options
% 7.63/1.50  
% 7.63/1.50  --sat_mode                              false
% 7.63/1.50  --sat_fm_restart_options                ""
% 7.63/1.50  --sat_gr_def                            false
% 7.63/1.50  --sat_epr_types                         true
% 7.63/1.50  --sat_non_cyclic_types                  false
% 7.63/1.50  --sat_finite_models                     false
% 7.63/1.50  --sat_fm_lemmas                         false
% 7.63/1.50  --sat_fm_prep                           false
% 7.63/1.50  --sat_fm_uc_incr                        true
% 7.63/1.50  --sat_out_model                         small
% 7.63/1.50  --sat_out_clauses                       false
% 7.63/1.50  
% 7.63/1.50  ------ QBF Options
% 7.63/1.50  
% 7.63/1.50  --qbf_mode                              false
% 7.63/1.50  --qbf_elim_univ                         false
% 7.63/1.50  --qbf_dom_inst                          none
% 7.63/1.50  --qbf_dom_pre_inst                      false
% 7.63/1.50  --qbf_sk_in                             false
% 7.63/1.50  --qbf_pred_elim                         true
% 7.63/1.50  --qbf_split                             512
% 7.63/1.50  
% 7.63/1.50  ------ BMC1 Options
% 7.63/1.50  
% 7.63/1.50  --bmc1_incremental                      false
% 7.63/1.50  --bmc1_axioms                           reachable_all
% 7.63/1.50  --bmc1_min_bound                        0
% 7.63/1.50  --bmc1_max_bound                        -1
% 7.63/1.50  --bmc1_max_bound_default                -1
% 7.63/1.50  --bmc1_symbol_reachability              true
% 7.63/1.50  --bmc1_property_lemmas                  false
% 7.63/1.50  --bmc1_k_induction                      false
% 7.63/1.50  --bmc1_non_equiv_states                 false
% 7.63/1.50  --bmc1_deadlock                         false
% 7.63/1.50  --bmc1_ucm                              false
% 7.63/1.50  --bmc1_add_unsat_core                   none
% 7.63/1.50  --bmc1_unsat_core_children              false
% 7.63/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.50  --bmc1_out_stat                         full
% 7.63/1.50  --bmc1_ground_init                      false
% 7.63/1.50  --bmc1_pre_inst_next_state              false
% 7.63/1.50  --bmc1_pre_inst_state                   false
% 7.63/1.50  --bmc1_pre_inst_reach_state             false
% 7.63/1.50  --bmc1_out_unsat_core                   false
% 7.63/1.50  --bmc1_aig_witness_out                  false
% 7.63/1.50  --bmc1_verbose                          false
% 7.63/1.50  --bmc1_dump_clauses_tptp                false
% 7.63/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.50  --bmc1_dump_file                        -
% 7.63/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.50  --bmc1_ucm_extend_mode                  1
% 7.63/1.50  --bmc1_ucm_init_mode                    2
% 7.63/1.50  --bmc1_ucm_cone_mode                    none
% 7.63/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.50  --bmc1_ucm_relax_model                  4
% 7.63/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.50  --bmc1_ucm_layered_model                none
% 7.63/1.50  --bmc1_ucm_max_lemma_size               10
% 7.63/1.50  
% 7.63/1.50  ------ AIG Options
% 7.63/1.50  
% 7.63/1.50  --aig_mode                              false
% 7.63/1.50  
% 7.63/1.50  ------ Instantiation Options
% 7.63/1.50  
% 7.63/1.50  --instantiation_flag                    true
% 7.63/1.50  --inst_sos_flag                         false
% 7.63/1.50  --inst_sos_phase                        true
% 7.63/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.50  --inst_lit_sel_side                     num_symb
% 7.63/1.50  --inst_solver_per_active                1400
% 7.63/1.50  --inst_solver_calls_frac                1.
% 7.63/1.50  --inst_passive_queue_type               priority_queues
% 7.63/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.50  --inst_passive_queues_freq              [25;2]
% 7.63/1.50  --inst_dismatching                      true
% 7.63/1.50  --inst_eager_unprocessed_to_passive     true
% 7.63/1.50  --inst_prop_sim_given                   true
% 7.63/1.50  --inst_prop_sim_new                     false
% 7.63/1.50  --inst_subs_new                         false
% 7.63/1.50  --inst_eq_res_simp                      false
% 7.63/1.50  --inst_subs_given                       false
% 7.63/1.50  --inst_orphan_elimination               true
% 7.63/1.50  --inst_learning_loop_flag               true
% 7.63/1.50  --inst_learning_start                   3000
% 7.63/1.50  --inst_learning_factor                  2
% 7.63/1.50  --inst_start_prop_sim_after_learn       3
% 7.63/1.50  --inst_sel_renew                        solver
% 7.63/1.50  --inst_lit_activity_flag                true
% 7.63/1.50  --inst_restr_to_given                   false
% 7.63/1.50  --inst_activity_threshold               500
% 7.63/1.50  --inst_out_proof                        true
% 7.63/1.50  
% 7.63/1.50  ------ Resolution Options
% 7.63/1.50  
% 7.63/1.50  --resolution_flag                       true
% 7.63/1.50  --res_lit_sel                           adaptive
% 7.63/1.50  --res_lit_sel_side                      none
% 7.63/1.50  --res_ordering                          kbo
% 7.63/1.50  --res_to_prop_solver                    active
% 7.63/1.50  --res_prop_simpl_new                    false
% 7.63/1.50  --res_prop_simpl_given                  true
% 7.63/1.50  --res_passive_queue_type                priority_queues
% 7.63/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.50  --res_passive_queues_freq               [15;5]
% 7.63/1.50  --res_forward_subs                      full
% 7.63/1.50  --res_backward_subs                     full
% 7.63/1.50  --res_forward_subs_resolution           true
% 7.63/1.50  --res_backward_subs_resolution          true
% 7.63/1.50  --res_orphan_elimination                true
% 7.63/1.50  --res_time_limit                        2.
% 7.63/1.50  --res_out_proof                         true
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Options
% 7.63/1.50  
% 7.63/1.50  --superposition_flag                    true
% 7.63/1.50  --sup_passive_queue_type                priority_queues
% 7.63/1.50  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.50  --sup_passive_queues_freq               [1;4]
% 7.63/1.50  --demod_completeness_check              fast
% 7.63/1.50  --demod_use_ground                      true
% 7.63/1.50  --sup_to_prop_solver                    passive
% 7.63/1.50  --sup_prop_simpl_new                    true
% 7.63/1.50  --sup_prop_simpl_given                  true
% 7.63/1.50  --sup_fun_splitting                     false
% 7.63/1.50  --sup_smt_interval                      50000
% 7.63/1.50  
% 7.63/1.50  ------ Superposition Simplification Setup
% 7.63/1.50  
% 7.63/1.50  --sup_indices_passive                   []
% 7.63/1.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_full_bw                           [BwDemod]
% 7.63/1.50  --sup_immed_triv                        [TrivRules]
% 7.63/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_immed_bw_main                     []
% 7.63/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.50  
% 7.63/1.50  ------ Combination Options
% 7.63/1.50  
% 7.63/1.50  --comb_res_mult                         3
% 7.63/1.50  --comb_sup_mult                         2
% 7.63/1.50  --comb_inst_mult                        10
% 7.63/1.50  
% 7.63/1.50  ------ Debug Options
% 7.63/1.50  
% 7.63/1.50  --dbg_backtrace                         false
% 7.63/1.50  --dbg_dump_prop_clauses                 false
% 7.63/1.50  --dbg_dump_prop_clauses_file            -
% 7.63/1.50  --dbg_out_stat                          false
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  ------ Proving...
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS status Theorem for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  fof(f9,axiom,(
% 7.63/1.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f49,plain,(
% 7.63/1.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f9])).
% 7.63/1.50  
% 7.63/1.50  fof(f8,axiom,(
% 7.63/1.50    ! [X0] : k2_subset_1(X0) = X0),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f48,plain,(
% 7.63/1.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 7.63/1.50    inference(cnf_transformation,[],[f8])).
% 7.63/1.50  
% 7.63/1.50  fof(f17,conjecture,(
% 7.63/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f18,negated_conjecture,(
% 7.63/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 7.63/1.50    inference(negated_conjecture,[],[f17])).
% 7.63/1.50  
% 7.63/1.50  fof(f19,plain,(
% 7.63/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 7.63/1.50    inference(pure_predicate_removal,[],[f18])).
% 7.63/1.50  
% 7.63/1.50  fof(f31,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f19])).
% 7.63/1.50  
% 7.63/1.50  fof(f32,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 7.63/1.50    inference(flattening,[],[f31])).
% 7.63/1.50  
% 7.63/1.50  fof(f39,plain,(
% 7.63/1.50    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f38,plain,(
% 7.63/1.50    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f40,plain,(
% 7.63/1.50    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f39,f38])).
% 7.63/1.50  
% 7.63/1.50  fof(f64,plain,(
% 7.63/1.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.63/1.50    inference(cnf_transformation,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  fof(f7,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f23,plain,(
% 7.63/1.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f7])).
% 7.63/1.50  
% 7.63/1.50  fof(f47,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f23])).
% 7.63/1.50  
% 7.63/1.50  fof(f63,plain,(
% 7.63/1.50    v1_xboole_0(sK3)),
% 7.63/1.50    inference(cnf_transformation,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  fof(f2,axiom,(
% 7.63/1.50    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f21,plain,(
% 7.63/1.50    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f2])).
% 7.63/1.50  
% 7.63/1.50  fof(f42,plain,(
% 7.63/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f21])).
% 7.63/1.50  
% 7.63/1.50  fof(f11,axiom,(
% 7.63/1.50    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f51,plain,(
% 7.63/1.50    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f11])).
% 7.63/1.50  
% 7.63/1.50  fof(f10,axiom,(
% 7.63/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f24,plain,(
% 7.63/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f10])).
% 7.63/1.50  
% 7.63/1.50  fof(f50,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f24])).
% 7.63/1.50  
% 7.63/1.50  fof(f6,axiom,(
% 7.63/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f46,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 7.63/1.50    inference(cnf_transformation,[],[f6])).
% 7.63/1.50  
% 7.63/1.50  fof(f67,plain,(
% 7.63/1.50    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.63/1.50    inference(definition_unfolding,[],[f50,f46])).
% 7.63/1.50  
% 7.63/1.50  fof(f4,axiom,(
% 7.63/1.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f44,plain,(
% 7.63/1.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 7.63/1.50    inference(cnf_transformation,[],[f4])).
% 7.63/1.50  
% 7.63/1.50  fof(f1,axiom,(
% 7.63/1.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f41,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f1])).
% 7.63/1.50  
% 7.63/1.50  fof(f66,plain,(
% 7.63/1.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 7.63/1.50    inference(definition_unfolding,[],[f41,f46,f46])).
% 7.63/1.50  
% 7.63/1.50  fof(f3,axiom,(
% 7.63/1.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f43,plain,(
% 7.63/1.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f3])).
% 7.63/1.50  
% 7.63/1.50  fof(f5,axiom,(
% 7.63/1.50    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f22,plain,(
% 7.63/1.50    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 7.63/1.50    inference(ennf_transformation,[],[f5])).
% 7.63/1.50  
% 7.63/1.50  fof(f45,plain,(
% 7.63/1.50    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f22])).
% 7.63/1.50  
% 7.63/1.50  fof(f16,axiom,(
% 7.63/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f29,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f16])).
% 7.63/1.50  
% 7.63/1.50  fof(f30,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(flattening,[],[f29])).
% 7.63/1.50  
% 7.63/1.50  fof(f33,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(nnf_transformation,[],[f30])).
% 7.63/1.50  
% 7.63/1.50  fof(f34,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(rectify,[],[f33])).
% 7.63/1.50  
% 7.63/1.50  fof(f36,plain,(
% 7.63/1.50    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f35,plain,(
% 7.63/1.50    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.63/1.50    introduced(choice_axiom,[])).
% 7.63/1.50  
% 7.63/1.50  fof(f37,plain,(
% 7.63/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v4_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 7.63/1.50  
% 7.63/1.50  fof(f60,plain,(
% 7.63/1.50    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f37])).
% 7.63/1.50  
% 7.63/1.50  fof(f62,plain,(
% 7.63/1.50    l1_pre_topc(sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  fof(f59,plain,(
% 7.63/1.50    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f37])).
% 7.63/1.50  
% 7.63/1.50  fof(f65,plain,(
% 7.63/1.50    ~v2_tex_2(sK3,sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  fof(f14,axiom,(
% 7.63/1.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f26,plain,(
% 7.63/1.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f14])).
% 7.63/1.50  
% 7.63/1.50  fof(f53,plain,(
% 7.63/1.50    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f26])).
% 7.63/1.50  
% 7.63/1.50  fof(f13,axiom,(
% 7.63/1.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f25,plain,(
% 7.63/1.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 7.63/1.50    inference(ennf_transformation,[],[f13])).
% 7.63/1.50  
% 7.63/1.50  fof(f52,plain,(
% 7.63/1.50    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f25])).
% 7.63/1.50  
% 7.63/1.50  fof(f15,axiom,(
% 7.63/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 7.63/1.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.63/1.50  
% 7.63/1.50  fof(f27,plain,(
% 7.63/1.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 7.63/1.50    inference(ennf_transformation,[],[f15])).
% 7.63/1.50  
% 7.63/1.50  fof(f28,plain,(
% 7.63/1.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 7.63/1.50    inference(flattening,[],[f27])).
% 7.63/1.50  
% 7.63/1.50  fof(f54,plain,(
% 7.63/1.50    ( ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 7.63/1.50    inference(cnf_transformation,[],[f28])).
% 7.63/1.50  
% 7.63/1.50  fof(f61,plain,(
% 7.63/1.50    v2_pre_topc(sK2)),
% 7.63/1.50    inference(cnf_transformation,[],[f40])).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7,plain,
% 7.63/1.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f49]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_617,plain,
% 7.63/1.50      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6,plain,
% 7.63/1.50      ( k2_subset_1(X0) = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_638,plain,
% 7.63/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_617,c_6]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_20,negated_conjecture,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.63/1.50      inference(cnf_transformation,[],[f64]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_604,plain,
% 7.63/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_5,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.50      | k9_subset_1(X1,X0,X2) = k9_subset_1(X1,X2,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_618,plain,
% 7.63/1.50      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
% 7.63/1.50      | m1_subset_1(X1,k1_zfmisc_1(X0)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2019,plain,
% 7.63/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,sK3) = k9_subset_1(u1_struct_0(sK2),sK3,X0) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_604,c_618]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_21,negated_conjecture,
% 7.63/1.50      ( v1_xboole_0(sK3) ),
% 7.63/1.50      inference(cnf_transformation,[],[f63]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_603,plain,
% 7.63/1.50      ( v1_xboole_0(sK3) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1,plain,
% 7.63/1.50      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f42]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_621,plain,
% 7.63/1.50      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1280,plain,
% 7.63/1.50      ( sK3 = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_603,c_621]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6869,plain,
% 7.63/1.50      ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) = k9_subset_1(u1_struct_0(sK2),X0,k1_xboole_0) ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_2019,c_1280]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_9,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f51]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_615,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_8,plain,
% 7.63/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.63/1.50      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f67]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_616,plain,
% 7.63/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 7.63/1.50      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2320,plain,
% 7.63/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_615,c_616]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3,plain,
% 7.63/1.50      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_0,plain,
% 7.63/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 7.63/1.50      inference(cnf_transformation,[],[f66]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2,plain,
% 7.63/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f43]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_620,plain,
% 7.63/1.50      ( r1_tarski(k4_xboole_0(X0,X1),X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1222,plain,
% 7.63/1.50      ( r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_0,c_620]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4,plain,
% 7.63/1.50      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 7.63/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_619,plain,
% 7.63/1.50      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1716,plain,
% 7.63/1.50      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1222,c_619]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1719,plain,
% 7.63/1.50      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_1716,c_3]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_2350,plain,
% 7.63/1.50      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_2320,c_3,c_1719]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6870,plain,
% 7.63/1.50      ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,X0) = k1_xboole_0 ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_6869,c_2350]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_13,plain,
% 7.63/1.50      ( v2_tex_2(X0,X1)
% 7.63/1.50      | ~ v4_pre_topc(X2,X1)
% 7.63/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.50      | ~ l1_pre_topc(X1)
% 7.63/1.50      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f60]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_611,plain,
% 7.63/1.50      ( k9_subset_1(u1_struct_0(X0),X1,X2) != sK0(X0,X1)
% 7.63/1.50      | v2_tex_2(X1,X0) = iProver_top
% 7.63/1.50      | v4_pre_topc(X2,X0) != iProver_top
% 7.63/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.63/1.50      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 7.63/1.50      | l1_pre_topc(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_6873,plain,
% 7.63/1.50      ( sK0(sK2,k1_xboole_0) != k1_xboole_0
% 7.63/1.50      | v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 7.63/1.50      | v4_pre_topc(X0,sK2) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.63/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.63/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_6870,c_611]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_22,negated_conjecture,
% 7.63/1.50      ( l1_pre_topc(sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f62]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_25,plain,
% 7.63/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_14,plain,
% 7.63/1.50      ( v2_tex_2(X0,X1)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.63/1.50      | r1_tarski(sK0(X1,X0),X0)
% 7.63/1.50      | ~ l1_pre_topc(X1) ),
% 7.63/1.50      inference(cnf_transformation,[],[f59]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_836,plain,
% 7.63/1.50      ( v2_tex_2(X0,sK2)
% 7.63/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.63/1.50      | r1_tarski(sK0(sK2,X0),X0)
% 7.63/1.50      | ~ l1_pre_topc(sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_14]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_837,plain,
% 7.63/1.50      ( v2_tex_2(X0,sK2) = iProver_top
% 7.63/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.63/1.50      | r1_tarski(sK0(sK2,X0),X0) = iProver_top
% 7.63/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_836]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_839,plain,
% 7.63/1.50      ( v2_tex_2(k1_xboole_0,sK2) = iProver_top
% 7.63/1.50      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.63/1.50      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) = iProver_top
% 7.63/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_837]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1000,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_9]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1003,plain,
% 7.63/1.50      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_1000]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3223,plain,
% 7.63/1.50      ( ~ r1_tarski(sK0(sK2,X0),k1_xboole_0)
% 7.63/1.50      | k1_xboole_0 = sK0(sK2,X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_4]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3231,plain,
% 7.63/1.50      ( k1_xboole_0 = sK0(sK2,X0)
% 7.63/1.50      | r1_tarski(sK0(sK2,X0),k1_xboole_0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_3223]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3233,plain,
% 7.63/1.50      ( k1_xboole_0 = sK0(sK2,k1_xboole_0)
% 7.63/1.50      | r1_tarski(sK0(sK2,k1_xboole_0),k1_xboole_0) != iProver_top ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3231]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_206,plain,( X0 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3250,plain,
% 7.63/1.50      ( sK0(sK2,X0) = sK0(sK2,X0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_206]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3255,plain,
% 7.63/1.50      ( sK0(sK2,k1_xboole_0) = sK0(sK2,k1_xboole_0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_3250]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_19,negated_conjecture,
% 7.63/1.50      ( ~ v2_tex_2(sK3,sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f65]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_605,plain,
% 7.63/1.50      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_3754,plain,
% 7.63/1.50      ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
% 7.63/1.50      inference(demodulation,[status(thm)],[c_1280,c_605]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_207,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_7474,plain,
% 7.63/1.50      ( X0 != X1 | sK0(sK2,X2) != X1 | sK0(sK2,X2) = X0 ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_207]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_11659,plain,
% 7.63/1.50      ( X0 != sK0(sK2,X1)
% 7.63/1.50      | sK0(sK2,X1) = X0
% 7.63/1.50      | sK0(sK2,X1) != sK0(sK2,X1) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_7474]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_11660,plain,
% 7.63/1.50      ( sK0(sK2,k1_xboole_0) != sK0(sK2,k1_xboole_0)
% 7.63/1.50      | sK0(sK2,k1_xboole_0) = k1_xboole_0
% 7.63/1.50      | k1_xboole_0 != sK0(sK2,k1_xboole_0) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_11659]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_25882,plain,
% 7.63/1.50      ( v4_pre_topc(X0,sK2) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.63/1.50      inference(global_propositional_subsumption,
% 7.63/1.50                [status(thm)],
% 7.63/1.50                [c_6873,c_25,c_839,c_1003,c_3233,c_3255,c_3754,c_11660]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_602,plain,
% 7.63/1.50      ( l1_pre_topc(sK2) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_11,plain,
% 7.63/1.50      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_613,plain,
% 7.63/1.50      ( l1_pre_topc(X0) != iProver_top | l1_struct_0(X0) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_1620,plain,
% 7.63/1.50      ( l1_struct_0(sK2) = iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_602,c_613]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_10,plain,
% 7.63/1.50      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_614,plain,
% 7.63/1.50      ( u1_struct_0(X0) = k2_struct_0(X0)
% 7.63/1.50      | l1_struct_0(X0) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_4294,plain,
% 7.63/1.50      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_1620,c_614]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_25888,plain,
% 7.63/1.50      ( v4_pre_topc(X0,sK2) != iProver_top
% 7.63/1.50      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 7.63/1.50      inference(light_normalisation,[status(thm)],[c_25882,c_4294]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_25895,plain,
% 7.63/1.50      ( v4_pre_topc(k2_struct_0(sK2),sK2) != iProver_top ),
% 7.63/1.50      inference(superposition,[status(thm)],[c_638,c_25888]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_12,plain,
% 7.63/1.50      ( v4_pre_topc(k2_struct_0(X0),X0)
% 7.63/1.50      | ~ v2_pre_topc(X0)
% 7.63/1.50      | ~ l1_pre_topc(X0) ),
% 7.63/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_818,plain,
% 7.63/1.50      ( v4_pre_topc(k2_struct_0(sK2),sK2)
% 7.63/1.50      | ~ v2_pre_topc(sK2)
% 7.63/1.50      | ~ l1_pre_topc(sK2) ),
% 7.63/1.50      inference(instantiation,[status(thm)],[c_12]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_819,plain,
% 7.63/1.50      ( v4_pre_topc(k2_struct_0(sK2),sK2) = iProver_top
% 7.63/1.50      | v2_pre_topc(sK2) != iProver_top
% 7.63/1.50      | l1_pre_topc(sK2) != iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_818]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_23,negated_conjecture,
% 7.63/1.50      ( v2_pre_topc(sK2) ),
% 7.63/1.50      inference(cnf_transformation,[],[f61]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(c_24,plain,
% 7.63/1.50      ( v2_pre_topc(sK2) = iProver_top ),
% 7.63/1.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.63/1.50  
% 7.63/1.50  cnf(contradiction,plain,
% 7.63/1.50      ( $false ),
% 7.63/1.50      inference(minisat,[status(thm)],[c_25895,c_819,c_25,c_24]) ).
% 7.63/1.50  
% 7.63/1.50  
% 7.63/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.50  
% 7.63/1.50  ------                               Statistics
% 7.63/1.50  
% 7.63/1.50  ------ Selected
% 7.63/1.50  
% 7.63/1.50  total_time:                             0.772
% 7.63/1.50  
%------------------------------------------------------------------------------
