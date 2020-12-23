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
% DateTime   : Thu Dec  3 12:26:09 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 221 expanded)
%              Number of clauses        :   55 (  75 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   18
%              Number of atoms          :  338 ( 954 expanded)
%              Number of equality atoms :   78 ( 115 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f14,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f41,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f44,f43])).

fof(f72,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f50,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_17457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(X0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_17459,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_xboole_0,u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_17457])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_236,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_237,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_237])).

cnf(c_8723,plain,
    ( ~ r1_tarski(X0,u1_struct_0(sK4))
    | k9_subset_1(u1_struct_0(sK4),X1,X1) = X1 ),
    inference(instantiation,[status(thm)],[c_284])).

cnf(c_8725,plain,
    ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK4))
    | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8723])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2277,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_20,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_715,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_28])).

cnf(c_716,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_715])).

cnf(c_2263,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_2776,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_2263])).

cnf(c_717,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_719,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_25,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2274,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_450,plain,
    ( sK5 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_27])).

cnf(c_451,plain,
    ( k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_450])).

cnf(c_2291,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2274,c_451])).

cnf(c_2457,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2461,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2457])).

cnf(c_3224,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2776,c_719,c_2291,c_2461])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2283,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_4947,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2(sK4,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3224,c_2283])).

cnf(c_2275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3794,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2277,c_2275])).

cnf(c_5771,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4947,c_3794])).

cnf(c_1713,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2579,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != X2
    | k9_subset_1(u1_struct_0(sK4),X0,X1) = sK2(sK4,X0)
    | sK2(sK4,X0) != X2 ),
    inference(instantiation,[status(thm)],[c_1713])).

cnf(c_2580,plain,
    ( k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) = sK2(sK4,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK2(sK4,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2579])).

cnf(c_2409,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2291])).

cnf(c_19,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_18,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_390,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_391,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_395,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v3_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_28])).

cnf(c_396,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_395])).

cnf(c_415,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_396])).

cnf(c_416,plain,
    ( v3_pre_topc(k1_xboole_0,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_422,plain,
    ( v3_pre_topc(k1_xboole_0,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_416,c_10])).

cnf(c_578,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_422])).

cnf(c_579,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k9_subset_1(u1_struct_0(sK4),X0,k1_xboole_0) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_581,plain,
    ( v2_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) != sK2(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_579])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17459,c_8725,c_5771,c_2580,c_2457,c_2409,c_581,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.32  % Computer   : n013.cluster.edu
% 0.10/0.32  % Model      : x86_64 x86_64
% 0.10/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.32  % Memory     : 8042.1875MB
% 0.10/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.32  % CPULimit   : 60
% 0.10/0.32  % WCLimit    : 600
% 0.10/0.32  % DateTime   : Tue Dec  1 20:55:09 EST 2020
% 0.10/0.32  % CPUTime    : 
% 0.10/0.32  % Running in FOF mode
% 2.14/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.14/0.97  
% 2.14/0.97  ------  iProver source info
% 2.14/0.97  
% 2.14/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.14/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.14/0.97  git: non_committed_changes: false
% 2.14/0.97  git: last_make_outside_of_git: false
% 2.14/0.97  
% 2.14/0.97  ------ 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options
% 2.14/0.97  
% 2.14/0.97  --out_options                           all
% 2.14/0.97  --tptp_safe_out                         true
% 2.14/0.97  --problem_path                          ""
% 2.14/0.97  --include_path                          ""
% 2.14/0.97  --clausifier                            res/vclausify_rel
% 2.14/0.97  --clausifier_options                    --mode clausify
% 2.14/0.97  --stdin                                 false
% 2.14/0.97  --stats_out                             all
% 2.14/0.97  
% 2.14/0.97  ------ General Options
% 2.14/0.97  
% 2.14/0.97  --fof                                   false
% 2.14/0.97  --time_out_real                         305.
% 2.14/0.97  --time_out_virtual                      -1.
% 2.14/0.97  --symbol_type_check                     false
% 2.14/0.97  --clausify_out                          false
% 2.14/0.97  --sig_cnt_out                           false
% 2.14/0.97  --trig_cnt_out                          false
% 2.14/0.97  --trig_cnt_out_tolerance                1.
% 2.14/0.97  --trig_cnt_out_sk_spl                   false
% 2.14/0.97  --abstr_cl_out                          false
% 2.14/0.97  
% 2.14/0.97  ------ Global Options
% 2.14/0.97  
% 2.14/0.97  --schedule                              default
% 2.14/0.97  --add_important_lit                     false
% 2.14/0.97  --prop_solver_per_cl                    1000
% 2.14/0.97  --min_unsat_core                        false
% 2.14/0.97  --soft_assumptions                      false
% 2.14/0.97  --soft_lemma_size                       3
% 2.14/0.97  --prop_impl_unit_size                   0
% 2.14/0.97  --prop_impl_unit                        []
% 2.14/0.97  --share_sel_clauses                     true
% 2.14/0.97  --reset_solvers                         false
% 2.14/0.97  --bc_imp_inh                            [conj_cone]
% 2.14/0.97  --conj_cone_tolerance                   3.
% 2.14/0.97  --extra_neg_conj                        none
% 2.14/0.97  --large_theory_mode                     true
% 2.14/0.97  --prolific_symb_bound                   200
% 2.14/0.97  --lt_threshold                          2000
% 2.14/0.97  --clause_weak_htbl                      true
% 2.14/0.97  --gc_record_bc_elim                     false
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing Options
% 2.14/0.97  
% 2.14/0.97  --preprocessing_flag                    true
% 2.14/0.97  --time_out_prep_mult                    0.1
% 2.14/0.97  --splitting_mode                        input
% 2.14/0.97  --splitting_grd                         true
% 2.14/0.97  --splitting_cvd                         false
% 2.14/0.97  --splitting_cvd_svl                     false
% 2.14/0.97  --splitting_nvd                         32
% 2.14/0.97  --sub_typing                            true
% 2.14/0.97  --prep_gs_sim                           true
% 2.14/0.97  --prep_unflatten                        true
% 2.14/0.97  --prep_res_sim                          true
% 2.14/0.97  --prep_upred                            true
% 2.14/0.97  --prep_sem_filter                       exhaustive
% 2.14/0.97  --prep_sem_filter_out                   false
% 2.14/0.97  --pred_elim                             true
% 2.14/0.97  --res_sim_input                         true
% 2.14/0.97  --eq_ax_congr_red                       true
% 2.14/0.97  --pure_diseq_elim                       true
% 2.14/0.97  --brand_transform                       false
% 2.14/0.97  --non_eq_to_eq                          false
% 2.14/0.97  --prep_def_merge                        true
% 2.14/0.97  --prep_def_merge_prop_impl              false
% 2.14/0.97  --prep_def_merge_mbd                    true
% 2.14/0.97  --prep_def_merge_tr_red                 false
% 2.14/0.97  --prep_def_merge_tr_cl                  false
% 2.14/0.97  --smt_preprocessing                     true
% 2.14/0.97  --smt_ac_axioms                         fast
% 2.14/0.97  --preprocessed_out                      false
% 2.14/0.97  --preprocessed_stats                    false
% 2.14/0.97  
% 2.14/0.97  ------ Abstraction refinement Options
% 2.14/0.97  
% 2.14/0.97  --abstr_ref                             []
% 2.14/0.97  --abstr_ref_prep                        false
% 2.14/0.97  --abstr_ref_until_sat                   false
% 2.14/0.97  --abstr_ref_sig_restrict                funpre
% 2.14/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.97  --abstr_ref_under                       []
% 2.14/0.97  
% 2.14/0.97  ------ SAT Options
% 2.14/0.97  
% 2.14/0.97  --sat_mode                              false
% 2.14/0.97  --sat_fm_restart_options                ""
% 2.14/0.97  --sat_gr_def                            false
% 2.14/0.97  --sat_epr_types                         true
% 2.14/0.97  --sat_non_cyclic_types                  false
% 2.14/0.97  --sat_finite_models                     false
% 2.14/0.97  --sat_fm_lemmas                         false
% 2.14/0.97  --sat_fm_prep                           false
% 2.14/0.97  --sat_fm_uc_incr                        true
% 2.14/0.97  --sat_out_model                         small
% 2.14/0.97  --sat_out_clauses                       false
% 2.14/0.97  
% 2.14/0.97  ------ QBF Options
% 2.14/0.97  
% 2.14/0.97  --qbf_mode                              false
% 2.14/0.97  --qbf_elim_univ                         false
% 2.14/0.97  --qbf_dom_inst                          none
% 2.14/0.97  --qbf_dom_pre_inst                      false
% 2.14/0.97  --qbf_sk_in                             false
% 2.14/0.97  --qbf_pred_elim                         true
% 2.14/0.97  --qbf_split                             512
% 2.14/0.97  
% 2.14/0.97  ------ BMC1 Options
% 2.14/0.97  
% 2.14/0.97  --bmc1_incremental                      false
% 2.14/0.97  --bmc1_axioms                           reachable_all
% 2.14/0.97  --bmc1_min_bound                        0
% 2.14/0.97  --bmc1_max_bound                        -1
% 2.14/0.97  --bmc1_max_bound_default                -1
% 2.14/0.97  --bmc1_symbol_reachability              true
% 2.14/0.97  --bmc1_property_lemmas                  false
% 2.14/0.97  --bmc1_k_induction                      false
% 2.14/0.97  --bmc1_non_equiv_states                 false
% 2.14/0.97  --bmc1_deadlock                         false
% 2.14/0.97  --bmc1_ucm                              false
% 2.14/0.97  --bmc1_add_unsat_core                   none
% 2.14/0.97  --bmc1_unsat_core_children              false
% 2.14/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.97  --bmc1_out_stat                         full
% 2.14/0.97  --bmc1_ground_init                      false
% 2.14/0.97  --bmc1_pre_inst_next_state              false
% 2.14/0.97  --bmc1_pre_inst_state                   false
% 2.14/0.97  --bmc1_pre_inst_reach_state             false
% 2.14/0.97  --bmc1_out_unsat_core                   false
% 2.14/0.97  --bmc1_aig_witness_out                  false
% 2.14/0.97  --bmc1_verbose                          false
% 2.14/0.97  --bmc1_dump_clauses_tptp                false
% 2.14/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.97  --bmc1_dump_file                        -
% 2.14/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.97  --bmc1_ucm_extend_mode                  1
% 2.14/0.97  --bmc1_ucm_init_mode                    2
% 2.14/0.97  --bmc1_ucm_cone_mode                    none
% 2.14/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.97  --bmc1_ucm_relax_model                  4
% 2.14/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.97  --bmc1_ucm_layered_model                none
% 2.14/0.97  --bmc1_ucm_max_lemma_size               10
% 2.14/0.97  
% 2.14/0.97  ------ AIG Options
% 2.14/0.97  
% 2.14/0.97  --aig_mode                              false
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation Options
% 2.14/0.97  
% 2.14/0.97  --instantiation_flag                    true
% 2.14/0.97  --inst_sos_flag                         false
% 2.14/0.97  --inst_sos_phase                        true
% 2.14/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel_side                     num_symb
% 2.14/0.97  --inst_solver_per_active                1400
% 2.14/0.97  --inst_solver_calls_frac                1.
% 2.14/0.97  --inst_passive_queue_type               priority_queues
% 2.14/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.97  --inst_passive_queues_freq              [25;2]
% 2.14/0.97  --inst_dismatching                      true
% 2.14/0.97  --inst_eager_unprocessed_to_passive     true
% 2.14/0.97  --inst_prop_sim_given                   true
% 2.14/0.97  --inst_prop_sim_new                     false
% 2.14/0.97  --inst_subs_new                         false
% 2.14/0.97  --inst_eq_res_simp                      false
% 2.14/0.97  --inst_subs_given                       false
% 2.14/0.97  --inst_orphan_elimination               true
% 2.14/0.97  --inst_learning_loop_flag               true
% 2.14/0.97  --inst_learning_start                   3000
% 2.14/0.97  --inst_learning_factor                  2
% 2.14/0.97  --inst_start_prop_sim_after_learn       3
% 2.14/0.97  --inst_sel_renew                        solver
% 2.14/0.97  --inst_lit_activity_flag                true
% 2.14/0.97  --inst_restr_to_given                   false
% 2.14/0.97  --inst_activity_threshold               500
% 2.14/0.97  --inst_out_proof                        true
% 2.14/0.97  
% 2.14/0.97  ------ Resolution Options
% 2.14/0.97  
% 2.14/0.97  --resolution_flag                       true
% 2.14/0.97  --res_lit_sel                           adaptive
% 2.14/0.97  --res_lit_sel_side                      none
% 2.14/0.97  --res_ordering                          kbo
% 2.14/0.97  --res_to_prop_solver                    active
% 2.14/0.97  --res_prop_simpl_new                    false
% 2.14/0.97  --res_prop_simpl_given                  true
% 2.14/0.97  --res_passive_queue_type                priority_queues
% 2.14/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.97  --res_passive_queues_freq               [15;5]
% 2.14/0.97  --res_forward_subs                      full
% 2.14/0.97  --res_backward_subs                     full
% 2.14/0.97  --res_forward_subs_resolution           true
% 2.14/0.97  --res_backward_subs_resolution          true
% 2.14/0.97  --res_orphan_elimination                true
% 2.14/0.97  --res_time_limit                        2.
% 2.14/0.97  --res_out_proof                         true
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Options
% 2.14/0.97  
% 2.14/0.97  --superposition_flag                    true
% 2.14/0.97  --sup_passive_queue_type                priority_queues
% 2.14/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.97  --demod_completeness_check              fast
% 2.14/0.97  --demod_use_ground                      true
% 2.14/0.97  --sup_to_prop_solver                    passive
% 2.14/0.97  --sup_prop_simpl_new                    true
% 2.14/0.97  --sup_prop_simpl_given                  true
% 2.14/0.97  --sup_fun_splitting                     false
% 2.14/0.97  --sup_smt_interval                      50000
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Simplification Setup
% 2.14/0.97  
% 2.14/0.97  --sup_indices_passive                   []
% 2.14/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_full_bw                           [BwDemod]
% 2.14/0.97  --sup_immed_triv                        [TrivRules]
% 2.14/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_immed_bw_main                     []
% 2.14/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  
% 2.14/0.97  ------ Combination Options
% 2.14/0.97  
% 2.14/0.97  --comb_res_mult                         3
% 2.14/0.97  --comb_sup_mult                         2
% 2.14/0.97  --comb_inst_mult                        10
% 2.14/0.97  
% 2.14/0.97  ------ Debug Options
% 2.14/0.97  
% 2.14/0.97  --dbg_backtrace                         false
% 2.14/0.97  --dbg_dump_prop_clauses                 false
% 2.14/0.97  --dbg_dump_prop_clauses_file            -
% 2.14/0.97  --dbg_out_stat                          false
% 2.14/0.97  ------ Parsing...
% 2.14/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.14/0.97  ------ Proving...
% 2.14/0.97  ------ Problem Properties 
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  clauses                                 26
% 2.14/0.97  conjectures                             2
% 2.14/0.97  EPR                                     6
% 2.14/0.97  Horn                                    23
% 2.14/0.97  unary                                   9
% 2.14/0.97  binary                                  9
% 2.14/0.97  lits                                    59
% 2.14/0.97  lits eq                                 14
% 2.14/0.97  fd_pure                                 0
% 2.14/0.97  fd_pseudo                               0
% 2.14/0.97  fd_cond                                 5
% 2.14/0.97  fd_pseudo_cond                          1
% 2.14/0.97  AC symbols                              0
% 2.14/0.97  
% 2.14/0.97  ------ Schedule dynamic 5 is on 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  ------ 
% 2.14/0.97  Current options:
% 2.14/0.97  ------ 
% 2.14/0.97  
% 2.14/0.97  ------ Input Options
% 2.14/0.97  
% 2.14/0.97  --out_options                           all
% 2.14/0.97  --tptp_safe_out                         true
% 2.14/0.97  --problem_path                          ""
% 2.14/0.97  --include_path                          ""
% 2.14/0.97  --clausifier                            res/vclausify_rel
% 2.14/0.97  --clausifier_options                    --mode clausify
% 2.14/0.97  --stdin                                 false
% 2.14/0.97  --stats_out                             all
% 2.14/0.97  
% 2.14/0.97  ------ General Options
% 2.14/0.97  
% 2.14/0.97  --fof                                   false
% 2.14/0.97  --time_out_real                         305.
% 2.14/0.97  --time_out_virtual                      -1.
% 2.14/0.97  --symbol_type_check                     false
% 2.14/0.97  --clausify_out                          false
% 2.14/0.97  --sig_cnt_out                           false
% 2.14/0.97  --trig_cnt_out                          false
% 2.14/0.97  --trig_cnt_out_tolerance                1.
% 2.14/0.97  --trig_cnt_out_sk_spl                   false
% 2.14/0.97  --abstr_cl_out                          false
% 2.14/0.97  
% 2.14/0.97  ------ Global Options
% 2.14/0.97  
% 2.14/0.97  --schedule                              default
% 2.14/0.97  --add_important_lit                     false
% 2.14/0.97  --prop_solver_per_cl                    1000
% 2.14/0.97  --min_unsat_core                        false
% 2.14/0.97  --soft_assumptions                      false
% 2.14/0.97  --soft_lemma_size                       3
% 2.14/0.97  --prop_impl_unit_size                   0
% 2.14/0.97  --prop_impl_unit                        []
% 2.14/0.97  --share_sel_clauses                     true
% 2.14/0.97  --reset_solvers                         false
% 2.14/0.97  --bc_imp_inh                            [conj_cone]
% 2.14/0.97  --conj_cone_tolerance                   3.
% 2.14/0.97  --extra_neg_conj                        none
% 2.14/0.97  --large_theory_mode                     true
% 2.14/0.97  --prolific_symb_bound                   200
% 2.14/0.97  --lt_threshold                          2000
% 2.14/0.97  --clause_weak_htbl                      true
% 2.14/0.97  --gc_record_bc_elim                     false
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing Options
% 2.14/0.97  
% 2.14/0.97  --preprocessing_flag                    true
% 2.14/0.97  --time_out_prep_mult                    0.1
% 2.14/0.97  --splitting_mode                        input
% 2.14/0.97  --splitting_grd                         true
% 2.14/0.97  --splitting_cvd                         false
% 2.14/0.97  --splitting_cvd_svl                     false
% 2.14/0.97  --splitting_nvd                         32
% 2.14/0.97  --sub_typing                            true
% 2.14/0.97  --prep_gs_sim                           true
% 2.14/0.97  --prep_unflatten                        true
% 2.14/0.97  --prep_res_sim                          true
% 2.14/0.97  --prep_upred                            true
% 2.14/0.97  --prep_sem_filter                       exhaustive
% 2.14/0.97  --prep_sem_filter_out                   false
% 2.14/0.97  --pred_elim                             true
% 2.14/0.97  --res_sim_input                         true
% 2.14/0.97  --eq_ax_congr_red                       true
% 2.14/0.97  --pure_diseq_elim                       true
% 2.14/0.97  --brand_transform                       false
% 2.14/0.97  --non_eq_to_eq                          false
% 2.14/0.97  --prep_def_merge                        true
% 2.14/0.97  --prep_def_merge_prop_impl              false
% 2.14/0.97  --prep_def_merge_mbd                    true
% 2.14/0.97  --prep_def_merge_tr_red                 false
% 2.14/0.97  --prep_def_merge_tr_cl                  false
% 2.14/0.97  --smt_preprocessing                     true
% 2.14/0.97  --smt_ac_axioms                         fast
% 2.14/0.97  --preprocessed_out                      false
% 2.14/0.97  --preprocessed_stats                    false
% 2.14/0.97  
% 2.14/0.97  ------ Abstraction refinement Options
% 2.14/0.97  
% 2.14/0.97  --abstr_ref                             []
% 2.14/0.97  --abstr_ref_prep                        false
% 2.14/0.97  --abstr_ref_until_sat                   false
% 2.14/0.97  --abstr_ref_sig_restrict                funpre
% 2.14/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.14/0.97  --abstr_ref_under                       []
% 2.14/0.97  
% 2.14/0.97  ------ SAT Options
% 2.14/0.97  
% 2.14/0.97  --sat_mode                              false
% 2.14/0.97  --sat_fm_restart_options                ""
% 2.14/0.97  --sat_gr_def                            false
% 2.14/0.97  --sat_epr_types                         true
% 2.14/0.97  --sat_non_cyclic_types                  false
% 2.14/0.97  --sat_finite_models                     false
% 2.14/0.97  --sat_fm_lemmas                         false
% 2.14/0.97  --sat_fm_prep                           false
% 2.14/0.97  --sat_fm_uc_incr                        true
% 2.14/0.97  --sat_out_model                         small
% 2.14/0.97  --sat_out_clauses                       false
% 2.14/0.97  
% 2.14/0.97  ------ QBF Options
% 2.14/0.97  
% 2.14/0.97  --qbf_mode                              false
% 2.14/0.97  --qbf_elim_univ                         false
% 2.14/0.97  --qbf_dom_inst                          none
% 2.14/0.97  --qbf_dom_pre_inst                      false
% 2.14/0.97  --qbf_sk_in                             false
% 2.14/0.97  --qbf_pred_elim                         true
% 2.14/0.97  --qbf_split                             512
% 2.14/0.97  
% 2.14/0.97  ------ BMC1 Options
% 2.14/0.97  
% 2.14/0.97  --bmc1_incremental                      false
% 2.14/0.97  --bmc1_axioms                           reachable_all
% 2.14/0.97  --bmc1_min_bound                        0
% 2.14/0.97  --bmc1_max_bound                        -1
% 2.14/0.97  --bmc1_max_bound_default                -1
% 2.14/0.97  --bmc1_symbol_reachability              true
% 2.14/0.97  --bmc1_property_lemmas                  false
% 2.14/0.97  --bmc1_k_induction                      false
% 2.14/0.97  --bmc1_non_equiv_states                 false
% 2.14/0.97  --bmc1_deadlock                         false
% 2.14/0.97  --bmc1_ucm                              false
% 2.14/0.97  --bmc1_add_unsat_core                   none
% 2.14/0.97  --bmc1_unsat_core_children              false
% 2.14/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.14/0.97  --bmc1_out_stat                         full
% 2.14/0.97  --bmc1_ground_init                      false
% 2.14/0.97  --bmc1_pre_inst_next_state              false
% 2.14/0.97  --bmc1_pre_inst_state                   false
% 2.14/0.97  --bmc1_pre_inst_reach_state             false
% 2.14/0.97  --bmc1_out_unsat_core                   false
% 2.14/0.97  --bmc1_aig_witness_out                  false
% 2.14/0.97  --bmc1_verbose                          false
% 2.14/0.97  --bmc1_dump_clauses_tptp                false
% 2.14/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.14/0.97  --bmc1_dump_file                        -
% 2.14/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.14/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.14/0.97  --bmc1_ucm_extend_mode                  1
% 2.14/0.97  --bmc1_ucm_init_mode                    2
% 2.14/0.97  --bmc1_ucm_cone_mode                    none
% 2.14/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.14/0.97  --bmc1_ucm_relax_model                  4
% 2.14/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.14/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.14/0.97  --bmc1_ucm_layered_model                none
% 2.14/0.97  --bmc1_ucm_max_lemma_size               10
% 2.14/0.97  
% 2.14/0.97  ------ AIG Options
% 2.14/0.97  
% 2.14/0.97  --aig_mode                              false
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation Options
% 2.14/0.97  
% 2.14/0.97  --instantiation_flag                    true
% 2.14/0.97  --inst_sos_flag                         false
% 2.14/0.97  --inst_sos_phase                        true
% 2.14/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.14/0.97  --inst_lit_sel_side                     none
% 2.14/0.97  --inst_solver_per_active                1400
% 2.14/0.97  --inst_solver_calls_frac                1.
% 2.14/0.97  --inst_passive_queue_type               priority_queues
% 2.14/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.14/0.97  --inst_passive_queues_freq              [25;2]
% 2.14/0.97  --inst_dismatching                      true
% 2.14/0.97  --inst_eager_unprocessed_to_passive     true
% 2.14/0.97  --inst_prop_sim_given                   true
% 2.14/0.97  --inst_prop_sim_new                     false
% 2.14/0.97  --inst_subs_new                         false
% 2.14/0.97  --inst_eq_res_simp                      false
% 2.14/0.97  --inst_subs_given                       false
% 2.14/0.97  --inst_orphan_elimination               true
% 2.14/0.97  --inst_learning_loop_flag               true
% 2.14/0.97  --inst_learning_start                   3000
% 2.14/0.97  --inst_learning_factor                  2
% 2.14/0.97  --inst_start_prop_sim_after_learn       3
% 2.14/0.97  --inst_sel_renew                        solver
% 2.14/0.97  --inst_lit_activity_flag                true
% 2.14/0.97  --inst_restr_to_given                   false
% 2.14/0.97  --inst_activity_threshold               500
% 2.14/0.97  --inst_out_proof                        true
% 2.14/0.97  
% 2.14/0.97  ------ Resolution Options
% 2.14/0.97  
% 2.14/0.97  --resolution_flag                       false
% 2.14/0.97  --res_lit_sel                           adaptive
% 2.14/0.97  --res_lit_sel_side                      none
% 2.14/0.97  --res_ordering                          kbo
% 2.14/0.97  --res_to_prop_solver                    active
% 2.14/0.97  --res_prop_simpl_new                    false
% 2.14/0.97  --res_prop_simpl_given                  true
% 2.14/0.97  --res_passive_queue_type                priority_queues
% 2.14/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.14/0.97  --res_passive_queues_freq               [15;5]
% 2.14/0.97  --res_forward_subs                      full
% 2.14/0.97  --res_backward_subs                     full
% 2.14/0.97  --res_forward_subs_resolution           true
% 2.14/0.97  --res_backward_subs_resolution          true
% 2.14/0.97  --res_orphan_elimination                true
% 2.14/0.97  --res_time_limit                        2.
% 2.14/0.97  --res_out_proof                         true
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Options
% 2.14/0.97  
% 2.14/0.97  --superposition_flag                    true
% 2.14/0.97  --sup_passive_queue_type                priority_queues
% 2.14/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.14/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.14/0.97  --demod_completeness_check              fast
% 2.14/0.97  --demod_use_ground                      true
% 2.14/0.97  --sup_to_prop_solver                    passive
% 2.14/0.97  --sup_prop_simpl_new                    true
% 2.14/0.97  --sup_prop_simpl_given                  true
% 2.14/0.97  --sup_fun_splitting                     false
% 2.14/0.97  --sup_smt_interval                      50000
% 2.14/0.97  
% 2.14/0.97  ------ Superposition Simplification Setup
% 2.14/0.97  
% 2.14/0.97  --sup_indices_passive                   []
% 2.14/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.14/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.14/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_full_bw                           [BwDemod]
% 2.14/0.97  --sup_immed_triv                        [TrivRules]
% 2.14/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.14/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_immed_bw_main                     []
% 2.14/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.14/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.14/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.14/0.97  
% 2.14/0.97  ------ Combination Options
% 2.14/0.97  
% 2.14/0.97  --comb_res_mult                         3
% 2.14/0.97  --comb_sup_mult                         2
% 2.14/0.97  --comb_inst_mult                        10
% 2.14/0.97  
% 2.14/0.97  ------ Debug Options
% 2.14/0.97  
% 2.14/0.97  --dbg_backtrace                         false
% 2.14/0.97  --dbg_dump_prop_clauses                 false
% 2.14/0.97  --dbg_dump_prop_clauses_file            -
% 2.14/0.97  --dbg_out_stat                          false
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  ------ Proving...
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  % SZS status Theorem for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  fof(f9,axiom,(
% 2.14/0.97    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f35,plain,(
% 2.14/0.97    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.14/0.97    inference(nnf_transformation,[],[f9])).
% 2.14/0.97  
% 2.14/0.97  fof(f57,plain,(
% 2.14/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.14/0.97    inference(cnf_transformation,[],[f35])).
% 2.14/0.97  
% 2.14/0.97  fof(f7,axiom,(
% 2.14/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f19,plain,(
% 2.14/0.97    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.14/0.97    inference(ennf_transformation,[],[f7])).
% 2.14/0.97  
% 2.14/0.97  fof(f55,plain,(
% 2.14/0.97    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.14/0.97    inference(cnf_transformation,[],[f19])).
% 2.14/0.97  
% 2.14/0.97  fof(f58,plain,(
% 2.14/0.97    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f35])).
% 2.14/0.97  
% 2.14/0.97  fof(f8,axiom,(
% 2.14/0.97    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f56,plain,(
% 2.14/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.14/0.97    inference(cnf_transformation,[],[f8])).
% 2.14/0.97  
% 2.14/0.97  fof(f14,axiom,(
% 2.14/0.97    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f26,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.97    inference(ennf_transformation,[],[f14])).
% 2.14/0.97  
% 2.14/0.97  fof(f27,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.97    inference(flattening,[],[f26])).
% 2.14/0.97  
% 2.14/0.97  fof(f38,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.97    inference(nnf_transformation,[],[f27])).
% 2.14/0.97  
% 2.14/0.97  fof(f39,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.97    inference(rectify,[],[f38])).
% 2.14/0.97  
% 2.14/0.97  fof(f41,plain,(
% 2.14/0.97    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f40,plain,(
% 2.14/0.97    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f42,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f39,f41,f40])).
% 2.14/0.97  
% 2.14/0.97  fof(f69,plain,(
% 2.14/0.97    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f42])).
% 2.14/0.97  
% 2.14/0.97  fof(f15,conjecture,(
% 2.14/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f16,negated_conjecture,(
% 2.14/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.14/0.97    inference(negated_conjecture,[],[f15])).
% 2.14/0.97  
% 2.14/0.97  fof(f17,plain,(
% 2.14/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.14/0.97    inference(pure_predicate_removal,[],[f16])).
% 2.14/0.97  
% 2.14/0.97  fof(f28,plain,(
% 2.14/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.14/0.97    inference(ennf_transformation,[],[f17])).
% 2.14/0.97  
% 2.14/0.97  fof(f29,plain,(
% 2.14/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.14/0.97    inference(flattening,[],[f28])).
% 2.14/0.97  
% 2.14/0.97  fof(f44,plain,(
% 2.14/0.97    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f43,plain,(
% 2.14/0.97    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.14/0.97    introduced(choice_axiom,[])).
% 2.14/0.97  
% 2.14/0.97  fof(f45,plain,(
% 2.14/0.97    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.14/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f29,f44,f43])).
% 2.14/0.97  
% 2.14/0.97  fof(f72,plain,(
% 2.14/0.97    l1_pre_topc(sK4)),
% 2.14/0.97    inference(cnf_transformation,[],[f45])).
% 2.14/0.97  
% 2.14/0.97  fof(f75,plain,(
% 2.14/0.97    ~v2_tex_2(sK5,sK4)),
% 2.14/0.97    inference(cnf_transformation,[],[f45])).
% 2.14/0.97  
% 2.14/0.97  fof(f2,axiom,(
% 2.14/0.97    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f18,plain,(
% 2.14/0.97    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.14/0.97    inference(ennf_transformation,[],[f2])).
% 2.14/0.97  
% 2.14/0.97  fof(f47,plain,(
% 2.14/0.97    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f18])).
% 2.14/0.97  
% 2.14/0.97  fof(f73,plain,(
% 2.14/0.97    v1_xboole_0(sK5)),
% 2.14/0.97    inference(cnf_transformation,[],[f45])).
% 2.14/0.97  
% 2.14/0.97  fof(f3,axiom,(
% 2.14/0.97    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f30,plain,(
% 2.14/0.97    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.97    inference(nnf_transformation,[],[f3])).
% 2.14/0.97  
% 2.14/0.97  fof(f31,plain,(
% 2.14/0.97    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.14/0.97    inference(flattening,[],[f30])).
% 2.14/0.97  
% 2.14/0.97  fof(f50,plain,(
% 2.14/0.97    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f31])).
% 2.14/0.97  
% 2.14/0.97  fof(f70,plain,(
% 2.14/0.97    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f42])).
% 2.14/0.97  
% 2.14/0.97  fof(f1,axiom,(
% 2.14/0.97    v1_xboole_0(k1_xboole_0)),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f46,plain,(
% 2.14/0.97    v1_xboole_0(k1_xboole_0)),
% 2.14/0.97    inference(cnf_transformation,[],[f1])).
% 2.14/0.97  
% 2.14/0.97  fof(f13,axiom,(
% 2.14/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 2.14/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.14/0.97  
% 2.14/0.97  fof(f24,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.14/0.97    inference(ennf_transformation,[],[f13])).
% 2.14/0.97  
% 2.14/0.97  fof(f25,plain,(
% 2.14/0.97    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.14/0.97    inference(flattening,[],[f24])).
% 2.14/0.97  
% 2.14/0.97  fof(f64,plain,(
% 2.14/0.97    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.14/0.97    inference(cnf_transformation,[],[f25])).
% 2.14/0.97  
% 2.14/0.97  fof(f71,plain,(
% 2.14/0.97    v2_pre_topc(sK4)),
% 2.14/0.97    inference(cnf_transformation,[],[f45])).
% 2.14/0.97  
% 2.14/0.97  cnf(c_12,plain,
% 2.14/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_17457,plain,
% 2.14/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | r1_tarski(X0,u1_struct_0(sK4)) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_12]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_17459,plain,
% 2.14/0.97      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | r1_tarski(k1_xboole_0,u1_struct_0(sK4)) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_17457]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_9,plain,
% 2.14/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 2.14/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_11,plain,
% 2.14/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_236,plain,
% 2.14/0.97      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.14/0.97      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_237,plain,
% 2.14/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.14/0.97      inference(renaming,[status(thm)],[c_236]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_284,plain,
% 2.14/0.97      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 2.14/0.97      inference(bin_hyper_res,[status(thm)],[c_9,c_237]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_8723,plain,
% 2.14/0.97      ( ~ r1_tarski(X0,u1_struct_0(sK4))
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),X1,X1) = X1 ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_284]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_8725,plain,
% 2.14/0.97      ( ~ r1_tarski(k1_xboole_0,u1_struct_0(sK4))
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_8723]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_10,plain,
% 2.14/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.14/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2277,plain,
% 2.14/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_20,plain,
% 2.14/0.97      ( v2_tex_2(X0,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | r1_tarski(sK2(X1,X0),X0)
% 2.14/0.97      | ~ l1_pre_topc(X1) ),
% 2.14/0.97      inference(cnf_transformation,[],[f69]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_28,negated_conjecture,
% 2.14/0.97      ( l1_pre_topc(sK4) ),
% 2.14/0.97      inference(cnf_transformation,[],[f72]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_715,plain,
% 2.14/0.97      ( v2_tex_2(X0,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | r1_tarski(sK2(X1,X0),X0)
% 2.14/0.97      | sK4 != X1 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_20,c_28]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_716,plain,
% 2.14/0.97      ( v2_tex_2(X0,sK4)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | r1_tarski(sK2(sK4,X0),X0) ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_715]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2263,plain,
% 2.14/0.97      ( v2_tex_2(X0,sK4) = iProver_top
% 2.14/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.14/0.97      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2776,plain,
% 2.14/0.97      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.14/0.97      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_2277,c_2263]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_717,plain,
% 2.14/0.97      ( v2_tex_2(X0,sK4) = iProver_top
% 2.14/0.97      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.14/0.97      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_719,plain,
% 2.14/0.97      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.14/0.97      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.14/0.97      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_717]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_25,negated_conjecture,
% 2.14/0.97      ( ~ v2_tex_2(sK5,sK4) ),
% 2.14/0.97      inference(cnf_transformation,[],[f75]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2274,plain,
% 2.14/0.97      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1,plain,
% 2.14/0.97      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.14/0.97      inference(cnf_transformation,[],[f47]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_27,negated_conjecture,
% 2.14/0.97      ( v1_xboole_0(sK5) ),
% 2.14/0.97      inference(cnf_transformation,[],[f73]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_450,plain,
% 2.14/0.97      ( sK5 != X0 | k1_xboole_0 = X0 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_1,c_27]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_451,plain,
% 2.14/0.97      ( k1_xboole_0 = sK5 ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_450]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2291,plain,
% 2.14/0.97      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 2.14/0.97      inference(light_normalisation,[status(thm)],[c_2274,c_451]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2457,plain,
% 2.14/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_10]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2461,plain,
% 2.14/0.97      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_2457]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_3224,plain,
% 2.14/0.97      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.14/0.97      inference(global_propositional_subsumption,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_2776,c_719,c_2291,c_2461]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2,plain,
% 2.14/0.97      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.14/0.97      inference(cnf_transformation,[],[f50]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2283,plain,
% 2.14/0.97      ( X0 = X1
% 2.14/0.97      | r1_tarski(X0,X1) != iProver_top
% 2.14/0.97      | r1_tarski(X1,X0) != iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_4947,plain,
% 2.14/0.97      ( sK2(sK4,k1_xboole_0) = k1_xboole_0
% 2.14/0.97      | r1_tarski(k1_xboole_0,sK2(sK4,k1_xboole_0)) != iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_3224,c_2283]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2275,plain,
% 2.14/0.97      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.14/0.97      | r1_tarski(X0,X1) = iProver_top ),
% 2.14/0.97      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_3794,plain,
% 2.14/0.97      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.14/0.97      inference(superposition,[status(thm)],[c_2277,c_2275]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_5771,plain,
% 2.14/0.97      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 2.14/0.97      inference(forward_subsumption_resolution,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_4947,c_3794]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_1713,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2579,plain,
% 2.14/0.97      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != X2
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),X0,X1) = sK2(sK4,X0)
% 2.14/0.97      | sK2(sK4,X0) != X2 ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_1713]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2580,plain,
% 2.14/0.97      ( k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) = sK2(sK4,k1_xboole_0)
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 2.14/0.97      | sK2(sK4,k1_xboole_0) != k1_xboole_0 ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_2579]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_2409,plain,
% 2.14/0.97      ( ~ v2_tex_2(k1_xboole_0,sK4) ),
% 2.14/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_2291]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_19,plain,
% 2.14/0.97      ( v2_tex_2(X0,X1)
% 2.14/0.97      | ~ v3_pre_topc(X2,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ l1_pre_topc(X1)
% 2.14/0.97      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 2.14/0.97      inference(cnf_transformation,[],[f70]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_0,plain,
% 2.14/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.14/0.97      inference(cnf_transformation,[],[f46]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_18,plain,
% 2.14/0.97      ( v3_pre_topc(X0,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ v2_pre_topc(X1)
% 2.14/0.97      | ~ l1_pre_topc(X1)
% 2.14/0.97      | ~ v1_xboole_0(X0) ),
% 2.14/0.97      inference(cnf_transformation,[],[f64]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_29,negated_conjecture,
% 2.14/0.97      ( v2_pre_topc(sK4) ),
% 2.14/0.97      inference(cnf_transformation,[],[f71]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_390,plain,
% 2.14/0.97      ( v3_pre_topc(X0,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ l1_pre_topc(X1)
% 2.14/0.97      | ~ v1_xboole_0(X0)
% 2.14/0.97      | sK4 != X1 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_391,plain,
% 2.14/0.97      ( v3_pre_topc(X0,sK4)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | ~ l1_pre_topc(sK4)
% 2.14/0.97      | ~ v1_xboole_0(X0) ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_390]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_395,plain,
% 2.14/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | v3_pre_topc(X0,sK4)
% 2.14/0.97      | ~ v1_xboole_0(X0) ),
% 2.14/0.97      inference(global_propositional_subsumption,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_391,c_28]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_396,plain,
% 2.14/0.97      ( v3_pre_topc(X0,sK4)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | ~ v1_xboole_0(X0) ),
% 2.14/0.97      inference(renaming,[status(thm)],[c_395]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_415,plain,
% 2.14/0.97      ( v3_pre_topc(X0,sK4)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | k1_xboole_0 != X0 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_396]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_416,plain,
% 2.14/0.97      ( v3_pre_topc(k1_xboole_0,sK4)
% 2.14/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_415]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_422,plain,
% 2.14/0.97      ( v3_pre_topc(k1_xboole_0,sK4) ),
% 2.14/0.97      inference(forward_subsumption_resolution,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_416,c_10]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_578,plain,
% 2.14/0.97      ( v2_tex_2(X0,X1)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.14/0.97      | ~ l1_pre_topc(X1)
% 2.14/0.97      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 2.14/0.97      | sK4 != X1
% 2.14/0.97      | k1_xboole_0 != X2 ),
% 2.14/0.97      inference(resolution_lifted,[status(thm)],[c_19,c_422]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_579,plain,
% 2.14/0.97      ( v2_tex_2(X0,sK4)
% 2.14/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | ~ l1_pre_topc(sK4)
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),X0,k1_xboole_0) != sK2(sK4,X0) ),
% 2.14/0.97      inference(unflattening,[status(thm)],[c_578]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(c_581,plain,
% 2.14/0.97      ( v2_tex_2(k1_xboole_0,sK4)
% 2.14/0.97      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.14/0.97      | ~ l1_pre_topc(sK4)
% 2.14/0.97      | k9_subset_1(u1_struct_0(sK4),k1_xboole_0,k1_xboole_0) != sK2(sK4,k1_xboole_0) ),
% 2.14/0.97      inference(instantiation,[status(thm)],[c_579]) ).
% 2.14/0.97  
% 2.14/0.97  cnf(contradiction,plain,
% 2.14/0.97      ( $false ),
% 2.14/0.97      inference(minisat,
% 2.14/0.97                [status(thm)],
% 2.14/0.97                [c_17459,c_8725,c_5771,c_2580,c_2457,c_2409,c_581,c_28]) ).
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.14/0.97  
% 2.14/0.97  ------                               Statistics
% 2.14/0.97  
% 2.14/0.97  ------ General
% 2.14/0.97  
% 2.14/0.97  abstr_ref_over_cycles:                  0
% 2.14/0.97  abstr_ref_under_cycles:                 0
% 2.14/0.97  gc_basic_clause_elim:                   0
% 2.14/0.97  forced_gc_time:                         0
% 2.14/0.97  parsing_time:                           0.009
% 2.14/0.97  unif_index_cands_time:                  0.
% 2.14/0.97  unif_index_add_time:                    0.
% 2.14/0.97  orderings_time:                         0.
% 2.14/0.97  out_proof_time:                         0.01
% 2.14/0.97  total_time:                             0.421
% 2.14/0.97  num_of_symbols:                         51
% 2.14/0.97  num_of_terms:                           12267
% 2.14/0.97  
% 2.14/0.97  ------ Preprocessing
% 2.14/0.97  
% 2.14/0.97  num_of_splits:                          0
% 2.14/0.97  num_of_split_atoms:                     0
% 2.14/0.97  num_of_reused_defs:                     0
% 2.14/0.97  num_eq_ax_congr_red:                    36
% 2.14/0.97  num_of_sem_filtered_clauses:            1
% 2.14/0.97  num_of_subtypes:                        0
% 2.14/0.97  monotx_restored_types:                  0
% 2.14/0.97  sat_num_of_epr_types:                   0
% 2.14/0.97  sat_num_of_non_cyclic_types:            0
% 2.14/0.97  sat_guarded_non_collapsed_types:        0
% 2.14/0.97  num_pure_diseq_elim:                    0
% 2.14/0.97  simp_replaced_by:                       0
% 2.14/0.97  res_preprocessed:                       132
% 2.14/0.97  prep_upred:                             0
% 2.14/0.97  prep_unflattend:                        41
% 2.14/0.97  smt_new_axioms:                         0
% 2.14/0.97  pred_elim_cands:                        4
% 2.14/0.97  pred_elim:                              4
% 2.14/0.97  pred_elim_cl:                           3
% 2.14/0.97  pred_elim_cycles:                       9
% 2.14/0.97  merged_defs:                            16
% 2.14/0.97  merged_defs_ncl:                        0
% 2.14/0.97  bin_hyper_res:                          18
% 2.14/0.97  prep_cycles:                            4
% 2.14/0.97  pred_elim_time:                         0.022
% 2.14/0.97  splitting_time:                         0.
% 2.14/0.97  sem_filter_time:                        0.
% 2.14/0.97  monotx_time:                            0.001
% 2.14/0.97  subtype_inf_time:                       0.
% 2.14/0.97  
% 2.14/0.97  ------ Problem properties
% 2.14/0.97  
% 2.14/0.97  clauses:                                26
% 2.14/0.97  conjectures:                            2
% 2.14/0.97  epr:                                    6
% 2.14/0.97  horn:                                   23
% 2.14/0.97  ground:                                 5
% 2.14/0.97  unary:                                  9
% 2.14/0.97  binary:                                 9
% 2.14/0.97  lits:                                   59
% 2.14/0.97  lits_eq:                                14
% 2.14/0.97  fd_pure:                                0
% 2.14/0.97  fd_pseudo:                              0
% 2.14/0.97  fd_cond:                                5
% 2.14/0.97  fd_pseudo_cond:                         1
% 2.14/0.97  ac_symbols:                             0
% 2.14/0.97  
% 2.14/0.97  ------ Propositional Solver
% 2.14/0.97  
% 2.14/0.97  prop_solver_calls:                      28
% 2.14/0.97  prop_fast_solver_calls:                 1516
% 2.14/0.97  smt_solver_calls:                       0
% 2.14/0.97  smt_fast_solver_calls:                  0
% 2.14/0.97  prop_num_of_clauses:                    5304
% 2.14/0.97  prop_preprocess_simplified:             13671
% 2.14/0.97  prop_fo_subsumed:                       21
% 2.14/0.97  prop_solver_time:                       0.
% 2.14/0.97  smt_solver_time:                        0.
% 2.14/0.97  smt_fast_solver_time:                   0.
% 2.14/0.97  prop_fast_solver_time:                  0.
% 2.14/0.97  prop_unsat_core_time:                   0.
% 2.14/0.97  
% 2.14/0.97  ------ QBF
% 2.14/0.97  
% 2.14/0.97  qbf_q_res:                              0
% 2.14/0.97  qbf_num_tautologies:                    0
% 2.14/0.97  qbf_prep_cycles:                        0
% 2.14/0.97  
% 2.14/0.97  ------ BMC1
% 2.14/0.97  
% 2.14/0.97  bmc1_current_bound:                     -1
% 2.14/0.97  bmc1_last_solved_bound:                 -1
% 2.14/0.97  bmc1_unsat_core_size:                   -1
% 2.14/0.97  bmc1_unsat_core_parents_size:           -1
% 2.14/0.97  bmc1_merge_next_fun:                    0
% 2.14/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.14/0.97  
% 2.14/0.97  ------ Instantiation
% 2.14/0.97  
% 2.14/0.97  inst_num_of_clauses:                    1426
% 2.14/0.97  inst_num_in_passive:                    805
% 2.14/0.97  inst_num_in_active:                     568
% 2.14/0.97  inst_num_in_unprocessed:                53
% 2.14/0.97  inst_num_of_loops:                      710
% 2.14/0.97  inst_num_of_learning_restarts:          0
% 2.14/0.97  inst_num_moves_active_passive:          139
% 2.14/0.97  inst_lit_activity:                      0
% 2.14/0.97  inst_lit_activity_moves:                0
% 2.14/0.97  inst_num_tautologies:                   0
% 2.14/0.97  inst_num_prop_implied:                  0
% 2.14/0.97  inst_num_existing_simplified:           0
% 2.14/0.97  inst_num_eq_res_simplified:             0
% 2.14/0.97  inst_num_child_elim:                    0
% 2.14/0.97  inst_num_of_dismatching_blockings:      699
% 2.14/0.97  inst_num_of_non_proper_insts:           1641
% 2.14/0.97  inst_num_of_duplicates:                 0
% 2.14/0.97  inst_inst_num_from_inst_to_res:         0
% 2.14/0.97  inst_dismatching_checking_time:         0.
% 2.14/0.97  
% 2.14/0.97  ------ Resolution
% 2.14/0.97  
% 2.14/0.97  res_num_of_clauses:                     0
% 2.14/0.97  res_num_in_passive:                     0
% 2.14/0.97  res_num_in_active:                      0
% 2.14/0.97  res_num_of_loops:                       136
% 2.14/0.97  res_forward_subset_subsumed:            151
% 2.14/0.97  res_backward_subset_subsumed:           6
% 2.14/0.97  res_forward_subsumed:                   0
% 2.14/0.97  res_backward_subsumed:                  0
% 2.14/0.97  res_forward_subsumption_resolution:     4
% 2.14/0.97  res_backward_subsumption_resolution:    0
% 2.14/0.97  res_clause_to_clause_subsumption:       2912
% 2.14/0.97  res_orphan_elimination:                 0
% 2.14/0.97  res_tautology_del:                      99
% 2.14/0.97  res_num_eq_res_simplified:              0
% 2.14/0.97  res_num_sel_changes:                    0
% 2.14/0.97  res_moves_from_active_to_pass:          0
% 2.14/0.97  
% 2.14/0.97  ------ Superposition
% 2.14/0.97  
% 2.14/0.97  sup_time_total:                         0.
% 2.14/0.97  sup_time_generating:                    0.
% 2.14/0.97  sup_time_sim_full:                      0.
% 2.14/0.97  sup_time_sim_immed:                     0.
% 2.14/0.97  
% 2.14/0.97  sup_num_of_clauses:                     330
% 2.14/0.97  sup_num_in_active:                      137
% 2.14/0.97  sup_num_in_passive:                     193
% 2.14/0.97  sup_num_of_loops:                       140
% 2.14/0.97  sup_fw_superposition:                   357
% 2.14/0.97  sup_bw_superposition:                   135
% 2.14/0.97  sup_immediate_simplified:               92
% 2.14/0.97  sup_given_eliminated:                   0
% 2.14/0.97  comparisons_done:                       0
% 2.14/0.97  comparisons_avoided:                    18
% 2.14/0.97  
% 2.14/0.97  ------ Simplifications
% 2.14/0.97  
% 2.14/0.97  
% 2.14/0.97  sim_fw_subset_subsumed:                 20
% 2.14/0.97  sim_bw_subset_subsumed:                 7
% 2.14/0.97  sim_fw_subsumed:                        30
% 2.14/0.97  sim_bw_subsumed:                        0
% 2.14/0.97  sim_fw_subsumption_res:                 5
% 2.14/0.97  sim_bw_subsumption_res:                 0
% 2.14/0.97  sim_tautology_del:                      39
% 2.14/0.97  sim_eq_tautology_del:                   35
% 2.14/0.97  sim_eq_res_simp:                        0
% 2.14/0.97  sim_fw_demodulated:                     24
% 2.14/0.97  sim_bw_demodulated:                     2
% 2.14/0.97  sim_light_normalised:                   43
% 2.14/0.97  sim_joinable_taut:                      0
% 2.14/0.97  sim_joinable_simp:                      0
% 2.14/0.97  sim_ac_normalised:                      0
% 2.14/0.97  sim_smt_subsumption:                    0
% 2.14/0.97  
%------------------------------------------------------------------------------
