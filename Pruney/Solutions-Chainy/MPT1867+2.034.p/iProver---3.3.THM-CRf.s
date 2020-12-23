%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:12 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 307 expanded)
%              Number of clauses        :   69 (  93 expanded)
%              Number of leaves         :   21 (  73 expanded)
%              Depth                    :   16
%              Number of atoms          :  416 (1275 expanded)
%              Number of equality atoms :  109 ( 160 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
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

fof(f46,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f45,f44])).

fof(f73,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f46])).

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
                            & v4_pre_topc(X3,X0) ) )
                    & r1_tarski(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v4_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v4_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v4_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
            | ~ v4_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
                    | ~ v4_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
                    & v4_pre_topc(sK3(X0,X1,X4),X0)
                    & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f57,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f61,f59])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f59,f59])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v4_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_25,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1976,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1984,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3214,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1976,c_1984])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1977,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_18,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_544,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_545,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_544])).

cnf(c_1970,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_545])).

cnf(c_2310,plain,
    ( v2_tex_2(sK5,sK4) = iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1977,c_1970])).

cnf(c_31,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_890,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0)
    | sK4 != sK4
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_545])).

cnf(c_891,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,sK5),sK5) ),
    inference(unflattening,[status(thm)],[c_890])).

cnf(c_892,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_891])).

cnf(c_2686,plain,
    ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2310,c_31,c_892])).

cnf(c_3285,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3214,c_2686])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1987,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_15,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1979,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3066,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1977,c_1979])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_374,plain,
    ( ~ r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_25])).

cnf(c_375,plain,
    ( ~ r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_376,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_375])).

cnf(c_3400,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3066,c_376])).

cnf(c_3404,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3400,c_3214])).

cnf(c_3711,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1987,c_3404])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1983,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4461,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3711,c_1983])).

cnf(c_5188,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3285,c_4461])).

cnf(c_14,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1980,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1981,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4350,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1980,c_1981])).

cnf(c_11,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_12,plain,
    ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2410,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_0,c_12])).

cnf(c_2413,plain,
    ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2410,c_11])).

cnf(c_4370,plain,
    ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4350,c_11,c_2413])).

cnf(c_17,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_559,plain,
    ( v2_tex_2(X0,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_560,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v4_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_559])).

cnf(c_1969,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
    | v2_tex_2(X0,sK4) = iProver_top
    | v4_pre_topc(X1,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_560])).

cnf(c_4378,plain,
    ( sK2(sK4,X0) != k1_xboole_0
    | v2_tex_2(X0,sK4) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4370,c_1969])).

cnf(c_4380,plain,
    ( sK2(sK4,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4378])).

cnf(c_1978,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3288,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3214,c_1978])).

cnf(c_2172,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2176,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2172])).

cnf(c_16,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_275,plain,
    ( v4_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_276,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | v4_pre_topc(X0,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_276,c_26])).

cnf(c_281,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_280])).

cnf(c_6,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_337,plain,
    ( v4_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_281,c_6])).

cnf(c_338,plain,
    ( v4_pre_topc(k1_xboole_0,sK4)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(unflattening,[status(thm)],[c_337])).

cnf(c_344,plain,
    ( v4_pre_topc(k1_xboole_0,sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_338,c_14])).

cnf(c_346,plain,
    ( v4_pre_topc(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5188,c_4380,c_3288,c_2176,c_346])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:17:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.21/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/0.99  
% 2.21/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/0.99  
% 2.21/0.99  ------  iProver source info
% 2.21/0.99  
% 2.21/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.21/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/0.99  git: non_committed_changes: false
% 2.21/0.99  git: last_make_outside_of_git: false
% 2.21/0.99  
% 2.21/0.99  ------ 
% 2.21/0.99  
% 2.21/0.99  ------ Input Options
% 2.21/0.99  
% 2.21/0.99  --out_options                           all
% 2.21/0.99  --tptp_safe_out                         true
% 2.21/0.99  --problem_path                          ""
% 2.21/0.99  --include_path                          ""
% 2.21/0.99  --clausifier                            res/vclausify_rel
% 2.21/0.99  --clausifier_options                    --mode clausify
% 2.21/0.99  --stdin                                 false
% 2.21/0.99  --stats_out                             all
% 2.21/0.99  
% 2.21/0.99  ------ General Options
% 2.21/0.99  
% 2.21/0.99  --fof                                   false
% 2.21/0.99  --time_out_real                         305.
% 2.21/0.99  --time_out_virtual                      -1.
% 2.21/0.99  --symbol_type_check                     false
% 2.21/0.99  --clausify_out                          false
% 2.21/0.99  --sig_cnt_out                           false
% 2.21/0.99  --trig_cnt_out                          false
% 2.21/0.99  --trig_cnt_out_tolerance                1.
% 2.21/0.99  --trig_cnt_out_sk_spl                   false
% 2.21/0.99  --abstr_cl_out                          false
% 2.21/0.99  
% 2.21/0.99  ------ Global Options
% 2.21/0.99  
% 2.21/0.99  --schedule                              default
% 2.21/0.99  --add_important_lit                     false
% 2.21/0.99  --prop_solver_per_cl                    1000
% 2.21/0.99  --min_unsat_core                        false
% 2.21/0.99  --soft_assumptions                      false
% 2.21/0.99  --soft_lemma_size                       3
% 2.21/0.99  --prop_impl_unit_size                   0
% 2.21/0.99  --prop_impl_unit                        []
% 2.21/0.99  --share_sel_clauses                     true
% 2.21/0.99  --reset_solvers                         false
% 2.21/0.99  --bc_imp_inh                            [conj_cone]
% 2.21/0.99  --conj_cone_tolerance                   3.
% 2.21/0.99  --extra_neg_conj                        none
% 2.21/0.99  --large_theory_mode                     true
% 2.21/0.99  --prolific_symb_bound                   200
% 2.21/0.99  --lt_threshold                          2000
% 2.21/0.99  --clause_weak_htbl                      true
% 2.21/0.99  --gc_record_bc_elim                     false
% 2.21/0.99  
% 2.21/0.99  ------ Preprocessing Options
% 2.21/0.99  
% 2.21/0.99  --preprocessing_flag                    true
% 2.21/0.99  --time_out_prep_mult                    0.1
% 2.21/0.99  --splitting_mode                        input
% 2.21/0.99  --splitting_grd                         true
% 2.21/0.99  --splitting_cvd                         false
% 2.21/0.99  --splitting_cvd_svl                     false
% 2.21/0.99  --splitting_nvd                         32
% 2.21/0.99  --sub_typing                            true
% 2.21/0.99  --prep_gs_sim                           true
% 2.21/0.99  --prep_unflatten                        true
% 2.21/0.99  --prep_res_sim                          true
% 2.21/0.99  --prep_upred                            true
% 2.21/0.99  --prep_sem_filter                       exhaustive
% 2.21/0.99  --prep_sem_filter_out                   false
% 2.21/0.99  --pred_elim                             true
% 2.21/0.99  --res_sim_input                         true
% 2.21/0.99  --eq_ax_congr_red                       true
% 2.21/0.99  --pure_diseq_elim                       true
% 2.21/0.99  --brand_transform                       false
% 2.21/0.99  --non_eq_to_eq                          false
% 2.21/0.99  --prep_def_merge                        true
% 2.21/0.99  --prep_def_merge_prop_impl              false
% 2.21/0.99  --prep_def_merge_mbd                    true
% 2.21/0.99  --prep_def_merge_tr_red                 false
% 2.21/0.99  --prep_def_merge_tr_cl                  false
% 2.21/0.99  --smt_preprocessing                     true
% 2.21/0.99  --smt_ac_axioms                         fast
% 2.21/0.99  --preprocessed_out                      false
% 2.21/0.99  --preprocessed_stats                    false
% 2.21/0.99  
% 2.21/0.99  ------ Abstraction refinement Options
% 2.21/0.99  
% 2.21/0.99  --abstr_ref                             []
% 2.21/0.99  --abstr_ref_prep                        false
% 2.21/0.99  --abstr_ref_until_sat                   false
% 2.21/0.99  --abstr_ref_sig_restrict                funpre
% 2.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.99  --abstr_ref_under                       []
% 2.21/0.99  
% 2.21/0.99  ------ SAT Options
% 2.21/0.99  
% 2.21/0.99  --sat_mode                              false
% 2.21/0.99  --sat_fm_restart_options                ""
% 2.21/0.99  --sat_gr_def                            false
% 2.21/0.99  --sat_epr_types                         true
% 2.21/0.99  --sat_non_cyclic_types                  false
% 2.21/0.99  --sat_finite_models                     false
% 2.21/0.99  --sat_fm_lemmas                         false
% 2.21/0.99  --sat_fm_prep                           false
% 2.21/0.99  --sat_fm_uc_incr                        true
% 2.21/0.99  --sat_out_model                         small
% 2.21/0.99  --sat_out_clauses                       false
% 2.21/0.99  
% 2.21/0.99  ------ QBF Options
% 2.21/0.99  
% 2.21/0.99  --qbf_mode                              false
% 2.21/0.99  --qbf_elim_univ                         false
% 2.21/0.99  --qbf_dom_inst                          none
% 2.21/0.99  --qbf_dom_pre_inst                      false
% 2.21/0.99  --qbf_sk_in                             false
% 2.21/0.99  --qbf_pred_elim                         true
% 2.21/0.99  --qbf_split                             512
% 2.21/0.99  
% 2.21/0.99  ------ BMC1 Options
% 2.21/0.99  
% 2.21/0.99  --bmc1_incremental                      false
% 2.21/0.99  --bmc1_axioms                           reachable_all
% 2.21/0.99  --bmc1_min_bound                        0
% 2.21/0.99  --bmc1_max_bound                        -1
% 2.21/0.99  --bmc1_max_bound_default                -1
% 2.21/0.99  --bmc1_symbol_reachability              true
% 2.21/0.99  --bmc1_property_lemmas                  false
% 2.21/0.99  --bmc1_k_induction                      false
% 2.21/0.99  --bmc1_non_equiv_states                 false
% 2.21/0.99  --bmc1_deadlock                         false
% 2.21/0.99  --bmc1_ucm                              false
% 2.21/0.99  --bmc1_add_unsat_core                   none
% 2.21/0.99  --bmc1_unsat_core_children              false
% 2.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.99  --bmc1_out_stat                         full
% 2.21/0.99  --bmc1_ground_init                      false
% 2.21/0.99  --bmc1_pre_inst_next_state              false
% 2.21/0.99  --bmc1_pre_inst_state                   false
% 2.21/0.99  --bmc1_pre_inst_reach_state             false
% 2.21/0.99  --bmc1_out_unsat_core                   false
% 2.21/0.99  --bmc1_aig_witness_out                  false
% 2.21/0.99  --bmc1_verbose                          false
% 2.21/0.99  --bmc1_dump_clauses_tptp                false
% 2.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.99  --bmc1_dump_file                        -
% 2.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.99  --bmc1_ucm_extend_mode                  1
% 2.21/0.99  --bmc1_ucm_init_mode                    2
% 2.21/0.99  --bmc1_ucm_cone_mode                    none
% 2.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.99  --bmc1_ucm_relax_model                  4
% 2.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.99  --bmc1_ucm_layered_model                none
% 2.21/0.99  --bmc1_ucm_max_lemma_size               10
% 2.21/0.99  
% 2.21/0.99  ------ AIG Options
% 2.21/0.99  
% 2.21/0.99  --aig_mode                              false
% 2.21/0.99  
% 2.21/0.99  ------ Instantiation Options
% 2.21/0.99  
% 2.21/0.99  --instantiation_flag                    true
% 2.21/0.99  --inst_sos_flag                         false
% 2.21/0.99  --inst_sos_phase                        true
% 2.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.99  --inst_lit_sel_side                     num_symb
% 2.21/0.99  --inst_solver_per_active                1400
% 2.21/0.99  --inst_solver_calls_frac                1.
% 2.21/0.99  --inst_passive_queue_type               priority_queues
% 2.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.99  --inst_passive_queues_freq              [25;2]
% 2.21/0.99  --inst_dismatching                      true
% 2.21/0.99  --inst_eager_unprocessed_to_passive     true
% 2.21/0.99  --inst_prop_sim_given                   true
% 2.21/0.99  --inst_prop_sim_new                     false
% 2.21/0.99  --inst_subs_new                         false
% 2.21/0.99  --inst_eq_res_simp                      false
% 2.21/0.99  --inst_subs_given                       false
% 2.21/0.99  --inst_orphan_elimination               true
% 2.21/0.99  --inst_learning_loop_flag               true
% 2.21/0.99  --inst_learning_start                   3000
% 2.21/0.99  --inst_learning_factor                  2
% 2.21/0.99  --inst_start_prop_sim_after_learn       3
% 2.21/0.99  --inst_sel_renew                        solver
% 2.21/0.99  --inst_lit_activity_flag                true
% 2.21/0.99  --inst_restr_to_given                   false
% 2.21/0.99  --inst_activity_threshold               500
% 2.21/0.99  --inst_out_proof                        true
% 2.21/0.99  
% 2.21/0.99  ------ Resolution Options
% 2.21/0.99  
% 2.21/0.99  --resolution_flag                       true
% 2.21/0.99  --res_lit_sel                           adaptive
% 2.21/0.99  --res_lit_sel_side                      none
% 2.21/0.99  --res_ordering                          kbo
% 2.21/0.99  --res_to_prop_solver                    active
% 2.21/0.99  --res_prop_simpl_new                    false
% 2.21/0.99  --res_prop_simpl_given                  true
% 2.21/0.99  --res_passive_queue_type                priority_queues
% 2.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.99  --res_passive_queues_freq               [15;5]
% 2.21/0.99  --res_forward_subs                      full
% 2.21/0.99  --res_backward_subs                     full
% 2.21/0.99  --res_forward_subs_resolution           true
% 2.21/0.99  --res_backward_subs_resolution          true
% 2.21/0.99  --res_orphan_elimination                true
% 2.21/0.99  --res_time_limit                        2.
% 2.21/0.99  --res_out_proof                         true
% 2.21/0.99  
% 2.21/0.99  ------ Superposition Options
% 2.21/0.99  
% 2.21/0.99  --superposition_flag                    true
% 2.21/0.99  --sup_passive_queue_type                priority_queues
% 2.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.99  --demod_completeness_check              fast
% 2.21/0.99  --demod_use_ground                      true
% 2.21/0.99  --sup_to_prop_solver                    passive
% 2.21/0.99  --sup_prop_simpl_new                    true
% 2.21/0.99  --sup_prop_simpl_given                  true
% 2.21/0.99  --sup_fun_splitting                     false
% 2.21/0.99  --sup_smt_interval                      50000
% 2.21/0.99  
% 2.21/0.99  ------ Superposition Simplification Setup
% 2.21/0.99  
% 2.21/0.99  --sup_indices_passive                   []
% 2.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_full_bw                           [BwDemod]
% 2.21/0.99  --sup_immed_triv                        [TrivRules]
% 2.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_immed_bw_main                     []
% 2.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.99  
% 2.21/0.99  ------ Combination Options
% 2.21/0.99  
% 2.21/0.99  --comb_res_mult                         3
% 2.21/0.99  --comb_sup_mult                         2
% 2.21/0.99  --comb_inst_mult                        10
% 2.21/0.99  
% 2.21/0.99  ------ Debug Options
% 2.21/0.99  
% 2.21/0.99  --dbg_backtrace                         false
% 2.21/0.99  --dbg_dump_prop_clauses                 false
% 2.21/0.99  --dbg_dump_prop_clauses_file            -
% 2.21/0.99  --dbg_out_stat                          false
% 2.21/0.99  ------ Parsing...
% 2.21/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/0.99  
% 2.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.21/0.99  
% 2.21/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/0.99  
% 2.21/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/0.99  ------ Proving...
% 2.21/0.99  ------ Problem Properties 
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  clauses                                 25
% 2.21/0.99  conjectures                             3
% 2.21/0.99  EPR                                     8
% 2.21/0.99  Horn                                    21
% 2.21/0.99  unary                                   9
% 2.21/0.99  binary                                  6
% 2.21/0.99  lits                                    59
% 2.21/0.99  lits eq                                 8
% 2.21/0.99  fd_pure                                 0
% 2.21/0.99  fd_pseudo                               0
% 2.21/0.99  fd_cond                                 1
% 2.21/0.99  fd_pseudo_cond                          1
% 2.21/0.99  AC symbols                              0
% 2.21/0.99  
% 2.21/0.99  ------ Schedule dynamic 5 is on 
% 2.21/0.99  
% 2.21/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  ------ 
% 2.21/0.99  Current options:
% 2.21/0.99  ------ 
% 2.21/0.99  
% 2.21/0.99  ------ Input Options
% 2.21/0.99  
% 2.21/0.99  --out_options                           all
% 2.21/0.99  --tptp_safe_out                         true
% 2.21/0.99  --problem_path                          ""
% 2.21/0.99  --include_path                          ""
% 2.21/0.99  --clausifier                            res/vclausify_rel
% 2.21/0.99  --clausifier_options                    --mode clausify
% 2.21/0.99  --stdin                                 false
% 2.21/0.99  --stats_out                             all
% 2.21/0.99  
% 2.21/0.99  ------ General Options
% 2.21/0.99  
% 2.21/0.99  --fof                                   false
% 2.21/0.99  --time_out_real                         305.
% 2.21/0.99  --time_out_virtual                      -1.
% 2.21/0.99  --symbol_type_check                     false
% 2.21/0.99  --clausify_out                          false
% 2.21/0.99  --sig_cnt_out                           false
% 2.21/0.99  --trig_cnt_out                          false
% 2.21/0.99  --trig_cnt_out_tolerance                1.
% 2.21/0.99  --trig_cnt_out_sk_spl                   false
% 2.21/0.99  --abstr_cl_out                          false
% 2.21/0.99  
% 2.21/0.99  ------ Global Options
% 2.21/0.99  
% 2.21/0.99  --schedule                              default
% 2.21/0.99  --add_important_lit                     false
% 2.21/0.99  --prop_solver_per_cl                    1000
% 2.21/0.99  --min_unsat_core                        false
% 2.21/0.99  --soft_assumptions                      false
% 2.21/0.99  --soft_lemma_size                       3
% 2.21/0.99  --prop_impl_unit_size                   0
% 2.21/0.99  --prop_impl_unit                        []
% 2.21/0.99  --share_sel_clauses                     true
% 2.21/0.99  --reset_solvers                         false
% 2.21/0.99  --bc_imp_inh                            [conj_cone]
% 2.21/0.99  --conj_cone_tolerance                   3.
% 2.21/0.99  --extra_neg_conj                        none
% 2.21/0.99  --large_theory_mode                     true
% 2.21/0.99  --prolific_symb_bound                   200
% 2.21/0.99  --lt_threshold                          2000
% 2.21/0.99  --clause_weak_htbl                      true
% 2.21/0.99  --gc_record_bc_elim                     false
% 2.21/0.99  
% 2.21/0.99  ------ Preprocessing Options
% 2.21/0.99  
% 2.21/0.99  --preprocessing_flag                    true
% 2.21/0.99  --time_out_prep_mult                    0.1
% 2.21/0.99  --splitting_mode                        input
% 2.21/0.99  --splitting_grd                         true
% 2.21/0.99  --splitting_cvd                         false
% 2.21/0.99  --splitting_cvd_svl                     false
% 2.21/0.99  --splitting_nvd                         32
% 2.21/0.99  --sub_typing                            true
% 2.21/0.99  --prep_gs_sim                           true
% 2.21/0.99  --prep_unflatten                        true
% 2.21/0.99  --prep_res_sim                          true
% 2.21/0.99  --prep_upred                            true
% 2.21/0.99  --prep_sem_filter                       exhaustive
% 2.21/0.99  --prep_sem_filter_out                   false
% 2.21/0.99  --pred_elim                             true
% 2.21/0.99  --res_sim_input                         true
% 2.21/0.99  --eq_ax_congr_red                       true
% 2.21/0.99  --pure_diseq_elim                       true
% 2.21/0.99  --brand_transform                       false
% 2.21/0.99  --non_eq_to_eq                          false
% 2.21/0.99  --prep_def_merge                        true
% 2.21/0.99  --prep_def_merge_prop_impl              false
% 2.21/0.99  --prep_def_merge_mbd                    true
% 2.21/0.99  --prep_def_merge_tr_red                 false
% 2.21/0.99  --prep_def_merge_tr_cl                  false
% 2.21/0.99  --smt_preprocessing                     true
% 2.21/0.99  --smt_ac_axioms                         fast
% 2.21/0.99  --preprocessed_out                      false
% 2.21/0.99  --preprocessed_stats                    false
% 2.21/0.99  
% 2.21/0.99  ------ Abstraction refinement Options
% 2.21/0.99  
% 2.21/0.99  --abstr_ref                             []
% 2.21/0.99  --abstr_ref_prep                        false
% 2.21/0.99  --abstr_ref_until_sat                   false
% 2.21/0.99  --abstr_ref_sig_restrict                funpre
% 2.21/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/0.99  --abstr_ref_under                       []
% 2.21/0.99  
% 2.21/0.99  ------ SAT Options
% 2.21/0.99  
% 2.21/0.99  --sat_mode                              false
% 2.21/0.99  --sat_fm_restart_options                ""
% 2.21/0.99  --sat_gr_def                            false
% 2.21/0.99  --sat_epr_types                         true
% 2.21/0.99  --sat_non_cyclic_types                  false
% 2.21/0.99  --sat_finite_models                     false
% 2.21/0.99  --sat_fm_lemmas                         false
% 2.21/0.99  --sat_fm_prep                           false
% 2.21/0.99  --sat_fm_uc_incr                        true
% 2.21/0.99  --sat_out_model                         small
% 2.21/0.99  --sat_out_clauses                       false
% 2.21/0.99  
% 2.21/0.99  ------ QBF Options
% 2.21/0.99  
% 2.21/0.99  --qbf_mode                              false
% 2.21/0.99  --qbf_elim_univ                         false
% 2.21/0.99  --qbf_dom_inst                          none
% 2.21/0.99  --qbf_dom_pre_inst                      false
% 2.21/0.99  --qbf_sk_in                             false
% 2.21/0.99  --qbf_pred_elim                         true
% 2.21/0.99  --qbf_split                             512
% 2.21/0.99  
% 2.21/0.99  ------ BMC1 Options
% 2.21/0.99  
% 2.21/0.99  --bmc1_incremental                      false
% 2.21/0.99  --bmc1_axioms                           reachable_all
% 2.21/0.99  --bmc1_min_bound                        0
% 2.21/0.99  --bmc1_max_bound                        -1
% 2.21/0.99  --bmc1_max_bound_default                -1
% 2.21/0.99  --bmc1_symbol_reachability              true
% 2.21/0.99  --bmc1_property_lemmas                  false
% 2.21/0.99  --bmc1_k_induction                      false
% 2.21/0.99  --bmc1_non_equiv_states                 false
% 2.21/0.99  --bmc1_deadlock                         false
% 2.21/0.99  --bmc1_ucm                              false
% 2.21/0.99  --bmc1_add_unsat_core                   none
% 2.21/0.99  --bmc1_unsat_core_children              false
% 2.21/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/0.99  --bmc1_out_stat                         full
% 2.21/0.99  --bmc1_ground_init                      false
% 2.21/0.99  --bmc1_pre_inst_next_state              false
% 2.21/0.99  --bmc1_pre_inst_state                   false
% 2.21/0.99  --bmc1_pre_inst_reach_state             false
% 2.21/0.99  --bmc1_out_unsat_core                   false
% 2.21/0.99  --bmc1_aig_witness_out                  false
% 2.21/0.99  --bmc1_verbose                          false
% 2.21/0.99  --bmc1_dump_clauses_tptp                false
% 2.21/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.21/0.99  --bmc1_dump_file                        -
% 2.21/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.21/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.21/0.99  --bmc1_ucm_extend_mode                  1
% 2.21/0.99  --bmc1_ucm_init_mode                    2
% 2.21/0.99  --bmc1_ucm_cone_mode                    none
% 2.21/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.21/0.99  --bmc1_ucm_relax_model                  4
% 2.21/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.21/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/0.99  --bmc1_ucm_layered_model                none
% 2.21/0.99  --bmc1_ucm_max_lemma_size               10
% 2.21/0.99  
% 2.21/0.99  ------ AIG Options
% 2.21/0.99  
% 2.21/0.99  --aig_mode                              false
% 2.21/0.99  
% 2.21/0.99  ------ Instantiation Options
% 2.21/0.99  
% 2.21/0.99  --instantiation_flag                    true
% 2.21/0.99  --inst_sos_flag                         false
% 2.21/0.99  --inst_sos_phase                        true
% 2.21/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/0.99  --inst_lit_sel_side                     none
% 2.21/0.99  --inst_solver_per_active                1400
% 2.21/0.99  --inst_solver_calls_frac                1.
% 2.21/0.99  --inst_passive_queue_type               priority_queues
% 2.21/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/0.99  --inst_passive_queues_freq              [25;2]
% 2.21/0.99  --inst_dismatching                      true
% 2.21/0.99  --inst_eager_unprocessed_to_passive     true
% 2.21/0.99  --inst_prop_sim_given                   true
% 2.21/0.99  --inst_prop_sim_new                     false
% 2.21/0.99  --inst_subs_new                         false
% 2.21/0.99  --inst_eq_res_simp                      false
% 2.21/0.99  --inst_subs_given                       false
% 2.21/0.99  --inst_orphan_elimination               true
% 2.21/0.99  --inst_learning_loop_flag               true
% 2.21/0.99  --inst_learning_start                   3000
% 2.21/0.99  --inst_learning_factor                  2
% 2.21/0.99  --inst_start_prop_sim_after_learn       3
% 2.21/0.99  --inst_sel_renew                        solver
% 2.21/0.99  --inst_lit_activity_flag                true
% 2.21/0.99  --inst_restr_to_given                   false
% 2.21/0.99  --inst_activity_threshold               500
% 2.21/0.99  --inst_out_proof                        true
% 2.21/0.99  
% 2.21/0.99  ------ Resolution Options
% 2.21/0.99  
% 2.21/0.99  --resolution_flag                       false
% 2.21/0.99  --res_lit_sel                           adaptive
% 2.21/0.99  --res_lit_sel_side                      none
% 2.21/0.99  --res_ordering                          kbo
% 2.21/0.99  --res_to_prop_solver                    active
% 2.21/0.99  --res_prop_simpl_new                    false
% 2.21/0.99  --res_prop_simpl_given                  true
% 2.21/0.99  --res_passive_queue_type                priority_queues
% 2.21/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/0.99  --res_passive_queues_freq               [15;5]
% 2.21/0.99  --res_forward_subs                      full
% 2.21/0.99  --res_backward_subs                     full
% 2.21/0.99  --res_forward_subs_resolution           true
% 2.21/0.99  --res_backward_subs_resolution          true
% 2.21/0.99  --res_orphan_elimination                true
% 2.21/0.99  --res_time_limit                        2.
% 2.21/0.99  --res_out_proof                         true
% 2.21/0.99  
% 2.21/0.99  ------ Superposition Options
% 2.21/0.99  
% 2.21/0.99  --superposition_flag                    true
% 2.21/0.99  --sup_passive_queue_type                priority_queues
% 2.21/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.21/0.99  --demod_completeness_check              fast
% 2.21/0.99  --demod_use_ground                      true
% 2.21/0.99  --sup_to_prop_solver                    passive
% 2.21/0.99  --sup_prop_simpl_new                    true
% 2.21/0.99  --sup_prop_simpl_given                  true
% 2.21/0.99  --sup_fun_splitting                     false
% 2.21/0.99  --sup_smt_interval                      50000
% 2.21/0.99  
% 2.21/0.99  ------ Superposition Simplification Setup
% 2.21/0.99  
% 2.21/0.99  --sup_indices_passive                   []
% 2.21/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_full_bw                           [BwDemod]
% 2.21/0.99  --sup_immed_triv                        [TrivRules]
% 2.21/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_immed_bw_main                     []
% 2.21/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/0.99  
% 2.21/0.99  ------ Combination Options
% 2.21/0.99  
% 2.21/0.99  --comb_res_mult                         3
% 2.21/0.99  --comb_sup_mult                         2
% 2.21/0.99  --comb_inst_mult                        10
% 2.21/0.99  
% 2.21/0.99  ------ Debug Options
% 2.21/0.99  
% 2.21/0.99  --dbg_backtrace                         false
% 2.21/0.99  --dbg_dump_prop_clauses                 false
% 2.21/0.99  --dbg_dump_prop_clauses_file            -
% 2.21/0.99  --dbg_out_stat                          false
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  ------ Proving...
% 2.21/0.99  
% 2.21/0.99  
% 2.21/0.99  % SZS status Theorem for theBenchmark.p
% 2.21/0.99  
% 2.21/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/0.99  
% 2.21/0.99  fof(f15,conjecture,(
% 2.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f16,negated_conjecture,(
% 2.21/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.21/0.99    inference(negated_conjecture,[],[f15])).
% 2.21/0.99  
% 2.21/0.99  fof(f17,plain,(
% 2.21/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.21/0.99    inference(pure_predicate_removal,[],[f16])).
% 2.21/0.99  
% 2.21/0.99  fof(f27,plain,(
% 2.21/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.21/0.99    inference(ennf_transformation,[],[f17])).
% 2.21/0.99  
% 2.21/0.99  fof(f28,plain,(
% 2.21/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.21/0.99    inference(flattening,[],[f27])).
% 2.21/0.99  
% 2.21/0.99  fof(f45,plain,(
% 2.21/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f44,plain,(
% 2.21/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f46,plain,(
% 2.21/0.99    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f45,f44])).
% 2.21/0.99  
% 2.21/0.99  fof(f73,plain,(
% 2.21/0.99    v1_xboole_0(sK5)),
% 2.21/0.99    inference(cnf_transformation,[],[f46])).
% 2.21/0.99  
% 2.21/0.99  fof(f5,axiom,(
% 2.21/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f19,plain,(
% 2.21/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.21/0.99    inference(ennf_transformation,[],[f5])).
% 2.21/0.99  
% 2.21/0.99  fof(f54,plain,(
% 2.21/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f19])).
% 2.21/0.99  
% 2.21/0.99  fof(f74,plain,(
% 2.21/0.99    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.21/0.99    inference(cnf_transformation,[],[f46])).
% 2.21/0.99  
% 2.21/0.99  fof(f14,axiom,(
% 2.21/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f25,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.99    inference(ennf_transformation,[],[f14])).
% 2.21/0.99  
% 2.21/0.99  fof(f26,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.99    inference(flattening,[],[f25])).
% 2.21/0.99  
% 2.21/0.99  fof(f39,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.99    inference(nnf_transformation,[],[f26])).
% 2.21/0.99  
% 2.21/0.99  fof(f40,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.99    inference(rectify,[],[f39])).
% 2.21/0.99  
% 2.21/0.99  fof(f42,plain,(
% 2.21/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v4_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f41,plain,(
% 2.21/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f43,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v4_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f40,f42,f41])).
% 2.21/0.99  
% 2.21/0.99  fof(f69,plain,(
% 2.21/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f43])).
% 2.21/0.99  
% 2.21/0.99  fof(f72,plain,(
% 2.21/0.99    l1_pre_topc(sK4)),
% 2.21/0.99    inference(cnf_transformation,[],[f46])).
% 2.21/0.99  
% 2.21/0.99  fof(f75,plain,(
% 2.21/0.99    ~v2_tex_2(sK5,sK4)),
% 2.21/0.99    inference(cnf_transformation,[],[f46])).
% 2.21/0.99  
% 2.21/0.99  fof(f3,axiom,(
% 2.21/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f18,plain,(
% 2.21/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.21/0.99    inference(ennf_transformation,[],[f3])).
% 2.21/0.99  
% 2.21/0.99  fof(f33,plain,(
% 2.21/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.99    inference(nnf_transformation,[],[f18])).
% 2.21/0.99  
% 2.21/0.99  fof(f34,plain,(
% 2.21/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.99    inference(rectify,[],[f33])).
% 2.21/0.99  
% 2.21/0.99  fof(f35,plain,(
% 2.21/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f36,plain,(
% 2.21/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f34,f35])).
% 2.21/0.99  
% 2.21/0.99  fof(f51,plain,(
% 2.21/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f36])).
% 2.21/0.99  
% 2.21/0.99  fof(f12,axiom,(
% 2.21/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f21,plain,(
% 2.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.21/0.99    inference(ennf_transformation,[],[f12])).
% 2.21/0.99  
% 2.21/0.99  fof(f22,plain,(
% 2.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.21/0.99    inference(flattening,[],[f21])).
% 2.21/0.99  
% 2.21/0.99  fof(f63,plain,(
% 2.21/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f22])).
% 2.21/0.99  
% 2.21/0.99  fof(f2,axiom,(
% 2.21/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f29,plain,(
% 2.21/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.21/0.99    inference(nnf_transformation,[],[f2])).
% 2.21/0.99  
% 2.21/0.99  fof(f30,plain,(
% 2.21/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.21/0.99    inference(rectify,[],[f29])).
% 2.21/0.99  
% 2.21/0.99  fof(f31,plain,(
% 2.21/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.21/0.99    introduced(choice_axiom,[])).
% 2.21/0.99  
% 2.21/0.99  fof(f32,plain,(
% 2.21/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.21/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.21/0.99  
% 2.21/0.99  fof(f48,plain,(
% 2.21/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f32])).
% 2.21/0.99  
% 2.21/0.99  fof(f6,axiom,(
% 2.21/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f37,plain,(
% 2.21/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.99    inference(nnf_transformation,[],[f6])).
% 2.21/0.99  
% 2.21/0.99  fof(f38,plain,(
% 2.21/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/0.99    inference(flattening,[],[f37])).
% 2.21/0.99  
% 2.21/0.99  fof(f57,plain,(
% 2.21/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f38])).
% 2.21/0.99  
% 2.21/0.99  fof(f11,axiom,(
% 2.21/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f62,plain,(
% 2.21/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.21/0.99    inference(cnf_transformation,[],[f11])).
% 2.21/0.99  
% 2.21/0.99  fof(f10,axiom,(
% 2.21/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f20,plain,(
% 2.21/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.21/0.99    inference(ennf_transformation,[],[f10])).
% 2.21/0.99  
% 2.21/0.99  fof(f61,plain,(
% 2.21/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.21/0.99    inference(cnf_transformation,[],[f20])).
% 2.21/0.99  
% 2.21/0.99  fof(f8,axiom,(
% 2.21/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f59,plain,(
% 2.21/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.21/0.99    inference(cnf_transformation,[],[f8])).
% 2.21/0.99  
% 2.21/0.99  fof(f77,plain,(
% 2.21/0.99    ( ! [X2,X0,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.21/0.99    inference(definition_unfolding,[],[f61,f59])).
% 2.21/0.99  
% 2.21/0.99  fof(f7,axiom,(
% 2.21/0.99    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f58,plain,(
% 2.21/0.99    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.21/0.99    inference(cnf_transformation,[],[f7])).
% 2.21/0.99  
% 2.21/0.99  fof(f1,axiom,(
% 2.21/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f47,plain,(
% 2.21/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f1])).
% 2.21/0.99  
% 2.21/0.99  fof(f76,plain,(
% 2.21/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 2.21/0.99    inference(definition_unfolding,[],[f47,f59,f59])).
% 2.21/0.99  
% 2.21/0.99  fof(f9,axiom,(
% 2.21/0.99    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f60,plain,(
% 2.21/0.99    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f9])).
% 2.21/0.99  
% 2.21/0.99  fof(f70,plain,(
% 2.21/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v4_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f43])).
% 2.21/0.99  
% 2.21/0.99  fof(f13,axiom,(
% 2.21/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f23,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.21/0.99    inference(ennf_transformation,[],[f13])).
% 2.21/0.99  
% 2.21/0.99  fof(f24,plain,(
% 2.21/0.99    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.21/0.99    inference(flattening,[],[f23])).
% 2.21/0.99  
% 2.21/0.99  fof(f64,plain,(
% 2.21/0.99    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.21/0.99    inference(cnf_transformation,[],[f24])).
% 2.21/0.99  
% 2.21/0.99  fof(f71,plain,(
% 2.21/0.99    v2_pre_topc(sK4)),
% 2.21/0.99    inference(cnf_transformation,[],[f46])).
% 2.21/0.99  
% 2.21/0.99  fof(f4,axiom,(
% 2.21/0.99    v1_xboole_0(k1_xboole_0)),
% 2.21/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.21/0.99  
% 2.21/0.99  fof(f53,plain,(
% 2.21/0.99    v1_xboole_0(k1_xboole_0)),
% 2.21/0.99    inference(cnf_transformation,[],[f4])).
% 2.21/0.99  
% 2.21/0.99  cnf(c_25,negated_conjecture,
% 2.21/0.99      ( v1_xboole_0(sK5) ),
% 2.21/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1976,plain,
% 2.21/0.99      ( v1_xboole_0(sK5) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_7,plain,
% 2.21/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.21/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1984,plain,
% 2.21/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_3214,plain,
% 2.21/0.99      ( sK5 = k1_xboole_0 ),
% 2.21/0.99      inference(superposition,[status(thm)],[c_1976,c_1984]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_24,negated_conjecture,
% 2.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.21/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1977,plain,
% 2.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_18,plain,
% 2.21/0.99      ( v2_tex_2(X0,X1)
% 2.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.99      | r1_tarski(sK2(X1,X0),X0)
% 2.21/0.99      | ~ l1_pre_topc(X1) ),
% 2.21/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_26,negated_conjecture,
% 2.21/0.99      ( l1_pre_topc(sK4) ),
% 2.21/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_544,plain,
% 2.21/0.99      ( v2_tex_2(X0,X1)
% 2.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/0.99      | r1_tarski(sK2(X1,X0),X0)
% 2.21/0.99      | sK4 != X1 ),
% 2.21/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_545,plain,
% 2.21/0.99      ( v2_tex_2(X0,sK4)
% 2.21/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.99      | r1_tarski(sK2(sK4,X0),X0) ),
% 2.21/0.99      inference(unflattening,[status(thm)],[c_544]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1970,plain,
% 2.21/0.99      ( v2_tex_2(X0,sK4) = iProver_top
% 2.21/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.99      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_545]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_2310,plain,
% 2.21/0.99      ( v2_tex_2(sK5,sK4) = iProver_top
% 2.21/0.99      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 2.21/0.99      inference(superposition,[status(thm)],[c_1977,c_1970]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_31,plain,
% 2.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_23,negated_conjecture,
% 2.21/0.99      ( ~ v2_tex_2(sK5,sK4) ),
% 2.21/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_890,plain,
% 2.21/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.99      | r1_tarski(sK2(sK4,X0),X0)
% 2.21/0.99      | sK4 != sK4
% 2.21/0.99      | sK5 != X0 ),
% 2.21/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_545]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_891,plain,
% 2.21/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/0.99      | r1_tarski(sK2(sK4,sK5),sK5) ),
% 2.21/0.99      inference(unflattening,[status(thm)],[c_890]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_892,plain,
% 2.21/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/0.99      | r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_891]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_2686,plain,
% 2.21/0.99      ( r1_tarski(sK2(sK4,sK5),sK5) = iProver_top ),
% 2.21/0.99      inference(global_propositional_subsumption,
% 2.21/0.99                [status(thm)],
% 2.21/0.99                [c_2310,c_31,c_892]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_3285,plain,
% 2.21/0.99      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.21/0.99      inference(demodulation,[status(thm)],[c_3214,c_2686]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_4,plain,
% 2.21/0.99      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.21/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1987,plain,
% 2.21/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.21/0.99      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_15,plain,
% 2.21/0.99      ( m1_subset_1(X0,X1)
% 2.21/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.21/0.99      | ~ r2_hidden(X0,X2) ),
% 2.21/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_1979,plain,
% 2.21/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 2.21/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.21/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_3066,plain,
% 2.21/0.99      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 2.21/0.99      | r2_hidden(X0,sK5) != iProver_top ),
% 2.21/0.99      inference(superposition,[status(thm)],[c_1977,c_1979]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_2,plain,
% 2.21/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.21/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_374,plain,
% 2.21/0.99      ( ~ r2_hidden(X0,X1) | sK5 != X1 ),
% 2.21/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_25]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_375,plain,
% 2.21/0.99      ( ~ r2_hidden(X0,sK5) ),
% 2.21/0.99      inference(unflattening,[status(thm)],[c_374]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_376,plain,
% 2.21/0.99      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.21/0.99      inference(predicate_to_equality,[status(thm)],[c_375]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_3400,plain,
% 2.21/0.99      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.21/0.99      inference(global_propositional_subsumption,
% 2.21/0.99                [status(thm)],
% 2.21/0.99                [c_3066,c_376]) ).
% 2.21/0.99  
% 2.21/0.99  cnf(c_3404,plain,
% 2.21/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 2.21/0.99      inference(light_normalisation,[status(thm)],[c_3400,c_3214]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_3711,plain,
% 2.21/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1987,c_3404]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_8,plain,
% 2.21/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1983,plain,
% 2.21/1.00      ( X0 = X1
% 2.21/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.21/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4461,plain,
% 2.21/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_3711,c_1983]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_5188,plain,
% 2.21/1.00      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_3285,c_4461]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_14,plain,
% 2.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.21/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1980,plain,
% 2.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_13,plain,
% 2.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.21/1.00      | k4_xboole_0(X2,k4_xboole_0(X2,X0)) = k9_subset_1(X1,X2,X0) ),
% 2.21/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1981,plain,
% 2.21/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k9_subset_1(X2,X0,X1)
% 2.21/1.00      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4350,plain,
% 2.21/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k9_subset_1(X1,X0,k1_xboole_0) ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_1980,c_1981]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_11,plain,
% 2.21/1.00      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_0,plain,
% 2.21/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
% 2.21/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_12,plain,
% 2.21/1.00      ( k4_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.21/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2410,plain,
% 2.21/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) = k1_xboole_0 ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_0,c_12]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2413,plain,
% 2.21/1.00      ( k4_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.21/1.00      inference(light_normalisation,[status(thm)],[c_2410,c_11]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4370,plain,
% 2.21/1.00      ( k9_subset_1(X0,X1,k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.00      inference(light_normalisation,[status(thm)],[c_4350,c_11,c_2413]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_17,plain,
% 2.21/1.00      ( v2_tex_2(X0,X1)
% 2.21/1.00      | ~ v4_pre_topc(X2,X1)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | ~ l1_pre_topc(X1)
% 2.21/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 2.21/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_559,plain,
% 2.21/1.00      ( v2_tex_2(X0,X1)
% 2.21/1.00      | ~ v4_pre_topc(X2,X1)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 2.21/1.00      | sK4 != X1 ),
% 2.21/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_560,plain,
% 2.21/1.00      ( v2_tex_2(X0,sK4)
% 2.21/1.00      | ~ v4_pre_topc(X1,sK4)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 2.21/1.00      inference(unflattening,[status(thm)],[c_559]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1969,plain,
% 2.21/1.00      ( k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0)
% 2.21/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 2.21/1.00      | v4_pre_topc(X1,sK4) != iProver_top
% 2.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_560]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4378,plain,
% 2.21/1.00      ( sK2(sK4,X0) != k1_xboole_0
% 2.21/1.00      | v2_tex_2(X0,sK4) = iProver_top
% 2.21/1.00      | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
% 2.21/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.21/1.00      inference(superposition,[status(thm)],[c_4370,c_1969]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_4380,plain,
% 2.21/1.00      ( sK2(sK4,k1_xboole_0) != k1_xboole_0
% 2.21/1.00      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.21/1.00      | v4_pre_topc(k1_xboole_0,sK4) != iProver_top
% 2.21/1.00      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_4378]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_1978,plain,
% 2.21/1.00      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_3288,plain,
% 2.21/1.00      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 2.21/1.00      inference(demodulation,[status(thm)],[c_3214,c_1978]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2172,plain,
% 2.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.21/1.00      inference(instantiation,[status(thm)],[c_14]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_2176,plain,
% 2.21/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_2172]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_16,plain,
% 2.21/1.00      ( v4_pre_topc(X0,X1)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | ~ v2_pre_topc(X1)
% 2.21/1.00      | ~ l1_pre_topc(X1)
% 2.21/1.00      | ~ v1_xboole_0(X0) ),
% 2.21/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_27,negated_conjecture,
% 2.21/1.00      ( v2_pre_topc(sK4) ),
% 2.21/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_275,plain,
% 2.21/1.00      ( v4_pre_topc(X0,X1)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.21/1.00      | ~ l1_pre_topc(X1)
% 2.21/1.00      | ~ v1_xboole_0(X0)
% 2.21/1.00      | sK4 != X1 ),
% 2.21/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_276,plain,
% 2.21/1.00      ( v4_pre_topc(X0,sK4)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | ~ l1_pre_topc(sK4)
% 2.21/1.00      | ~ v1_xboole_0(X0) ),
% 2.21/1.00      inference(unflattening,[status(thm)],[c_275]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_280,plain,
% 2.21/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | v4_pre_topc(X0,sK4)
% 2.21/1.00      | ~ v1_xboole_0(X0) ),
% 2.21/1.00      inference(global_propositional_subsumption,
% 2.21/1.00                [status(thm)],
% 2.21/1.00                [c_276,c_26]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_281,plain,
% 2.21/1.00      ( v4_pre_topc(X0,sK4)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | ~ v1_xboole_0(X0) ),
% 2.21/1.00      inference(renaming,[status(thm)],[c_280]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_6,plain,
% 2.21/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.21/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_337,plain,
% 2.21/1.00      ( v4_pre_topc(X0,sK4)
% 2.21/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.21/1.00      | k1_xboole_0 != X0 ),
% 2.21/1.00      inference(resolution_lifted,[status(thm)],[c_281,c_6]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_338,plain,
% 2.21/1.00      ( v4_pre_topc(k1_xboole_0,sK4)
% 2.21/1.00      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.21/1.00      inference(unflattening,[status(thm)],[c_337]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_344,plain,
% 2.21/1.00      ( v4_pre_topc(k1_xboole_0,sK4) ),
% 2.21/1.00      inference(forward_subsumption_resolution,
% 2.21/1.00                [status(thm)],
% 2.21/1.00                [c_338,c_14]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(c_346,plain,
% 2.21/1.00      ( v4_pre_topc(k1_xboole_0,sK4) = iProver_top ),
% 2.21/1.00      inference(predicate_to_equality,[status(thm)],[c_344]) ).
% 2.21/1.00  
% 2.21/1.00  cnf(contradiction,plain,
% 2.21/1.00      ( $false ),
% 2.21/1.00      inference(minisat,[status(thm)],[c_5188,c_4380,c_3288,c_2176,c_346]) ).
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.00  
% 2.21/1.00  ------                               Statistics
% 2.21/1.00  
% 2.21/1.00  ------ General
% 2.21/1.00  
% 2.21/1.00  abstr_ref_over_cycles:                  0
% 2.21/1.00  abstr_ref_under_cycles:                 0
% 2.21/1.00  gc_basic_clause_elim:                   0
% 2.21/1.00  forced_gc_time:                         0
% 2.21/1.00  parsing_time:                           0.007
% 2.21/1.00  unif_index_cands_time:                  0.
% 2.21/1.00  unif_index_add_time:                    0.
% 2.21/1.00  orderings_time:                         0.
% 2.21/1.00  out_proof_time:                         0.008
% 2.21/1.00  total_time:                             0.163
% 2.21/1.00  num_of_symbols:                         50
% 2.21/1.00  num_of_terms:                           3760
% 2.21/1.00  
% 2.21/1.00  ------ Preprocessing
% 2.21/1.00  
% 2.21/1.00  num_of_splits:                          0
% 2.21/1.00  num_of_split_atoms:                     0
% 2.21/1.00  num_of_reused_defs:                     0
% 2.21/1.00  num_eq_ax_congr_red:                    30
% 2.21/1.00  num_of_sem_filtered_clauses:            1
% 2.21/1.00  num_of_subtypes:                        0
% 2.21/1.00  monotx_restored_types:                  0
% 2.21/1.00  sat_num_of_epr_types:                   0
% 2.21/1.00  sat_num_of_non_cyclic_types:            0
% 2.21/1.00  sat_guarded_non_collapsed_types:        0
% 2.21/1.00  num_pure_diseq_elim:                    0
% 2.21/1.00  simp_replaced_by:                       0
% 2.21/1.00  res_preprocessed:                       131
% 2.21/1.00  prep_upred:                             0
% 2.21/1.00  prep_unflattend:                        35
% 2.21/1.00  smt_new_axioms:                         0
% 2.21/1.00  pred_elim_cands:                        6
% 2.21/1.00  pred_elim:                              2
% 2.21/1.00  pred_elim_cl:                           2
% 2.21/1.00  pred_elim_cycles:                       9
% 2.21/1.00  merged_defs:                            0
% 2.21/1.00  merged_defs_ncl:                        0
% 2.21/1.00  bin_hyper_res:                          0
% 2.21/1.00  prep_cycles:                            4
% 2.21/1.00  pred_elim_time:                         0.021
% 2.21/1.00  splitting_time:                         0.
% 2.21/1.00  sem_filter_time:                        0.
% 2.21/1.00  monotx_time:                            0.
% 2.21/1.00  subtype_inf_time:                       0.
% 2.21/1.00  
% 2.21/1.00  ------ Problem properties
% 2.21/1.00  
% 2.21/1.00  clauses:                                25
% 2.21/1.00  conjectures:                            3
% 2.21/1.00  epr:                                    8
% 2.21/1.00  horn:                                   21
% 2.21/1.00  ground:                                 4
% 2.21/1.00  unary:                                  9
% 2.21/1.00  binary:                                 6
% 2.21/1.00  lits:                                   59
% 2.21/1.00  lits_eq:                                8
% 2.21/1.00  fd_pure:                                0
% 2.21/1.00  fd_pseudo:                              0
% 2.21/1.00  fd_cond:                                1
% 2.21/1.00  fd_pseudo_cond:                         1
% 2.21/1.00  ac_symbols:                             0
% 2.21/1.00  
% 2.21/1.00  ------ Propositional Solver
% 2.21/1.00  
% 2.21/1.00  prop_solver_calls:                      28
% 2.21/1.00  prop_fast_solver_calls:                 1104
% 2.21/1.00  smt_solver_calls:                       0
% 2.21/1.00  smt_fast_solver_calls:                  0
% 2.21/1.00  prop_num_of_clauses:                    1415
% 2.21/1.00  prop_preprocess_simplified:             5326
% 2.21/1.00  prop_fo_subsumed:                       24
% 2.21/1.00  prop_solver_time:                       0.
% 2.21/1.00  smt_solver_time:                        0.
% 2.21/1.00  smt_fast_solver_time:                   0.
% 2.21/1.00  prop_fast_solver_time:                  0.
% 2.21/1.00  prop_unsat_core_time:                   0.
% 2.21/1.00  
% 2.21/1.00  ------ QBF
% 2.21/1.00  
% 2.21/1.00  qbf_q_res:                              0
% 2.21/1.00  qbf_num_tautologies:                    0
% 2.21/1.00  qbf_prep_cycles:                        0
% 2.21/1.00  
% 2.21/1.00  ------ BMC1
% 2.21/1.00  
% 2.21/1.00  bmc1_current_bound:                     -1
% 2.21/1.00  bmc1_last_solved_bound:                 -1
% 2.21/1.00  bmc1_unsat_core_size:                   -1
% 2.21/1.00  bmc1_unsat_core_parents_size:           -1
% 2.21/1.00  bmc1_merge_next_fun:                    0
% 2.21/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.00  
% 2.21/1.00  ------ Instantiation
% 2.21/1.00  
% 2.21/1.00  inst_num_of_clauses:                    408
% 2.21/1.00  inst_num_in_passive:                    115
% 2.21/1.00  inst_num_in_active:                     220
% 2.21/1.00  inst_num_in_unprocessed:                74
% 2.21/1.00  inst_num_of_loops:                      290
% 2.21/1.00  inst_num_of_learning_restarts:          0
% 2.21/1.00  inst_num_moves_active_passive:          67
% 2.21/1.00  inst_lit_activity:                      0
% 2.21/1.00  inst_lit_activity_moves:                0
% 2.21/1.00  inst_num_tautologies:                   0
% 2.21/1.00  inst_num_prop_implied:                  0
% 2.21/1.00  inst_num_existing_simplified:           0
% 2.21/1.00  inst_num_eq_res_simplified:             0
% 2.21/1.00  inst_num_child_elim:                    0
% 2.21/1.00  inst_num_of_dismatching_blockings:      122
% 2.21/1.00  inst_num_of_non_proper_insts:           399
% 2.21/1.00  inst_num_of_duplicates:                 0
% 2.21/1.00  inst_inst_num_from_inst_to_res:         0
% 2.21/1.00  inst_dismatching_checking_time:         0.
% 2.21/1.00  
% 2.21/1.00  ------ Resolution
% 2.21/1.00  
% 2.21/1.00  res_num_of_clauses:                     0
% 2.21/1.00  res_num_in_passive:                     0
% 2.21/1.00  res_num_in_active:                      0
% 2.21/1.00  res_num_of_loops:                       135
% 2.21/1.00  res_forward_subset_subsumed:            41
% 2.21/1.00  res_backward_subset_subsumed:           2
% 2.21/1.00  res_forward_subsumed:                   0
% 2.21/1.00  res_backward_subsumed:                  0
% 2.21/1.00  res_forward_subsumption_resolution:     3
% 2.21/1.00  res_backward_subsumption_resolution:    0
% 2.21/1.00  res_clause_to_clause_subsumption:       532
% 2.21/1.00  res_orphan_elimination:                 0
% 2.21/1.00  res_tautology_del:                      40
% 2.21/1.00  res_num_eq_res_simplified:              0
% 2.21/1.00  res_num_sel_changes:                    0
% 2.21/1.00  res_moves_from_active_to_pass:          0
% 2.21/1.00  
% 2.21/1.00  ------ Superposition
% 2.21/1.00  
% 2.21/1.00  sup_time_total:                         0.
% 2.21/1.00  sup_time_generating:                    0.
% 2.21/1.00  sup_time_sim_full:                      0.
% 2.21/1.00  sup_time_sim_immed:                     0.
% 2.21/1.00  
% 2.21/1.00  sup_num_of_clauses:                     76
% 2.21/1.00  sup_num_in_active:                      51
% 2.21/1.00  sup_num_in_passive:                     25
% 2.21/1.00  sup_num_of_loops:                       56
% 2.21/1.00  sup_fw_superposition:                   55
% 2.21/1.00  sup_bw_superposition:                   23
% 2.21/1.00  sup_immediate_simplified:               10
% 2.21/1.00  sup_given_eliminated:                   0
% 2.21/1.00  comparisons_done:                       0
% 2.21/1.00  comparisons_avoided:                    0
% 2.21/1.00  
% 2.21/1.00  ------ Simplifications
% 2.21/1.00  
% 2.21/1.00  
% 2.21/1.00  sim_fw_subset_subsumed:                 4
% 2.21/1.00  sim_bw_subset_subsumed:                 2
% 2.21/1.00  sim_fw_subsumed:                        2
% 2.21/1.00  sim_bw_subsumed:                        0
% 2.21/1.00  sim_fw_subsumption_res:                 0
% 2.21/1.00  sim_bw_subsumption_res:                 0
% 2.21/1.00  sim_tautology_del:                      2
% 2.21/1.00  sim_eq_tautology_del:                   4
% 2.21/1.00  sim_eq_res_simp:                        0
% 2.21/1.00  sim_fw_demodulated:                     1
% 2.21/1.00  sim_bw_demodulated:                     6
% 2.21/1.00  sim_light_normalised:                   5
% 2.21/1.00  sim_joinable_taut:                      0
% 2.21/1.00  sim_joinable_simp:                      0
% 2.21/1.00  sim_ac_normalised:                      0
% 2.21/1.00  sim_smt_subsumption:                    0
% 2.21/1.00  
%------------------------------------------------------------------------------
