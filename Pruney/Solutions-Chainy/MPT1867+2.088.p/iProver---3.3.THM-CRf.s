%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:23 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 367 expanded)
%              Number of clauses        :   86 ( 135 expanded)
%              Number of leaves         :   16 (  80 expanded)
%              Depth                    :   23
%              Number of atoms          :  474 (1559 expanded)
%              Number of equality atoms :  140 ( 216 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f42,f46])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f46])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f25])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f34,plain,(
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
    inference(rectify,[],[f33])).

fof(f36,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4
        & v3_pre_topc(sK3(X0,X1,X4),X0)
        & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
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
          ( ~ v2_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ~ v2_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f39,f38])).

fof(f59,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f61,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK0) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f29])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X2,X0)
      | k1_tops_1(X0,X2) != X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f58,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_tops_1(X1,X3) = X3
      | ~ v3_pre_topc(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK2(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f62,plain,(
    ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3658,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_48,X1_48)),X0_48) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_4204,plain,
    ( r1_tarski(k1_setfam_1(k2_tarski(X0_48,X1_48)),X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3658])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_3657,plain,
    ( ~ r1_tarski(X0_48,k1_xboole_0)
    | k1_xboole_0 = X0_48 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_4205,plain,
    ( k1_xboole_0 = X0_48
    | r1_tarski(X0_48,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3657])).

cnf(c_4801,plain,
    ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_48)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4204,c_4205])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_3655,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_4207,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3655])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3656,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X0_51))
    | k9_subset_1(X0_51,X1_48,X0_48) = k1_setfam_1(k2_tarski(X1_48,X0_48)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_4206,plain,
    ( k9_subset_1(X0_51,X0_48,X1_48) = k1_setfam_1(k2_tarski(X0_48,X1_48))
    | m1_subset_1(X1_48,k1_zfmisc_1(X0_51)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3656])).

cnf(c_4746,plain,
    ( k9_subset_1(X0_51,X0_48,k1_xboole_0) = k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_4207,c_4206])).

cnf(c_10,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1054,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_1055,plain,
    ( v2_tex_2(X0,sK4)
    | ~ v3_pre_topc(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_1054])).

cnf(c_3634,plain,
    ( v2_tex_2(X0_48,sK4)
    | ~ v3_pre_topc(X1_48,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | k9_subset_1(u1_struct_0(sK4),X0_48,X1_48) != sK2(sK4,X0_48) ),
    inference(subtyping,[status(esa)],[c_1055])).

cnf(c_4233,plain,
    ( k9_subset_1(u1_struct_0(sK4),X0_48,X1_48) != sK2(sK4,X0_48)
    | v2_tex_2(X0_48,sK4) = iProver_top
    | v3_pre_topc(X1_48,sK4) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3634])).

cnf(c_5315,plain,
    ( k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
    | v2_tex_2(X0_48,sK4) = iProver_top
    | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4746,c_4233])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_24,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5,plain,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_8,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_243,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_244,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(sK4)
    | k1_tops_1(sK4,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_243])).

cnf(c_248,plain,
    ( ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,sK4)
    | k1_tops_1(sK4,X0) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_244,c_19])).

cnf(c_249,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X2)
    | k1_tops_1(sK4,X0) != X0 ),
    inference(renaming,[status(thm)],[c_248])).

cnf(c_918,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(sK4,X0) != X0
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_249])).

cnf(c_919,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK4,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_918])).

cnf(c_3642,plain,
    ( v3_pre_topc(X0_48,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK4,X0_48) != X0_48 ),
    inference(subtyping,[status(esa)],[c_919])).

cnf(c_3663,plain,
    ( v3_pre_topc(X0_48,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(sK4,X0_48) != X0_48
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_3642])).

cnf(c_3717,plain,
    ( k1_tops_1(sK4,X0_48) != X0_48
    | v3_pre_topc(X0_48,sK4) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3663])).

cnf(c_3719,plain,
    ( k1_tops_1(sK4,k1_xboole_0) != k1_xboole_0
    | v3_pre_topc(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(instantiation,[status(thm)],[c_3717])).

cnf(c_1087,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(sK4,X0) != X0
    | sK4 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_249])).

cnf(c_1088,plain,
    ( v3_pre_topc(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(sK4,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_1087])).

cnf(c_3632,plain,
    ( v3_pre_topc(X0_48,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(sK4,X0_48) != X0_48 ),
    inference(subtyping,[status(esa)],[c_1088])).

cnf(c_3667,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_3632])).

cnf(c_3740,plain,
    ( sP3_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3667])).

cnf(c_9,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_270,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X3)
    | k1_tops_1(X1,X0) = X0
    | sK4 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_20])).

cnf(c_271,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(sK4)
    | k1_tops_1(X1,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X0,X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_19])).

cnf(c_276,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_pre_topc(X1)
    | k1_tops_1(X1,X0) = X0 ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_774,plain,
    ( ~ v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
    | k1_tops_1(X1,X0) = X0
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_276])).

cnf(c_775,plain,
    ( ~ v3_pre_topc(X0,sK0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0) = X0 ),
    inference(unflattening,[status(thm)],[c_774])).

cnf(c_3650,plain,
    ( ~ v3_pre_topc(X0_48,sK0)
    | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_tops_1(sK0,X0_48) = X0_48 ),
    inference(subtyping,[status(esa)],[c_775])).

cnf(c_3659,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_3650])).

cnf(c_4502,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ sP0_iProver_split ),
    inference(instantiation,[status(thm)],[c_3659])).

cnf(c_4503,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4502])).

cnf(c_4514,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(instantiation,[status(thm)],[c_3655])).

cnf(c_4520,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4514])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1075,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(k1_tops_1(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_19])).

cnf(c_1076,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_1075])).

cnf(c_3633,plain,
    ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(k1_tops_1(sK4,X0_48),X0_48) ),
    inference(subtyping,[status(esa)],[c_1076])).

cnf(c_4234,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(k1_tops_1(sK4,X0_48),X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3633])).

cnf(c_4745,plain,
    ( r1_tarski(k1_tops_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4207,c_4234])).

cnf(c_5224,plain,
    ( k1_tops_1(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4745,c_4205])).

cnf(c_5772,plain,
    ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
    | v2_tex_2(X0_48,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5315,c_24,c_3719,c_3740,c_4503,c_4520,c_5224])).

cnf(c_5773,plain,
    ( k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
    | v2_tex_2(X0_48,sK4) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_5772])).

cnf(c_5781,plain,
    ( sK2(sK4,k1_xboole_0) != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4801,c_5773])).

cnf(c_11,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1039,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK2(X1,X0),X0)
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_19])).

cnf(c_1040,plain,
    ( v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0),X0) ),
    inference(unflattening,[status(thm)],[c_1039])).

cnf(c_3635,plain,
    ( v2_tex_2(X0_48,sK4)
    | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
    | r1_tarski(sK2(sK4,X0_48),X0_48) ),
    inference(subtyping,[status(esa)],[c_1040])).

cnf(c_4232,plain,
    ( v2_tex_2(X0_48,sK4) = iProver_top
    | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0_48),X0_48) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3635])).

cnf(c_5042,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4207,c_4232])).

cnf(c_1041,plain,
    ( v2_tex_2(X0,sK4) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1040])).

cnf(c_1043,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1041])).

cnf(c_16,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3654,negated_conjecture,
    ( ~ v2_tex_2(sK5,sK4) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_4208,plain,
    ( v2_tex_2(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3654])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_18,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_237,plain,
    ( sK5 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_18])).

cnf(c_238,plain,
    ( k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_237])).

cnf(c_3652,plain,
    ( k1_xboole_0 = sK5 ),
    inference(subtyping,[status(esa)],[c_238])).

cnf(c_4242,plain,
    ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4208,c_3652])).

cnf(c_5662,plain,
    ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5042,c_1043,c_4242,c_4520])).

cnf(c_5667,plain,
    ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5662,c_4205])).

cnf(c_5782,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5781,c_5667])).

cnf(c_5783,plain,
    ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5782])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5783,c_4520,c_4242])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.02/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.01  
% 2.02/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.02/1.01  
% 2.02/1.01  ------  iProver source info
% 2.02/1.01  
% 2.02/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.02/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.02/1.01  git: non_committed_changes: false
% 2.02/1.01  git: last_make_outside_of_git: false
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.01  --fof                                   false
% 2.02/1.01  --time_out_real                         305.
% 2.02/1.01  --time_out_virtual                      -1.
% 2.02/1.01  --symbol_type_check                     false
% 2.02/1.01  --clausify_out                          false
% 2.02/1.01  --sig_cnt_out                           false
% 2.02/1.01  --trig_cnt_out                          false
% 2.02/1.01  --trig_cnt_out_tolerance                1.
% 2.02/1.01  --trig_cnt_out_sk_spl                   false
% 2.02/1.01  --abstr_cl_out                          false
% 2.02/1.01  
% 2.02/1.01  ------ Global Options
% 2.02/1.01  
% 2.02/1.01  --schedule                              default
% 2.02/1.01  --add_important_lit                     false
% 2.02/1.01  --prop_solver_per_cl                    1000
% 2.02/1.01  --min_unsat_core                        false
% 2.02/1.01  --soft_assumptions                      false
% 2.02/1.01  --soft_lemma_size                       3
% 2.02/1.01  --prop_impl_unit_size                   0
% 2.02/1.01  --prop_impl_unit                        []
% 2.02/1.01  --share_sel_clauses                     true
% 2.02/1.01  --reset_solvers                         false
% 2.02/1.01  --bc_imp_inh                            [conj_cone]
% 2.02/1.01  --conj_cone_tolerance                   3.
% 2.02/1.01  --extra_neg_conj                        none
% 2.02/1.01  --large_theory_mode                     true
% 2.02/1.01  --prolific_symb_bound                   200
% 2.02/1.01  --lt_threshold                          2000
% 2.02/1.01  --clause_weak_htbl                      true
% 2.02/1.01  --gc_record_bc_elim                     false
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing Options
% 2.02/1.01  
% 2.02/1.01  --preprocessing_flag                    true
% 2.02/1.01  --time_out_prep_mult                    0.1
% 2.02/1.01  --splitting_mode                        input
% 2.02/1.01  --splitting_grd                         true
% 2.02/1.01  --splitting_cvd                         false
% 2.02/1.01  --splitting_cvd_svl                     false
% 2.02/1.01  --splitting_nvd                         32
% 2.02/1.01  --sub_typing                            true
% 2.02/1.01  --prep_gs_sim                           true
% 2.02/1.01  --prep_unflatten                        true
% 2.02/1.01  --prep_res_sim                          true
% 2.02/1.01  --prep_upred                            true
% 2.02/1.01  --prep_sem_filter                       exhaustive
% 2.02/1.01  --prep_sem_filter_out                   false
% 2.02/1.01  --pred_elim                             true
% 2.02/1.01  --res_sim_input                         true
% 2.02/1.01  --eq_ax_congr_red                       true
% 2.02/1.01  --pure_diseq_elim                       true
% 2.02/1.01  --brand_transform                       false
% 2.02/1.01  --non_eq_to_eq                          false
% 2.02/1.01  --prep_def_merge                        true
% 2.02/1.01  --prep_def_merge_prop_impl              false
% 2.02/1.01  --prep_def_merge_mbd                    true
% 2.02/1.01  --prep_def_merge_tr_red                 false
% 2.02/1.01  --prep_def_merge_tr_cl                  false
% 2.02/1.01  --smt_preprocessing                     true
% 2.02/1.01  --smt_ac_axioms                         fast
% 2.02/1.01  --preprocessed_out                      false
% 2.02/1.01  --preprocessed_stats                    false
% 2.02/1.01  
% 2.02/1.01  ------ Abstraction refinement Options
% 2.02/1.01  
% 2.02/1.01  --abstr_ref                             []
% 2.02/1.01  --abstr_ref_prep                        false
% 2.02/1.01  --abstr_ref_until_sat                   false
% 2.02/1.01  --abstr_ref_sig_restrict                funpre
% 2.02/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.01  --abstr_ref_under                       []
% 2.02/1.01  
% 2.02/1.01  ------ SAT Options
% 2.02/1.01  
% 2.02/1.01  --sat_mode                              false
% 2.02/1.01  --sat_fm_restart_options                ""
% 2.02/1.01  --sat_gr_def                            false
% 2.02/1.01  --sat_epr_types                         true
% 2.02/1.01  --sat_non_cyclic_types                  false
% 2.02/1.01  --sat_finite_models                     false
% 2.02/1.01  --sat_fm_lemmas                         false
% 2.02/1.01  --sat_fm_prep                           false
% 2.02/1.01  --sat_fm_uc_incr                        true
% 2.02/1.01  --sat_out_model                         small
% 2.02/1.01  --sat_out_clauses                       false
% 2.02/1.01  
% 2.02/1.01  ------ QBF Options
% 2.02/1.01  
% 2.02/1.01  --qbf_mode                              false
% 2.02/1.01  --qbf_elim_univ                         false
% 2.02/1.01  --qbf_dom_inst                          none
% 2.02/1.01  --qbf_dom_pre_inst                      false
% 2.02/1.01  --qbf_sk_in                             false
% 2.02/1.01  --qbf_pred_elim                         true
% 2.02/1.01  --qbf_split                             512
% 2.02/1.01  
% 2.02/1.01  ------ BMC1 Options
% 2.02/1.01  
% 2.02/1.01  --bmc1_incremental                      false
% 2.02/1.01  --bmc1_axioms                           reachable_all
% 2.02/1.01  --bmc1_min_bound                        0
% 2.02/1.01  --bmc1_max_bound                        -1
% 2.02/1.01  --bmc1_max_bound_default                -1
% 2.02/1.01  --bmc1_symbol_reachability              true
% 2.02/1.01  --bmc1_property_lemmas                  false
% 2.02/1.01  --bmc1_k_induction                      false
% 2.02/1.01  --bmc1_non_equiv_states                 false
% 2.02/1.01  --bmc1_deadlock                         false
% 2.02/1.01  --bmc1_ucm                              false
% 2.02/1.01  --bmc1_add_unsat_core                   none
% 2.02/1.01  --bmc1_unsat_core_children              false
% 2.02/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.01  --bmc1_out_stat                         full
% 2.02/1.01  --bmc1_ground_init                      false
% 2.02/1.01  --bmc1_pre_inst_next_state              false
% 2.02/1.01  --bmc1_pre_inst_state                   false
% 2.02/1.01  --bmc1_pre_inst_reach_state             false
% 2.02/1.01  --bmc1_out_unsat_core                   false
% 2.02/1.01  --bmc1_aig_witness_out                  false
% 2.02/1.01  --bmc1_verbose                          false
% 2.02/1.01  --bmc1_dump_clauses_tptp                false
% 2.02/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.01  --bmc1_dump_file                        -
% 2.02/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.01  --bmc1_ucm_extend_mode                  1
% 2.02/1.01  --bmc1_ucm_init_mode                    2
% 2.02/1.01  --bmc1_ucm_cone_mode                    none
% 2.02/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.01  --bmc1_ucm_relax_model                  4
% 2.02/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.01  --bmc1_ucm_layered_model                none
% 2.02/1.01  --bmc1_ucm_max_lemma_size               10
% 2.02/1.01  
% 2.02/1.01  ------ AIG Options
% 2.02/1.01  
% 2.02/1.01  --aig_mode                              false
% 2.02/1.01  
% 2.02/1.01  ------ Instantiation Options
% 2.02/1.01  
% 2.02/1.01  --instantiation_flag                    true
% 2.02/1.01  --inst_sos_flag                         false
% 2.02/1.01  --inst_sos_phase                        true
% 2.02/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.01  --inst_lit_sel_side                     num_symb
% 2.02/1.01  --inst_solver_per_active                1400
% 2.02/1.01  --inst_solver_calls_frac                1.
% 2.02/1.01  --inst_passive_queue_type               priority_queues
% 2.02/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.01  --inst_passive_queues_freq              [25;2]
% 2.02/1.01  --inst_dismatching                      true
% 2.02/1.01  --inst_eager_unprocessed_to_passive     true
% 2.02/1.01  --inst_prop_sim_given                   true
% 2.02/1.01  --inst_prop_sim_new                     false
% 2.02/1.01  --inst_subs_new                         false
% 2.02/1.01  --inst_eq_res_simp                      false
% 2.02/1.01  --inst_subs_given                       false
% 2.02/1.01  --inst_orphan_elimination               true
% 2.02/1.01  --inst_learning_loop_flag               true
% 2.02/1.01  --inst_learning_start                   3000
% 2.02/1.01  --inst_learning_factor                  2
% 2.02/1.01  --inst_start_prop_sim_after_learn       3
% 2.02/1.01  --inst_sel_renew                        solver
% 2.02/1.01  --inst_lit_activity_flag                true
% 2.02/1.01  --inst_restr_to_given                   false
% 2.02/1.01  --inst_activity_threshold               500
% 2.02/1.01  --inst_out_proof                        true
% 2.02/1.01  
% 2.02/1.01  ------ Resolution Options
% 2.02/1.01  
% 2.02/1.01  --resolution_flag                       true
% 2.02/1.01  --res_lit_sel                           adaptive
% 2.02/1.01  --res_lit_sel_side                      none
% 2.02/1.01  --res_ordering                          kbo
% 2.02/1.01  --res_to_prop_solver                    active
% 2.02/1.01  --res_prop_simpl_new                    false
% 2.02/1.01  --res_prop_simpl_given                  true
% 2.02/1.01  --res_passive_queue_type                priority_queues
% 2.02/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.01  --res_passive_queues_freq               [15;5]
% 2.02/1.01  --res_forward_subs                      full
% 2.02/1.01  --res_backward_subs                     full
% 2.02/1.01  --res_forward_subs_resolution           true
% 2.02/1.01  --res_backward_subs_resolution          true
% 2.02/1.01  --res_orphan_elimination                true
% 2.02/1.01  --res_time_limit                        2.
% 2.02/1.01  --res_out_proof                         true
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Options
% 2.02/1.01  
% 2.02/1.01  --superposition_flag                    true
% 2.02/1.01  --sup_passive_queue_type                priority_queues
% 2.02/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.01  --demod_completeness_check              fast
% 2.02/1.01  --demod_use_ground                      true
% 2.02/1.01  --sup_to_prop_solver                    passive
% 2.02/1.01  --sup_prop_simpl_new                    true
% 2.02/1.01  --sup_prop_simpl_given                  true
% 2.02/1.01  --sup_fun_splitting                     false
% 2.02/1.01  --sup_smt_interval                      50000
% 2.02/1.01  
% 2.02/1.01  ------ Superposition Simplification Setup
% 2.02/1.01  
% 2.02/1.01  --sup_indices_passive                   []
% 2.02/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_full_bw                           [BwDemod]
% 2.02/1.01  --sup_immed_triv                        [TrivRules]
% 2.02/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_immed_bw_main                     []
% 2.02/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.01  
% 2.02/1.01  ------ Combination Options
% 2.02/1.01  
% 2.02/1.01  --comb_res_mult                         3
% 2.02/1.01  --comb_sup_mult                         2
% 2.02/1.01  --comb_inst_mult                        10
% 2.02/1.01  
% 2.02/1.01  ------ Debug Options
% 2.02/1.01  
% 2.02/1.01  --dbg_backtrace                         false
% 2.02/1.01  --dbg_dump_prop_clauses                 false
% 2.02/1.01  --dbg_dump_prop_clauses_file            -
% 2.02/1.01  --dbg_out_stat                          false
% 2.02/1.01  ------ Parsing...
% 2.02/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... gs_s  sp: 8 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.02/1.01  
% 2.02/1.01  ------ Preprocessing... sf_s  rm: 5 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.02/1.01  ------ Proving...
% 2.02/1.01  ------ Problem Properties 
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  clauses                                 35
% 2.02/1.01  conjectures                             2
% 2.02/1.01  EPR                                     7
% 2.02/1.01  Horn                                    27
% 2.02/1.01  unary                                   7
% 2.02/1.01  binary                                  12
% 2.02/1.01  lits                                    99
% 2.02/1.01  lits eq                                 11
% 2.02/1.01  fd_pure                                 0
% 2.02/1.01  fd_pseudo                               0
% 2.02/1.01  fd_cond                                 1
% 2.02/1.01  fd_pseudo_cond                          0
% 2.02/1.01  AC symbols                              0
% 2.02/1.01  
% 2.02/1.01  ------ Schedule dynamic 5 is on 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.02/1.01  
% 2.02/1.01  
% 2.02/1.01  ------ 
% 2.02/1.01  Current options:
% 2.02/1.01  ------ 
% 2.02/1.01  
% 2.02/1.01  ------ Input Options
% 2.02/1.01  
% 2.02/1.01  --out_options                           all
% 2.02/1.01  --tptp_safe_out                         true
% 2.02/1.01  --problem_path                          ""
% 2.02/1.01  --include_path                          ""
% 2.02/1.01  --clausifier                            res/vclausify_rel
% 2.02/1.01  --clausifier_options                    --mode clausify
% 2.02/1.01  --stdin                                 false
% 2.02/1.01  --stats_out                             all
% 2.02/1.01  
% 2.02/1.01  ------ General Options
% 2.02/1.01  
% 2.02/1.02  --fof                                   false
% 2.02/1.02  --time_out_real                         305.
% 2.02/1.02  --time_out_virtual                      -1.
% 2.02/1.02  --symbol_type_check                     false
% 2.02/1.02  --clausify_out                          false
% 2.02/1.02  --sig_cnt_out                           false
% 2.02/1.02  --trig_cnt_out                          false
% 2.02/1.02  --trig_cnt_out_tolerance                1.
% 2.02/1.02  --trig_cnt_out_sk_spl                   false
% 2.02/1.02  --abstr_cl_out                          false
% 2.02/1.02  
% 2.02/1.02  ------ Global Options
% 2.02/1.02  
% 2.02/1.02  --schedule                              default
% 2.02/1.02  --add_important_lit                     false
% 2.02/1.02  --prop_solver_per_cl                    1000
% 2.02/1.02  --min_unsat_core                        false
% 2.02/1.02  --soft_assumptions                      false
% 2.02/1.02  --soft_lemma_size                       3
% 2.02/1.02  --prop_impl_unit_size                   0
% 2.02/1.02  --prop_impl_unit                        []
% 2.02/1.02  --share_sel_clauses                     true
% 2.02/1.02  --reset_solvers                         false
% 2.02/1.02  --bc_imp_inh                            [conj_cone]
% 2.02/1.02  --conj_cone_tolerance                   3.
% 2.02/1.02  --extra_neg_conj                        none
% 2.02/1.02  --large_theory_mode                     true
% 2.02/1.02  --prolific_symb_bound                   200
% 2.02/1.02  --lt_threshold                          2000
% 2.02/1.02  --clause_weak_htbl                      true
% 2.02/1.02  --gc_record_bc_elim                     false
% 2.02/1.02  
% 2.02/1.02  ------ Preprocessing Options
% 2.02/1.02  
% 2.02/1.02  --preprocessing_flag                    true
% 2.02/1.02  --time_out_prep_mult                    0.1
% 2.02/1.02  --splitting_mode                        input
% 2.02/1.02  --splitting_grd                         true
% 2.02/1.02  --splitting_cvd                         false
% 2.02/1.02  --splitting_cvd_svl                     false
% 2.02/1.02  --splitting_nvd                         32
% 2.02/1.02  --sub_typing                            true
% 2.02/1.02  --prep_gs_sim                           true
% 2.02/1.02  --prep_unflatten                        true
% 2.02/1.02  --prep_res_sim                          true
% 2.02/1.02  --prep_upred                            true
% 2.02/1.02  --prep_sem_filter                       exhaustive
% 2.02/1.02  --prep_sem_filter_out                   false
% 2.02/1.02  --pred_elim                             true
% 2.02/1.02  --res_sim_input                         true
% 2.02/1.02  --eq_ax_congr_red                       true
% 2.02/1.02  --pure_diseq_elim                       true
% 2.02/1.02  --brand_transform                       false
% 2.02/1.02  --non_eq_to_eq                          false
% 2.02/1.02  --prep_def_merge                        true
% 2.02/1.02  --prep_def_merge_prop_impl              false
% 2.02/1.02  --prep_def_merge_mbd                    true
% 2.02/1.02  --prep_def_merge_tr_red                 false
% 2.02/1.02  --prep_def_merge_tr_cl                  false
% 2.02/1.02  --smt_preprocessing                     true
% 2.02/1.02  --smt_ac_axioms                         fast
% 2.02/1.02  --preprocessed_out                      false
% 2.02/1.02  --preprocessed_stats                    false
% 2.02/1.02  
% 2.02/1.02  ------ Abstraction refinement Options
% 2.02/1.02  
% 2.02/1.02  --abstr_ref                             []
% 2.02/1.02  --abstr_ref_prep                        false
% 2.02/1.02  --abstr_ref_until_sat                   false
% 2.02/1.02  --abstr_ref_sig_restrict                funpre
% 2.02/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.02/1.02  --abstr_ref_under                       []
% 2.02/1.02  
% 2.02/1.02  ------ SAT Options
% 2.02/1.02  
% 2.02/1.02  --sat_mode                              false
% 2.02/1.02  --sat_fm_restart_options                ""
% 2.02/1.02  --sat_gr_def                            false
% 2.02/1.02  --sat_epr_types                         true
% 2.02/1.02  --sat_non_cyclic_types                  false
% 2.02/1.02  --sat_finite_models                     false
% 2.02/1.02  --sat_fm_lemmas                         false
% 2.02/1.02  --sat_fm_prep                           false
% 2.02/1.02  --sat_fm_uc_incr                        true
% 2.02/1.02  --sat_out_model                         small
% 2.02/1.02  --sat_out_clauses                       false
% 2.02/1.02  
% 2.02/1.02  ------ QBF Options
% 2.02/1.02  
% 2.02/1.02  --qbf_mode                              false
% 2.02/1.02  --qbf_elim_univ                         false
% 2.02/1.02  --qbf_dom_inst                          none
% 2.02/1.02  --qbf_dom_pre_inst                      false
% 2.02/1.02  --qbf_sk_in                             false
% 2.02/1.02  --qbf_pred_elim                         true
% 2.02/1.02  --qbf_split                             512
% 2.02/1.02  
% 2.02/1.02  ------ BMC1 Options
% 2.02/1.02  
% 2.02/1.02  --bmc1_incremental                      false
% 2.02/1.02  --bmc1_axioms                           reachable_all
% 2.02/1.02  --bmc1_min_bound                        0
% 2.02/1.02  --bmc1_max_bound                        -1
% 2.02/1.02  --bmc1_max_bound_default                -1
% 2.02/1.02  --bmc1_symbol_reachability              true
% 2.02/1.02  --bmc1_property_lemmas                  false
% 2.02/1.02  --bmc1_k_induction                      false
% 2.02/1.02  --bmc1_non_equiv_states                 false
% 2.02/1.02  --bmc1_deadlock                         false
% 2.02/1.02  --bmc1_ucm                              false
% 2.02/1.02  --bmc1_add_unsat_core                   none
% 2.02/1.02  --bmc1_unsat_core_children              false
% 2.02/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.02/1.02  --bmc1_out_stat                         full
% 2.02/1.02  --bmc1_ground_init                      false
% 2.02/1.02  --bmc1_pre_inst_next_state              false
% 2.02/1.02  --bmc1_pre_inst_state                   false
% 2.02/1.02  --bmc1_pre_inst_reach_state             false
% 2.02/1.02  --bmc1_out_unsat_core                   false
% 2.02/1.02  --bmc1_aig_witness_out                  false
% 2.02/1.02  --bmc1_verbose                          false
% 2.02/1.02  --bmc1_dump_clauses_tptp                false
% 2.02/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.02/1.02  --bmc1_dump_file                        -
% 2.02/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.02/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.02/1.02  --bmc1_ucm_extend_mode                  1
% 2.02/1.02  --bmc1_ucm_init_mode                    2
% 2.02/1.02  --bmc1_ucm_cone_mode                    none
% 2.02/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.02/1.02  --bmc1_ucm_relax_model                  4
% 2.02/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.02/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.02/1.02  --bmc1_ucm_layered_model                none
% 2.02/1.02  --bmc1_ucm_max_lemma_size               10
% 2.02/1.02  
% 2.02/1.02  ------ AIG Options
% 2.02/1.02  
% 2.02/1.02  --aig_mode                              false
% 2.02/1.02  
% 2.02/1.02  ------ Instantiation Options
% 2.02/1.02  
% 2.02/1.02  --instantiation_flag                    true
% 2.02/1.02  --inst_sos_flag                         false
% 2.02/1.02  --inst_sos_phase                        true
% 2.02/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.02/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.02/1.02  --inst_lit_sel_side                     none
% 2.02/1.02  --inst_solver_per_active                1400
% 2.02/1.02  --inst_solver_calls_frac                1.
% 2.02/1.02  --inst_passive_queue_type               priority_queues
% 2.02/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.02/1.02  --inst_passive_queues_freq              [25;2]
% 2.02/1.02  --inst_dismatching                      true
% 2.02/1.02  --inst_eager_unprocessed_to_passive     true
% 2.02/1.02  --inst_prop_sim_given                   true
% 2.02/1.02  --inst_prop_sim_new                     false
% 2.02/1.02  --inst_subs_new                         false
% 2.02/1.02  --inst_eq_res_simp                      false
% 2.02/1.02  --inst_subs_given                       false
% 2.02/1.02  --inst_orphan_elimination               true
% 2.02/1.02  --inst_learning_loop_flag               true
% 2.02/1.02  --inst_learning_start                   3000
% 2.02/1.02  --inst_learning_factor                  2
% 2.02/1.02  --inst_start_prop_sim_after_learn       3
% 2.02/1.02  --inst_sel_renew                        solver
% 2.02/1.02  --inst_lit_activity_flag                true
% 2.02/1.02  --inst_restr_to_given                   false
% 2.02/1.02  --inst_activity_threshold               500
% 2.02/1.02  --inst_out_proof                        true
% 2.02/1.02  
% 2.02/1.02  ------ Resolution Options
% 2.02/1.02  
% 2.02/1.02  --resolution_flag                       false
% 2.02/1.02  --res_lit_sel                           adaptive
% 2.02/1.02  --res_lit_sel_side                      none
% 2.02/1.02  --res_ordering                          kbo
% 2.02/1.02  --res_to_prop_solver                    active
% 2.02/1.02  --res_prop_simpl_new                    false
% 2.02/1.02  --res_prop_simpl_given                  true
% 2.02/1.02  --res_passive_queue_type                priority_queues
% 2.02/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.02/1.02  --res_passive_queues_freq               [15;5]
% 2.02/1.02  --res_forward_subs                      full
% 2.02/1.02  --res_backward_subs                     full
% 2.02/1.02  --res_forward_subs_resolution           true
% 2.02/1.02  --res_backward_subs_resolution          true
% 2.02/1.02  --res_orphan_elimination                true
% 2.02/1.02  --res_time_limit                        2.
% 2.02/1.02  --res_out_proof                         true
% 2.02/1.02  
% 2.02/1.02  ------ Superposition Options
% 2.02/1.02  
% 2.02/1.02  --superposition_flag                    true
% 2.02/1.02  --sup_passive_queue_type                priority_queues
% 2.02/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.02/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.02/1.02  --demod_completeness_check              fast
% 2.02/1.02  --demod_use_ground                      true
% 2.02/1.02  --sup_to_prop_solver                    passive
% 2.02/1.02  --sup_prop_simpl_new                    true
% 2.02/1.02  --sup_prop_simpl_given                  true
% 2.02/1.02  --sup_fun_splitting                     false
% 2.02/1.02  --sup_smt_interval                      50000
% 2.02/1.02  
% 2.02/1.02  ------ Superposition Simplification Setup
% 2.02/1.02  
% 2.02/1.02  --sup_indices_passive                   []
% 2.02/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.02/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.02/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.02  --sup_full_bw                           [BwDemod]
% 2.02/1.02  --sup_immed_triv                        [TrivRules]
% 2.02/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.02/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.02  --sup_immed_bw_main                     []
% 2.02/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.02/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.02/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.02/1.02  
% 2.02/1.02  ------ Combination Options
% 2.02/1.02  
% 2.02/1.02  --comb_res_mult                         3
% 2.02/1.02  --comb_sup_mult                         2
% 2.02/1.02  --comb_inst_mult                        10
% 2.02/1.02  
% 2.02/1.02  ------ Debug Options
% 2.02/1.02  
% 2.02/1.02  --dbg_backtrace                         false
% 2.02/1.02  --dbg_dump_prop_clauses                 false
% 2.02/1.02  --dbg_dump_prop_clauses_file            -
% 2.02/1.02  --dbg_out_stat                          false
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  ------ Proving...
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  % SZS status Theorem for theBenchmark.p
% 2.02/1.02  
% 2.02/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.02/1.02  
% 2.02/1.02  fof(f2,axiom,(
% 2.02/1.02    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f42,plain,(
% 2.02/1.02    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f2])).
% 2.02/1.02  
% 2.02/1.02  fof(f6,axiom,(
% 2.02/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f46,plain,(
% 2.02/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.02/1.02    inference(cnf_transformation,[],[f6])).
% 2.02/1.02  
% 2.02/1.02  fof(f63,plain,(
% 2.02/1.02    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 2.02/1.02    inference(definition_unfolding,[],[f42,f46])).
% 2.02/1.02  
% 2.02/1.02  fof(f3,axiom,(
% 2.02/1.02    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f19,plain,(
% 2.02/1.02    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 2.02/1.02    inference(ennf_transformation,[],[f3])).
% 2.02/1.02  
% 2.02/1.02  fof(f43,plain,(
% 2.02/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f19])).
% 2.02/1.02  
% 2.02/1.02  fof(f5,axiom,(
% 2.02/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f45,plain,(
% 2.02/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.02/1.02    inference(cnf_transformation,[],[f5])).
% 2.02/1.02  
% 2.02/1.02  fof(f4,axiom,(
% 2.02/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f20,plain,(
% 2.02/1.02    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.02/1.02    inference(ennf_transformation,[],[f4])).
% 2.02/1.02  
% 2.02/1.02  fof(f44,plain,(
% 2.02/1.02    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.02/1.02    inference(cnf_transformation,[],[f20])).
% 2.02/1.02  
% 2.02/1.02  fof(f64,plain,(
% 2.02/1.02    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.02/1.02    inference(definition_unfolding,[],[f44,f46])).
% 2.02/1.02  
% 2.02/1.02  fof(f12,axiom,(
% 2.02/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f25,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(ennf_transformation,[],[f12])).
% 2.02/1.02  
% 2.02/1.02  fof(f26,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(flattening,[],[f25])).
% 2.02/1.02  
% 2.02/1.02  fof(f33,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(nnf_transformation,[],[f26])).
% 2.02/1.02  
% 2.02/1.02  fof(f34,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(rectify,[],[f33])).
% 2.02/1.02  
% 2.02/1.02  fof(f36,plain,(
% 2.02/1.02    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.02    introduced(choice_axiom,[])).
% 2.02/1.02  
% 2.02/1.02  fof(f35,plain,(
% 2.02/1.02    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.02/1.02    introduced(choice_axiom,[])).
% 2.02/1.02  
% 2.02/1.02  fof(f37,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK3(X0,X1,X4)) = X4 & v3_pre_topc(sK3(X0,X1,X4),X0) & m1_subset_1(sK3(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f34,f36,f35])).
% 2.02/1.02  
% 2.02/1.02  fof(f57,plain,(
% 2.02/1.02    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK2(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f37])).
% 2.02/1.02  
% 2.02/1.02  fof(f13,conjecture,(
% 2.02/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f14,negated_conjecture,(
% 2.02/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.02/1.02    inference(negated_conjecture,[],[f13])).
% 2.02/1.02  
% 2.02/1.02  fof(f15,plain,(
% 2.02/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 2.02/1.02    inference(pure_predicate_removal,[],[f14])).
% 2.02/1.02  
% 2.02/1.02  fof(f27,plain,(
% 2.02/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.02/1.02    inference(ennf_transformation,[],[f15])).
% 2.02/1.02  
% 2.02/1.02  fof(f28,plain,(
% 2.02/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.02/1.02    inference(flattening,[],[f27])).
% 2.02/1.02  
% 2.02/1.02  fof(f39,plain,(
% 2.02/1.02    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 2.02/1.02    introduced(choice_axiom,[])).
% 2.02/1.02  
% 2.02/1.02  fof(f38,plain,(
% 2.02/1.02    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4))),
% 2.02/1.02    introduced(choice_axiom,[])).
% 2.02/1.02  
% 2.02/1.02  fof(f40,plain,(
% 2.02/1.02    (~v2_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4)),
% 2.02/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f28,f39,f38])).
% 2.02/1.02  
% 2.02/1.02  fof(f59,plain,(
% 2.02/1.02    l1_pre_topc(sK4)),
% 2.02/1.02    inference(cnf_transformation,[],[f40])).
% 2.02/1.02  
% 2.02/1.02  fof(f61,plain,(
% 2.02/1.02    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.02/1.02    inference(cnf_transformation,[],[f40])).
% 2.02/1.02  
% 2.02/1.02  fof(f8,axiom,(
% 2.02/1.02    ? [X0] : l1_pre_topc(X0)),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f29,plain,(
% 2.02/1.02    ? [X0] : l1_pre_topc(X0) => l1_pre_topc(sK0)),
% 2.02/1.02    introduced(choice_axiom,[])).
% 2.02/1.02  
% 2.02/1.02  fof(f30,plain,(
% 2.02/1.02    l1_pre_topc(sK0)),
% 2.02/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f8,f29])).
% 2.02/1.02  
% 2.02/1.02  fof(f47,plain,(
% 2.02/1.02    l1_pre_topc(sK0)),
% 2.02/1.02    inference(cnf_transformation,[],[f30])).
% 2.02/1.02  
% 2.02/1.02  fof(f11,axiom,(
% 2.02/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f23,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.02/1.02    inference(ennf_transformation,[],[f11])).
% 2.02/1.02  
% 2.02/1.02  fof(f24,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.02/1.02    inference(flattening,[],[f23])).
% 2.02/1.02  
% 2.02/1.02  fof(f51,plain,(
% 2.02/1.02    ( ! [X2,X0,X3,X1] : (v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f24])).
% 2.02/1.02  
% 2.02/1.02  fof(f58,plain,(
% 2.02/1.02    v2_pre_topc(sK4)),
% 2.02/1.02    inference(cnf_transformation,[],[f40])).
% 2.02/1.02  
% 2.02/1.02  fof(f50,plain,(
% 2.02/1.02    ( ! [X2,X0,X3,X1] : (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f24])).
% 2.02/1.02  
% 2.02/1.02  fof(f10,axiom,(
% 2.02/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f22,plain,(
% 2.02/1.02    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.02/1.02    inference(ennf_transformation,[],[f10])).
% 2.02/1.02  
% 2.02/1.02  fof(f49,plain,(
% 2.02/1.02    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f22])).
% 2.02/1.02  
% 2.02/1.02  fof(f56,plain,(
% 2.02/1.02    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK2(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f37])).
% 2.02/1.02  
% 2.02/1.02  fof(f62,plain,(
% 2.02/1.02    ~v2_tex_2(sK5,sK4)),
% 2.02/1.02    inference(cnf_transformation,[],[f40])).
% 2.02/1.02  
% 2.02/1.02  fof(f1,axiom,(
% 2.02/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.02/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.02/1.02  
% 2.02/1.02  fof(f18,plain,(
% 2.02/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.02/1.02    inference(ennf_transformation,[],[f1])).
% 2.02/1.02  
% 2.02/1.02  fof(f41,plain,(
% 2.02/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.02/1.02    inference(cnf_transformation,[],[f18])).
% 2.02/1.02  
% 2.02/1.02  fof(f60,plain,(
% 2.02/1.02    v1_xboole_0(sK5)),
% 2.02/1.02    inference(cnf_transformation,[],[f40])).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1,plain,
% 2.02/1.02      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
% 2.02/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3658,plain,
% 2.02/1.02      ( r1_tarski(k1_setfam_1(k2_tarski(X0_48,X1_48)),X0_48) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4204,plain,
% 2.02/1.02      ( r1_tarski(k1_setfam_1(k2_tarski(X0_48,X1_48)),X0_48) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3658]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_2,plain,
% 2.02/1.02      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 2.02/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3657,plain,
% 2.02/1.02      ( ~ r1_tarski(X0_48,k1_xboole_0) | k1_xboole_0 = X0_48 ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4205,plain,
% 2.02/1.02      ( k1_xboole_0 = X0_48
% 2.02/1.02      | r1_tarski(X0_48,k1_xboole_0) != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3657]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4801,plain,
% 2.02/1.02      ( k1_setfam_1(k2_tarski(k1_xboole_0,X0_48)) = k1_xboole_0 ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4204,c_4205]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4,plain,
% 2.02/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.02/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3655,plain,
% 2.02/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_51)) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_4]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4207,plain,
% 2.02/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_51)) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3655]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.02/1.02      | k9_subset_1(X1,X2,X0) = k1_setfam_1(k2_tarski(X2,X0)) ),
% 2.02/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3656,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(X0_51))
% 2.02/1.02      | k9_subset_1(X0_51,X1_48,X0_48) = k1_setfam_1(k2_tarski(X1_48,X0_48)) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4206,plain,
% 2.02/1.02      ( k9_subset_1(X0_51,X0_48,X1_48) = k1_setfam_1(k2_tarski(X0_48,X1_48))
% 2.02/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(X0_51)) != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3656]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4746,plain,
% 2.02/1.02      ( k9_subset_1(X0_51,X0_48,k1_xboole_0) = k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4207,c_4206]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_10,plain,
% 2.02/1.02      ( v2_tex_2(X0,X1)
% 2.02/1.02      | ~ v3_pre_topc(X2,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0) ),
% 2.02/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_19,negated_conjecture,
% 2.02/1.02      ( l1_pre_topc(sK4) ),
% 2.02/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1054,plain,
% 2.02/1.02      ( v2_tex_2(X0,X1)
% 2.02/1.02      | ~ v3_pre_topc(X2,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK2(X1,X0)
% 2.02/1.02      | sK4 != X1 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1055,plain,
% 2.02/1.02      ( v2_tex_2(X0,sK4)
% 2.02/1.02      | ~ v3_pre_topc(X1,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k9_subset_1(u1_struct_0(sK4),X0,X1) != sK2(sK4,X0) ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_1054]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3634,plain,
% 2.02/1.02      ( v2_tex_2(X0_48,sK4)
% 2.02/1.02      | ~ v3_pre_topc(X1_48,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k9_subset_1(u1_struct_0(sK4),X0_48,X1_48) != sK2(sK4,X0_48) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_1055]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4233,plain,
% 2.02/1.02      ( k9_subset_1(u1_struct_0(sK4),X0_48,X1_48) != sK2(sK4,X0_48)
% 2.02/1.02      | v2_tex_2(X0_48,sK4) = iProver_top
% 2.02/1.02      | v3_pre_topc(X1_48,sK4) != iProver_top
% 2.02/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3634]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5315,plain,
% 2.02/1.02      ( k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
% 2.02/1.02      | v2_tex_2(X0_48,sK4) = iProver_top
% 2.02/1.02      | v3_pre_topc(k1_xboole_0,sK4) != iProver_top
% 2.02/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4746,c_4233]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_17,negated_conjecture,
% 2.02/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.02/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_24,plain,
% 2.02/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5,plain,
% 2.02/1.02      ( l1_pre_topc(sK0) ),
% 2.02/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_8,plain,
% 2.02/1.02      ( v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ v2_pre_topc(X1)
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | ~ l1_pre_topc(X3)
% 2.02/1.02      | k1_tops_1(X1,X0) != X0 ),
% 2.02/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_20,negated_conjecture,
% 2.02/1.02      ( v2_pre_topc(sK4) ),
% 2.02/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_243,plain,
% 2.02/1.02      ( v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | ~ l1_pre_topc(X3)
% 2.02/1.02      | k1_tops_1(X1,X0) != X0
% 2.02/1.02      | sK4 != X1 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_244,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ l1_pre_topc(X2)
% 2.02/1.02      | ~ l1_pre_topc(sK4)
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_243]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_248,plain,
% 2.02/1.02      ( ~ l1_pre_topc(X2)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.02/1.02      | v3_pre_topc(X0,sK4)
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0 ),
% 2.02/1.02      inference(global_propositional_subsumption,
% 2.02/1.02                [status(thm)],
% 2.02/1.02                [c_244,c_19]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_249,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ l1_pre_topc(X2)
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0 ),
% 2.02/1.02      inference(renaming,[status(thm)],[c_248]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_918,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0
% 2.02/1.02      | sK0 != X2 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_249]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_919,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_918]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3642,plain,
% 2.02/1.02      ( v3_pre_topc(X0_48,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.02      | k1_tops_1(sK4,X0_48) != X0_48 ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_919]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3663,plain,
% 2.02/1.02      ( v3_pre_topc(X0_48,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(sK4,X0_48) != X0_48
% 2.02/1.02      | ~ sP3_iProver_split ),
% 2.02/1.02      inference(splitting,
% 2.02/1.02                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.02/1.02                [c_3642]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3717,plain,
% 2.02/1.02      ( k1_tops_1(sK4,X0_48) != X0_48
% 2.02/1.02      | v3_pre_topc(X0_48,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | sP3_iProver_split != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3663]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3719,plain,
% 2.02/1.02      ( k1_tops_1(sK4,k1_xboole_0) != k1_xboole_0
% 2.02/1.02      | v3_pre_topc(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | sP3_iProver_split != iProver_top ),
% 2.02/1.02      inference(instantiation,[status(thm)],[c_3717]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1087,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0
% 2.02/1.02      | sK4 != X2 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_249]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1088,plain,
% 2.02/1.02      ( v3_pre_topc(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(sK4,X0) != X0 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_1087]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3632,plain,
% 2.02/1.02      ( v3_pre_topc(X0_48,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(sK4,X0_48) != X0_48 ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_1088]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3667,plain,
% 2.02/1.02      ( sP3_iProver_split | sP0_iProver_split ),
% 2.02/1.02      inference(splitting,
% 2.02/1.02                [splitting(split),new_symbols(definition,[])],
% 2.02/1.02                [c_3632]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3740,plain,
% 2.02/1.02      ( sP3_iProver_split = iProver_top
% 2.02/1.02      | sP0_iProver_split = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3667]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_9,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.02/1.02      | ~ v2_pre_topc(X3)
% 2.02/1.02      | ~ l1_pre_topc(X3)
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | k1_tops_1(X1,X0) = X0 ),
% 2.02/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_270,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | ~ l1_pre_topc(X3)
% 2.02/1.02      | k1_tops_1(X1,X0) = X0
% 2.02/1.02      | sK4 != X3 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_9,c_20]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_271,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | ~ l1_pre_topc(sK4)
% 2.02/1.02      | k1_tops_1(X1,X0) = X0 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_270]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_275,plain,
% 2.02/1.02      ( ~ l1_pre_topc(X1)
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | k1_tops_1(X1,X0) = X0 ),
% 2.02/1.02      inference(global_propositional_subsumption,
% 2.02/1.02                [status(thm)],
% 2.02/1.02                [c_271,c_19]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_276,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ l1_pre_topc(X1)
% 2.02/1.02      | k1_tops_1(X1,X0) = X0 ),
% 2.02/1.02      inference(renaming,[status(thm)],[c_275]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_774,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | k1_tops_1(X1,X0) = X0
% 2.02/1.02      | sK0 != X1 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_276]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_775,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0,sK0)
% 2.02/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.02      | k1_tops_1(sK0,X0) = X0 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_774]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3650,plain,
% 2.02/1.02      ( ~ v3_pre_topc(X0_48,sK0)
% 2.02/1.02      | ~ m1_subset_1(X1_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK0)))
% 2.02/1.02      | k1_tops_1(sK0,X0_48) = X0_48 ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_775]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3659,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ sP0_iProver_split ),
% 2.02/1.02      inference(splitting,
% 2.02/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.02/1.02                [c_3650]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4502,plain,
% 2.02/1.02      ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | ~ sP0_iProver_split ),
% 2.02/1.02      inference(instantiation,[status(thm)],[c_3659]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4503,plain,
% 2.02/1.02      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | sP0_iProver_split != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4502]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4514,plain,
% 2.02/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.02/1.02      inference(instantiation,[status(thm)],[c_3655]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4520,plain,
% 2.02/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_4514]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_7,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.02/1.02      | ~ l1_pre_topc(X1) ),
% 2.02/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1075,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | r1_tarski(k1_tops_1(X1,X0),X0)
% 2.02/1.02      | sK4 != X1 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_7,c_19]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1076,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | r1_tarski(k1_tops_1(sK4,X0),X0) ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_1075]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3633,plain,
% 2.02/1.02      ( ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | r1_tarski(k1_tops_1(sK4,X0_48),X0_48) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_1076]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4234,plain,
% 2.02/1.02      ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | r1_tarski(k1_tops_1(sK4,X0_48),X0_48) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3633]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4745,plain,
% 2.02/1.02      ( r1_tarski(k1_tops_1(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4207,c_4234]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5224,plain,
% 2.02/1.02      ( k1_tops_1(sK4,k1_xboole_0) = k1_xboole_0 ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4745,c_4205]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5772,plain,
% 2.02/1.02      ( m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
% 2.02/1.02      | v2_tex_2(X0_48,sK4) = iProver_top ),
% 2.02/1.02      inference(global_propositional_subsumption,
% 2.02/1.02                [status(thm)],
% 2.02/1.02                [c_5315,c_24,c_3719,c_3740,c_4503,c_4520,c_5224]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5773,plain,
% 2.02/1.02      ( k1_setfam_1(k2_tarski(X0_48,k1_xboole_0)) != sK2(sK4,X0_48)
% 2.02/1.02      | v2_tex_2(X0_48,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(renaming,[status(thm)],[c_5772]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5781,plain,
% 2.02/1.02      ( sK2(sK4,k1_xboole_0) != k1_xboole_0
% 2.02/1.02      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4801,c_5773]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_11,plain,
% 2.02/1.02      ( v2_tex_2(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | r1_tarski(sK2(X1,X0),X0)
% 2.02/1.02      | ~ l1_pre_topc(X1) ),
% 2.02/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1039,plain,
% 2.02/1.02      ( v2_tex_2(X0,X1)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.02/1.02      | r1_tarski(sK2(X1,X0),X0)
% 2.02/1.02      | sK4 != X1 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_19]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1040,plain,
% 2.02/1.02      ( v2_tex_2(X0,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | r1_tarski(sK2(sK4,X0),X0) ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_1039]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3635,plain,
% 2.02/1.02      ( v2_tex_2(X0_48,sK4)
% 2.02/1.02      | ~ m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.02/1.02      | r1_tarski(sK2(sK4,X0_48),X0_48) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_1040]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4232,plain,
% 2.02/1.02      ( v2_tex_2(X0_48,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(X0_48,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | r1_tarski(sK2(sK4,X0_48),X0_48) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3635]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5042,plain,
% 2.02/1.02      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_4207,c_4232]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1041,plain,
% 2.02/1.02      ( v2_tex_2(X0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | r1_tarski(sK2(sK4,X0),X0) = iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_1040]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_1043,plain,
% 2.02/1.02      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.02/1.02      | r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.02/1.02      inference(instantiation,[status(thm)],[c_1041]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_16,negated_conjecture,
% 2.02/1.02      ( ~ v2_tex_2(sK5,sK4) ),
% 2.02/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3654,negated_conjecture,
% 2.02/1.02      ( ~ v2_tex_2(sK5,sK4) ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_16]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4208,plain,
% 2.02/1.02      ( v2_tex_2(sK5,sK4) != iProver_top ),
% 2.02/1.02      inference(predicate_to_equality,[status(thm)],[c_3654]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_0,plain,
% 2.02/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.02/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_18,negated_conjecture,
% 2.02/1.02      ( v1_xboole_0(sK5) ),
% 2.02/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_237,plain,
% 2.02/1.02      ( sK5 != X0 | k1_xboole_0 = X0 ),
% 2.02/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_18]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_238,plain,
% 2.02/1.02      ( k1_xboole_0 = sK5 ),
% 2.02/1.02      inference(unflattening,[status(thm)],[c_237]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_3652,plain,
% 2.02/1.02      ( k1_xboole_0 = sK5 ),
% 2.02/1.02      inference(subtyping,[status(esa)],[c_238]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_4242,plain,
% 2.02/1.02      ( v2_tex_2(k1_xboole_0,sK4) != iProver_top ),
% 2.02/1.02      inference(light_normalisation,[status(thm)],[c_4208,c_3652]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5662,plain,
% 2.02/1.02      ( r1_tarski(sK2(sK4,k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.02/1.02      inference(global_propositional_subsumption,
% 2.02/1.02                [status(thm)],
% 2.02/1.02                [c_5042,c_1043,c_4242,c_4520]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5667,plain,
% 2.02/1.02      ( sK2(sK4,k1_xboole_0) = k1_xboole_0 ),
% 2.02/1.02      inference(superposition,[status(thm)],[c_5662,c_4205]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5782,plain,
% 2.02/1.02      ( k1_xboole_0 != k1_xboole_0
% 2.02/1.02      | v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(light_normalisation,[status(thm)],[c_5781,c_5667]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(c_5783,plain,
% 2.02/1.02      ( v2_tex_2(k1_xboole_0,sK4) = iProver_top
% 2.02/1.02      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.02/1.02      inference(equality_resolution_simp,[status(thm)],[c_5782]) ).
% 2.02/1.02  
% 2.02/1.02  cnf(contradiction,plain,
% 2.02/1.02      ( $false ),
% 2.02/1.02      inference(minisat,[status(thm)],[c_5783,c_4520,c_4242]) ).
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.02/1.02  
% 2.02/1.02  ------                               Statistics
% 2.02/1.02  
% 2.02/1.02  ------ General
% 2.02/1.02  
% 2.02/1.02  abstr_ref_over_cycles:                  0
% 2.02/1.02  abstr_ref_under_cycles:                 0
% 2.02/1.02  gc_basic_clause_elim:                   0
% 2.02/1.02  forced_gc_time:                         0
% 2.02/1.02  parsing_time:                           0.008
% 2.02/1.02  unif_index_cands_time:                  0.
% 2.02/1.02  unif_index_add_time:                    0.
% 2.02/1.02  orderings_time:                         0.
% 2.02/1.02  out_proof_time:                         0.008
% 2.02/1.02  total_time:                             0.199
% 2.02/1.02  num_of_symbols:                         58
% 2.02/1.02  num_of_terms:                           3984
% 2.02/1.02  
% 2.02/1.02  ------ Preprocessing
% 2.02/1.02  
% 2.02/1.02  num_of_splits:                          8
% 2.02/1.02  num_of_split_atoms:                     5
% 2.02/1.02  num_of_reused_defs:                     3
% 2.02/1.02  num_eq_ax_congr_red:                    29
% 2.02/1.02  num_of_sem_filtered_clauses:            5
% 2.02/1.02  num_of_subtypes:                        5
% 2.02/1.02  monotx_restored_types:                  0
% 2.02/1.02  sat_num_of_epr_types:                   0
% 2.02/1.02  sat_num_of_non_cyclic_types:            0
% 2.02/1.02  sat_guarded_non_collapsed_types:        1
% 2.02/1.02  num_pure_diseq_elim:                    0
% 2.02/1.02  simp_replaced_by:                       0
% 2.02/1.02  res_preprocessed:                       100
% 2.02/1.02  prep_upred:                             0
% 2.02/1.02  prep_unflattend:                        163
% 2.02/1.02  smt_new_axioms:                         0
% 2.02/1.02  pred_elim_cands:                        7
% 2.02/1.02  pred_elim:                              3
% 2.02/1.02  pred_elim_cl:                           -6
% 2.02/1.02  pred_elim_cycles:                       8
% 2.02/1.02  merged_defs:                            0
% 2.02/1.02  merged_defs_ncl:                        0
% 2.02/1.02  bin_hyper_res:                          0
% 2.02/1.02  prep_cycles:                            3
% 2.02/1.02  pred_elim_time:                         0.077
% 2.02/1.02  splitting_time:                         0.
% 2.02/1.02  sem_filter_time:                        0.
% 2.02/1.02  monotx_time:                            0.
% 2.02/1.02  subtype_inf_time:                       0.002
% 2.02/1.02  
% 2.02/1.02  ------ Problem properties
% 2.02/1.02  
% 2.02/1.02  clauses:                                35
% 2.02/1.02  conjectures:                            2
% 2.02/1.02  epr:                                    7
% 2.02/1.02  horn:                                   27
% 2.02/1.02  ground:                                 9
% 2.02/1.02  unary:                                  7
% 2.02/1.02  binary:                                 12
% 2.02/1.02  lits:                                   99
% 2.02/1.02  lits_eq:                                11
% 2.02/1.02  fd_pure:                                0
% 2.02/1.02  fd_pseudo:                              0
% 2.02/1.02  fd_cond:                                1
% 2.02/1.02  fd_pseudo_cond:                         0
% 2.02/1.02  ac_symbols:                             0
% 2.02/1.02  
% 2.02/1.02  ------ Propositional Solver
% 2.02/1.02  
% 2.02/1.02  prop_solver_calls:                      21
% 2.02/1.02  prop_fast_solver_calls:                 1391
% 2.02/1.02  smt_solver_calls:                       0
% 2.02/1.02  smt_fast_solver_calls:                  0
% 2.02/1.02  prop_num_of_clauses:                    1292
% 2.02/1.02  prop_preprocess_simplified:             4113
% 2.02/1.02  prop_fo_subsumed:                       21
% 2.02/1.02  prop_solver_time:                       0.
% 2.02/1.02  smt_solver_time:                        0.
% 2.02/1.02  smt_fast_solver_time:                   0.
% 2.02/1.02  prop_fast_solver_time:                  0.
% 2.02/1.02  prop_unsat_core_time:                   0.
% 2.02/1.02  
% 2.02/1.02  ------ QBF
% 2.02/1.02  
% 2.02/1.02  qbf_q_res:                              0
% 2.02/1.02  qbf_num_tautologies:                    0
% 2.02/1.02  qbf_prep_cycles:                        0
% 2.02/1.02  
% 2.02/1.02  ------ BMC1
% 2.02/1.02  
% 2.02/1.02  bmc1_current_bound:                     -1
% 2.02/1.02  bmc1_last_solved_bound:                 -1
% 2.02/1.02  bmc1_unsat_core_size:                   -1
% 2.02/1.02  bmc1_unsat_core_parents_size:           -1
% 2.02/1.02  bmc1_merge_next_fun:                    0
% 2.02/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.02/1.02  
% 2.02/1.02  ------ Instantiation
% 2.02/1.02  
% 2.02/1.02  inst_num_of_clauses:                    249
% 2.02/1.02  inst_num_in_passive:                    92
% 2.02/1.02  inst_num_in_active:                     157
% 2.02/1.02  inst_num_in_unprocessed:                0
% 2.02/1.02  inst_num_of_loops:                      190
% 2.02/1.02  inst_num_of_learning_restarts:          0
% 2.02/1.02  inst_num_moves_active_passive:          30
% 2.02/1.02  inst_lit_activity:                      0
% 2.02/1.02  inst_lit_activity_moves:                0
% 2.02/1.02  inst_num_tautologies:                   0
% 2.02/1.02  inst_num_prop_implied:                  0
% 2.02/1.02  inst_num_existing_simplified:           0
% 2.02/1.02  inst_num_eq_res_simplified:             0
% 2.02/1.02  inst_num_child_elim:                    0
% 2.02/1.02  inst_num_of_dismatching_blockings:      72
% 2.02/1.02  inst_num_of_non_proper_insts:           152
% 2.02/1.02  inst_num_of_duplicates:                 0
% 2.02/1.02  inst_inst_num_from_inst_to_res:         0
% 2.02/1.02  inst_dismatching_checking_time:         0.
% 2.02/1.02  
% 2.02/1.02  ------ Resolution
% 2.02/1.02  
% 2.02/1.02  res_num_of_clauses:                     0
% 2.02/1.02  res_num_in_passive:                     0
% 2.02/1.02  res_num_in_active:                      0
% 2.02/1.02  res_num_of_loops:                       103
% 2.02/1.02  res_forward_subset_subsumed:            2
% 2.02/1.02  res_backward_subset_subsumed:           0
% 2.02/1.02  res_forward_subsumed:                   0
% 2.02/1.02  res_backward_subsumed:                  0
% 2.02/1.02  res_forward_subsumption_resolution:     10
% 2.02/1.02  res_backward_subsumption_resolution:    0
% 2.02/1.02  res_clause_to_clause_subsumption:       180
% 2.02/1.02  res_orphan_elimination:                 0
% 2.02/1.02  res_tautology_del:                      14
% 2.02/1.02  res_num_eq_res_simplified:              0
% 2.02/1.02  res_num_sel_changes:                    0
% 2.02/1.02  res_moves_from_active_to_pass:          0
% 2.02/1.02  
% 2.02/1.02  ------ Superposition
% 2.02/1.02  
% 2.02/1.02  sup_time_total:                         0.
% 2.02/1.02  sup_time_generating:                    0.
% 2.02/1.02  sup_time_sim_full:                      0.
% 2.02/1.02  sup_time_sim_immed:                     0.
% 2.02/1.02  
% 2.02/1.02  sup_num_of_clauses:                     64
% 2.02/1.02  sup_num_in_active:                      36
% 2.02/1.02  sup_num_in_passive:                     28
% 2.02/1.02  sup_num_of_loops:                       37
% 2.02/1.02  sup_fw_superposition:                   19
% 2.02/1.02  sup_bw_superposition:                   20
% 2.02/1.02  sup_immediate_simplified:               3
% 2.02/1.02  sup_given_eliminated:                   0
% 2.02/1.02  comparisons_done:                       0
% 2.02/1.02  comparisons_avoided:                    0
% 2.02/1.02  
% 2.02/1.02  ------ Simplifications
% 2.02/1.02  
% 2.02/1.02  
% 2.02/1.02  sim_fw_subset_subsumed:                 1
% 2.02/1.02  sim_bw_subset_subsumed:                 2
% 2.02/1.02  sim_fw_subsumed:                        2
% 2.02/1.02  sim_bw_subsumed:                        0
% 2.02/1.02  sim_fw_subsumption_res:                 0
% 2.02/1.02  sim_bw_subsumption_res:                 0
% 2.02/1.02  sim_tautology_del:                      0
% 2.02/1.02  sim_eq_tautology_del:                   1
% 2.02/1.02  sim_eq_res_simp:                        1
% 2.02/1.02  sim_fw_demodulated:                     0
% 2.02/1.02  sim_bw_demodulated:                     2
% 2.02/1.02  sim_light_normalised:                   3
% 2.02/1.02  sim_joinable_taut:                      0
% 2.02/1.02  sim_joinable_simp:                      0
% 2.02/1.02  sim_ac_normalised:                      0
% 2.02/1.02  sim_smt_subsumption:                    0
% 2.02/1.02  
%------------------------------------------------------------------------------
