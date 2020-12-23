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
% DateTime   : Thu Dec  3 12:26:12 EST 2020

% Result     : Theorem 0.95s
% Output     : CNFRefutation 0.95s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 224 expanded)
%              Number of clauses        :   59 (  79 expanded)
%              Number of leaves         :   13 (  51 expanded)
%              Depth                    :   19
%              Number of atoms          :  323 ( 938 expanded)
%              Number of equality atoms :   79 ( 117 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f8,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f25,plain,(
    ! [X4,X1,X0] :
      ( ? [X5] :
          ( k9_subset_1(u1_struct_0(X0),X1,X5) = X4
          & v3_pre_topc(X5,X0)
          & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
        & v3_pre_topc(sK1(X0,X1,X4),X0)
        & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X0),X1,X3) != X2
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ! [X3] :
            ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
            | ~ v3_pre_topc(X3,X0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
        & r1_tarski(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( ! [X3] :
                    ( k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & r1_tarski(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X4] :
                  ( ( k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4
                    & v3_pre_topc(sK1(X0,X1,X4),X0)
                    & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r1_tarski(X4,X1)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | r1_tarski(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f11,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => v2_tex_2(X1,X0) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( ~ v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
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

fof(f29,plain,
    ( ~ v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28,f27])).

fof(f43,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f46,plain,(
    ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f42,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f45,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X1,X0)
      | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_1308,plain,
    ( X0_44 != X1_44
    | X2_44 != X1_44
    | X2_44 = X0_44 ),
    theory(equality)).

cnf(c_1728,plain,
    ( X0_44 != X1_44
    | k9_subset_1(u1_struct_0(sK2),X2_44,X3_44) != X1_44
    | k9_subset_1(u1_struct_0(sK2),X2_44,X3_44) = X0_44 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_1792,plain,
    ( X0_44 != k3_xboole_0(X1_44,X2_44)
    | k9_subset_1(u1_struct_0(sK2),X1_44,X2_44) = X0_44
    | k9_subset_1(u1_struct_0(sK2),X1_44,X2_44) != k3_xboole_0(X1_44,X2_44) ),
    inference(instantiation,[status(thm)],[c_1728])).

cnf(c_1793,plain,
    ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = k1_xboole_0
    | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1305,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_47))
    | k9_subset_1(X0_47,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1718,plain,
    ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
    inference(instantiation,[status(thm)],[c_1305])).

cnf(c_1721,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1718])).

cnf(c_1678,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) != X2_44
    | k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) = sK0(sK2,X0_44)
    | sK0(sK2,X0_44) != X2_44 ),
    inference(instantiation,[status(thm)],[c_1308])).

cnf(c_1679,plain,
    ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = sK0(sK2,k1_xboole_0)
    | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | sK0(sK2,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1678])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_1304,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1637,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_1304])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_15,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_378,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(sK0(X1,X0),X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_15])).

cnf(c_379,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,X0),X0) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_561,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X1
    | k1_xboole_0 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_379])).

cnf(c_562,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_561])).

cnf(c_570,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_562,c_4])).

cnf(c_1293,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_1541,plain,
    ( k1_xboole_0 = sK0(sK2,k1_xboole_0)
    | v2_tex_2(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1293])).

cnf(c_12,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1303,negated_conjecture,
    ( ~ v2_tex_2(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1533,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_14,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_229,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_230,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_229])).

cnf(c_1300,plain,
    ( k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_230])).

cnf(c_1551,plain,
    ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1533,c_1300])).

cnf(c_1557,plain,
    ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1541,c_1551])).

cnf(c_5,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_16,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_193,plain,
    ( v3_pre_topc(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_16])).

cnf(c_194,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_193])).

cnf(c_198,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(X0,sK2)
    | ~ v1_xboole_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_194,c_15])).

cnf(c_199,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(X0) ),
    inference(renaming,[status(thm)],[c_198])).

cnf(c_218,plain,
    ( v3_pre_topc(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_199,c_14])).

cnf(c_219,plain,
    ( v3_pre_topc(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_218])).

cnf(c_13,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_221,plain,
    ( v3_pre_topc(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_219,c_13])).

cnf(c_1301,plain,
    ( v3_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_221])).

cnf(c_1535,plain,
    ( v3_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_1544,plain,
    ( v3_pre_topc(k1_xboole_0,sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1535,c_1300])).

cnf(c_1606,plain,
    ( v3_pre_topc(k1_xboole_0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1544])).

cnf(c_1603,plain,
    ( ~ v2_tex_2(k1_xboole_0,sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1551])).

cnf(c_1,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_501,plain,
    ( k3_xboole_0(X0,X1) != X2
    | k1_xboole_0 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_2])).

cnf(c_502,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_1297,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0_44) ),
    inference(subtyping,[status(esa)],[c_502])).

cnf(c_1338,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1297])).

cnf(c_6,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_393,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_pre_topc(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_394,plain,
    ( v2_tex_2(X0,sK2)
    | ~ v3_pre_topc(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1298,plain,
    ( v2_tex_2(X0_44,sK2)
    | ~ v3_pre_topc(X1_44,sK2)
    | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) != sK0(sK2,X0_44) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_1336,plain,
    ( v2_tex_2(k1_xboole_0,sK2)
    | ~ v3_pre_topc(k1_xboole_0,sK2)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != sK0(sK2,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_1298])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1793,c_1721,c_1679,c_1637,c_1557,c_1606,c_1603,c_1338,c_1336])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:02:26 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.95/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.95/0.99  
% 0.95/0.99  ------  iProver source info
% 0.95/0.99  
% 0.95/0.99  git: date: 2020-06-30 10:37:57 +0100
% 0.95/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.95/0.99  git: non_committed_changes: false
% 0.95/0.99  git: last_make_outside_of_git: false
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     num_symb
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       true
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/0.99  --res_prop_simpl_new                    false
% 0.95/0.99  --res_prop_simpl_given                  true
% 0.95/0.99  --res_passive_queue_type                priority_queues
% 0.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.99  --res_passive_queues_freq               [15;5]
% 0.95/0.99  --res_forward_subs                      full
% 0.95/0.99  --res_backward_subs                     full
% 0.95/0.99  --res_forward_subs_resolution           true
% 0.95/0.99  --res_backward_subs_resolution          true
% 0.95/0.99  --res_orphan_elimination                true
% 0.95/0.99  --res_time_limit                        2.
% 0.95/0.99  --res_out_proof                         true
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Options
% 0.95/0.99  
% 0.95/0.99  --superposition_flag                    true
% 0.95/0.99  --sup_passive_queue_type                priority_queues
% 0.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.99  --demod_completeness_check              fast
% 0.95/0.99  --demod_use_ground                      true
% 0.95/0.99  --sup_to_prop_solver                    passive
% 0.95/0.99  --sup_prop_simpl_new                    true
% 0.95/0.99  --sup_prop_simpl_given                  true
% 0.95/0.99  --sup_fun_splitting                     false
% 0.95/0.99  --sup_smt_interval                      50000
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Simplification Setup
% 0.95/0.99  
% 0.95/0.99  --sup_indices_passive                   []
% 0.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_full_bw                           [BwDemod]
% 0.95/0.99  --sup_immed_triv                        [TrivRules]
% 0.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_immed_bw_main                     []
% 0.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  
% 0.95/0.99  ------ Combination Options
% 0.95/0.99  
% 0.95/0.99  --comb_res_mult                         3
% 0.95/0.99  --comb_sup_mult                         2
% 0.95/0.99  --comb_inst_mult                        10
% 0.95/0.99  
% 0.95/0.99  ------ Debug Options
% 0.95/0.99  
% 0.95/0.99  --dbg_backtrace                         false
% 0.95/0.99  --dbg_dump_prop_clauses                 false
% 0.95/0.99  --dbg_dump_prop_clauses_file            -
% 0.95/0.99  --dbg_out_stat                          false
% 0.95/0.99  ------ Parsing...
% 0.95/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.95/0.99  ------ Proving...
% 0.95/0.99  ------ Problem Properties 
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  clauses                                 13
% 0.95/0.99  conjectures                             2
% 0.95/0.99  EPR                                     3
% 0.95/0.99  Horn                                    11
% 0.95/0.99  unary                                   6
% 0.95/0.99  binary                                  2
% 0.95/0.99  lits                                    30
% 0.95/0.99  lits eq                                 6
% 0.95/0.99  fd_pure                                 0
% 0.95/0.99  fd_pseudo                               0
% 0.95/0.99  fd_cond                                 0
% 0.95/0.99  fd_pseudo_cond                          0
% 0.95/0.99  AC symbols                              0
% 0.95/0.99  
% 0.95/0.99  ------ Schedule dynamic 5 is on 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  ------ 
% 0.95/0.99  Current options:
% 0.95/0.99  ------ 
% 0.95/0.99  
% 0.95/0.99  ------ Input Options
% 0.95/0.99  
% 0.95/0.99  --out_options                           all
% 0.95/0.99  --tptp_safe_out                         true
% 0.95/0.99  --problem_path                          ""
% 0.95/0.99  --include_path                          ""
% 0.95/0.99  --clausifier                            res/vclausify_rel
% 0.95/0.99  --clausifier_options                    --mode clausify
% 0.95/0.99  --stdin                                 false
% 0.95/0.99  --stats_out                             all
% 0.95/0.99  
% 0.95/0.99  ------ General Options
% 0.95/0.99  
% 0.95/0.99  --fof                                   false
% 0.95/0.99  --time_out_real                         305.
% 0.95/0.99  --time_out_virtual                      -1.
% 0.95/0.99  --symbol_type_check                     false
% 0.95/0.99  --clausify_out                          false
% 0.95/0.99  --sig_cnt_out                           false
% 0.95/0.99  --trig_cnt_out                          false
% 0.95/0.99  --trig_cnt_out_tolerance                1.
% 0.95/0.99  --trig_cnt_out_sk_spl                   false
% 0.95/0.99  --abstr_cl_out                          false
% 0.95/0.99  
% 0.95/0.99  ------ Global Options
% 0.95/0.99  
% 0.95/0.99  --schedule                              default
% 0.95/0.99  --add_important_lit                     false
% 0.95/0.99  --prop_solver_per_cl                    1000
% 0.95/0.99  --min_unsat_core                        false
% 0.95/0.99  --soft_assumptions                      false
% 0.95/0.99  --soft_lemma_size                       3
% 0.95/0.99  --prop_impl_unit_size                   0
% 0.95/0.99  --prop_impl_unit                        []
% 0.95/0.99  --share_sel_clauses                     true
% 0.95/0.99  --reset_solvers                         false
% 0.95/0.99  --bc_imp_inh                            [conj_cone]
% 0.95/0.99  --conj_cone_tolerance                   3.
% 0.95/0.99  --extra_neg_conj                        none
% 0.95/0.99  --large_theory_mode                     true
% 0.95/0.99  --prolific_symb_bound                   200
% 0.95/0.99  --lt_threshold                          2000
% 0.95/0.99  --clause_weak_htbl                      true
% 0.95/0.99  --gc_record_bc_elim                     false
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing Options
% 0.95/0.99  
% 0.95/0.99  --preprocessing_flag                    true
% 0.95/0.99  --time_out_prep_mult                    0.1
% 0.95/0.99  --splitting_mode                        input
% 0.95/0.99  --splitting_grd                         true
% 0.95/0.99  --splitting_cvd                         false
% 0.95/0.99  --splitting_cvd_svl                     false
% 0.95/0.99  --splitting_nvd                         32
% 0.95/0.99  --sub_typing                            true
% 0.95/0.99  --prep_gs_sim                           true
% 0.95/0.99  --prep_unflatten                        true
% 0.95/0.99  --prep_res_sim                          true
% 0.95/0.99  --prep_upred                            true
% 0.95/0.99  --prep_sem_filter                       exhaustive
% 0.95/0.99  --prep_sem_filter_out                   false
% 0.95/0.99  --pred_elim                             true
% 0.95/0.99  --res_sim_input                         true
% 0.95/0.99  --eq_ax_congr_red                       true
% 0.95/0.99  --pure_diseq_elim                       true
% 0.95/0.99  --brand_transform                       false
% 0.95/0.99  --non_eq_to_eq                          false
% 0.95/0.99  --prep_def_merge                        true
% 0.95/0.99  --prep_def_merge_prop_impl              false
% 0.95/0.99  --prep_def_merge_mbd                    true
% 0.95/0.99  --prep_def_merge_tr_red                 false
% 0.95/0.99  --prep_def_merge_tr_cl                  false
% 0.95/0.99  --smt_preprocessing                     true
% 0.95/0.99  --smt_ac_axioms                         fast
% 0.95/0.99  --preprocessed_out                      false
% 0.95/0.99  --preprocessed_stats                    false
% 0.95/0.99  
% 0.95/0.99  ------ Abstraction refinement Options
% 0.95/0.99  
% 0.95/0.99  --abstr_ref                             []
% 0.95/0.99  --abstr_ref_prep                        false
% 0.95/0.99  --abstr_ref_until_sat                   false
% 0.95/0.99  --abstr_ref_sig_restrict                funpre
% 0.95/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 0.95/0.99  --abstr_ref_under                       []
% 0.95/0.99  
% 0.95/0.99  ------ SAT Options
% 0.95/0.99  
% 0.95/0.99  --sat_mode                              false
% 0.95/0.99  --sat_fm_restart_options                ""
% 0.95/0.99  --sat_gr_def                            false
% 0.95/0.99  --sat_epr_types                         true
% 0.95/0.99  --sat_non_cyclic_types                  false
% 0.95/0.99  --sat_finite_models                     false
% 0.95/0.99  --sat_fm_lemmas                         false
% 0.95/0.99  --sat_fm_prep                           false
% 0.95/0.99  --sat_fm_uc_incr                        true
% 0.95/0.99  --sat_out_model                         small
% 0.95/0.99  --sat_out_clauses                       false
% 0.95/0.99  
% 0.95/0.99  ------ QBF Options
% 0.95/0.99  
% 0.95/0.99  --qbf_mode                              false
% 0.95/0.99  --qbf_elim_univ                         false
% 0.95/0.99  --qbf_dom_inst                          none
% 0.95/0.99  --qbf_dom_pre_inst                      false
% 0.95/0.99  --qbf_sk_in                             false
% 0.95/0.99  --qbf_pred_elim                         true
% 0.95/0.99  --qbf_split                             512
% 0.95/0.99  
% 0.95/0.99  ------ BMC1 Options
% 0.95/0.99  
% 0.95/0.99  --bmc1_incremental                      false
% 0.95/0.99  --bmc1_axioms                           reachable_all
% 0.95/0.99  --bmc1_min_bound                        0
% 0.95/0.99  --bmc1_max_bound                        -1
% 0.95/0.99  --bmc1_max_bound_default                -1
% 0.95/0.99  --bmc1_symbol_reachability              true
% 0.95/0.99  --bmc1_property_lemmas                  false
% 0.95/0.99  --bmc1_k_induction                      false
% 0.95/0.99  --bmc1_non_equiv_states                 false
% 0.95/0.99  --bmc1_deadlock                         false
% 0.95/0.99  --bmc1_ucm                              false
% 0.95/0.99  --bmc1_add_unsat_core                   none
% 0.95/0.99  --bmc1_unsat_core_children              false
% 0.95/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 0.95/0.99  --bmc1_out_stat                         full
% 0.95/0.99  --bmc1_ground_init                      false
% 0.95/0.99  --bmc1_pre_inst_next_state              false
% 0.95/0.99  --bmc1_pre_inst_state                   false
% 0.95/0.99  --bmc1_pre_inst_reach_state             false
% 0.95/0.99  --bmc1_out_unsat_core                   false
% 0.95/0.99  --bmc1_aig_witness_out                  false
% 0.95/0.99  --bmc1_verbose                          false
% 0.95/0.99  --bmc1_dump_clauses_tptp                false
% 0.95/0.99  --bmc1_dump_unsat_core_tptp             false
% 0.95/0.99  --bmc1_dump_file                        -
% 0.95/0.99  --bmc1_ucm_expand_uc_limit              128
% 0.95/0.99  --bmc1_ucm_n_expand_iterations          6
% 0.95/0.99  --bmc1_ucm_extend_mode                  1
% 0.95/0.99  --bmc1_ucm_init_mode                    2
% 0.95/0.99  --bmc1_ucm_cone_mode                    none
% 0.95/0.99  --bmc1_ucm_reduced_relation_type        0
% 0.95/0.99  --bmc1_ucm_relax_model                  4
% 0.95/0.99  --bmc1_ucm_full_tr_after_sat            true
% 0.95/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 0.95/0.99  --bmc1_ucm_layered_model                none
% 0.95/0.99  --bmc1_ucm_max_lemma_size               10
% 0.95/0.99  
% 0.95/0.99  ------ AIG Options
% 0.95/0.99  
% 0.95/0.99  --aig_mode                              false
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation Options
% 0.95/0.99  
% 0.95/0.99  --instantiation_flag                    true
% 0.95/0.99  --inst_sos_flag                         false
% 0.95/0.99  --inst_sos_phase                        true
% 0.95/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.95/0.99  --inst_lit_sel_side                     none
% 0.95/0.99  --inst_solver_per_active                1400
% 0.95/0.99  --inst_solver_calls_frac                1.
% 0.95/0.99  --inst_passive_queue_type               priority_queues
% 0.95/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.95/0.99  --inst_passive_queues_freq              [25;2]
% 0.95/0.99  --inst_dismatching                      true
% 0.95/0.99  --inst_eager_unprocessed_to_passive     true
% 0.95/0.99  --inst_prop_sim_given                   true
% 0.95/0.99  --inst_prop_sim_new                     false
% 0.95/0.99  --inst_subs_new                         false
% 0.95/0.99  --inst_eq_res_simp                      false
% 0.95/0.99  --inst_subs_given                       false
% 0.95/0.99  --inst_orphan_elimination               true
% 0.95/0.99  --inst_learning_loop_flag               true
% 0.95/0.99  --inst_learning_start                   3000
% 0.95/0.99  --inst_learning_factor                  2
% 0.95/0.99  --inst_start_prop_sim_after_learn       3
% 0.95/0.99  --inst_sel_renew                        solver
% 0.95/0.99  --inst_lit_activity_flag                true
% 0.95/0.99  --inst_restr_to_given                   false
% 0.95/0.99  --inst_activity_threshold               500
% 0.95/0.99  --inst_out_proof                        true
% 0.95/0.99  
% 0.95/0.99  ------ Resolution Options
% 0.95/0.99  
% 0.95/0.99  --resolution_flag                       false
% 0.95/0.99  --res_lit_sel                           adaptive
% 0.95/0.99  --res_lit_sel_side                      none
% 0.95/0.99  --res_ordering                          kbo
% 0.95/0.99  --res_to_prop_solver                    active
% 0.95/0.99  --res_prop_simpl_new                    false
% 0.95/0.99  --res_prop_simpl_given                  true
% 0.95/0.99  --res_passive_queue_type                priority_queues
% 0.95/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.95/0.99  --res_passive_queues_freq               [15;5]
% 0.95/0.99  --res_forward_subs                      full
% 0.95/0.99  --res_backward_subs                     full
% 0.95/0.99  --res_forward_subs_resolution           true
% 0.95/0.99  --res_backward_subs_resolution          true
% 0.95/0.99  --res_orphan_elimination                true
% 0.95/0.99  --res_time_limit                        2.
% 0.95/0.99  --res_out_proof                         true
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Options
% 0.95/0.99  
% 0.95/0.99  --superposition_flag                    true
% 0.95/0.99  --sup_passive_queue_type                priority_queues
% 0.95/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.95/0.99  --sup_passive_queues_freq               [8;1;4]
% 0.95/0.99  --demod_completeness_check              fast
% 0.95/0.99  --demod_use_ground                      true
% 0.95/0.99  --sup_to_prop_solver                    passive
% 0.95/0.99  --sup_prop_simpl_new                    true
% 0.95/0.99  --sup_prop_simpl_given                  true
% 0.95/0.99  --sup_fun_splitting                     false
% 0.95/0.99  --sup_smt_interval                      50000
% 0.95/0.99  
% 0.95/0.99  ------ Superposition Simplification Setup
% 0.95/0.99  
% 0.95/0.99  --sup_indices_passive                   []
% 0.95/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.95/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 0.95/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_full_bw                           [BwDemod]
% 0.95/0.99  --sup_immed_triv                        [TrivRules]
% 0.95/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.95/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_immed_bw_main                     []
% 0.95/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 0.95/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.95/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.95/0.99  
% 0.95/0.99  ------ Combination Options
% 0.95/0.99  
% 0.95/0.99  --comb_res_mult                         3
% 0.95/0.99  --comb_sup_mult                         2
% 0.95/0.99  --comb_inst_mult                        10
% 0.95/0.99  
% 0.95/0.99  ------ Debug Options
% 0.95/0.99  
% 0.95/0.99  --dbg_backtrace                         false
% 0.95/0.99  --dbg_dump_prop_clauses                 false
% 0.95/0.99  --dbg_dump_prop_clauses_file            -
% 0.95/0.99  --dbg_out_stat                          false
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  ------ Proving...
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  % SZS status Theorem for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  fof(f4,axiom,(
% 0.95/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f15,plain,(
% 0.95/0.99    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f4])).
% 0.95/0.99  
% 0.95/0.99  fof(f33,plain,(
% 0.95/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.95/0.99    inference(cnf_transformation,[],[f15])).
% 0.95/0.99  
% 0.95/0.99  fof(f5,axiom,(
% 0.95/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f34,plain,(
% 0.95/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.95/0.99    inference(cnf_transformation,[],[f5])).
% 0.95/0.99  
% 0.95/0.99  fof(f3,axiom,(
% 0.95/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f14,plain,(
% 0.95/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.95/0.99    inference(ennf_transformation,[],[f3])).
% 0.95/0.99  
% 0.95/0.99  fof(f32,plain,(
% 0.95/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f14])).
% 0.95/0.99  
% 0.95/0.99  fof(f8,axiom,(
% 0.95/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0))) & r1_tarski(X2,X1))))))),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f18,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((? [X3] : ((k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f8])).
% 0.95/0.99  
% 0.95/0.99  fof(f19,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f18])).
% 0.95/0.99  
% 0.95/0.99  fof(f22,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (? [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(nnf_transformation,[],[f19])).
% 0.95/0.99  
% 0.95/0.99  fof(f23,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(rectify,[],[f22])).
% 0.95/0.99  
% 0.95/0.99  fof(f25,plain,(
% 0.95/0.99    ! [X4,X1,X0] : (? [X5] : (k9_subset_1(u1_struct_0(X0),X1,X5) = X4 & v3_pre_topc(X5,X0) & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f24,plain,(
% 0.95/0.99    ! [X1,X0] : (? [X2] : (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != X2 | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f26,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & r1_tarski(sK0(X0,X1),X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X4] : ((k9_subset_1(u1_struct_0(X0),X1,sK1(X0,X1,X4)) = X4 & v3_pre_topc(sK1(X0,X1,X4),X0) & m1_subset_1(sK1(X0,X1,X4),k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X4,X1) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f25,f24])).
% 0.95/0.99  
% 0.95/0.99  fof(f40,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | r1_tarski(sK0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f26])).
% 0.95/0.99  
% 0.95/0.99  fof(f9,conjecture,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f10,negated_conjecture,(
% 0.95/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.95/0.99    inference(negated_conjecture,[],[f9])).
% 0.95/0.99  
% 0.95/0.99  fof(f11,plain,(
% 0.95/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.95/0.99    inference(pure_predicate_removal,[],[f10])).
% 0.95/0.99  
% 0.95/0.99  fof(f20,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f11])).
% 0.95/0.99  
% 0.95/0.99  fof(f21,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f20])).
% 0.95/0.99  
% 0.95/0.99  fof(f28,plain,(
% 0.95/0.99    ( ! [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (~v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f27,plain,(
% 0.95/0.99    ? [X0] : (? [X1] : (~v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (~v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 0.95/0.99    introduced(choice_axiom,[])).
% 0.95/0.99  
% 0.95/0.99  fof(f29,plain,(
% 0.95/0.99    (~v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)),
% 0.95/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f28,f27])).
% 0.95/0.99  
% 0.95/0.99  fof(f43,plain,(
% 0.95/0.99    l1_pre_topc(sK2)),
% 0.95/0.99    inference(cnf_transformation,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f46,plain,(
% 0.95/0.99    ~v2_tex_2(sK3,sK2)),
% 0.95/0.99    inference(cnf_transformation,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f1,axiom,(
% 0.95/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f13,plain,(
% 0.95/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.95/0.99    inference(ennf_transformation,[],[f1])).
% 0.95/0.99  
% 0.95/0.99  fof(f30,plain,(
% 0.95/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f13])).
% 0.95/0.99  
% 0.95/0.99  fof(f44,plain,(
% 0.95/0.99    v1_xboole_0(sK3)),
% 0.95/0.99    inference(cnf_transformation,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f7,axiom,(
% 0.95/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v3_pre_topc(X1,X0))))),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f16,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.95/0.99    inference(ennf_transformation,[],[f7])).
% 0.95/0.99  
% 0.95/0.99  fof(f17,plain,(
% 0.95/0.99    ! [X0] : (! [X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.95/0.99    inference(flattening,[],[f16])).
% 0.95/0.99  
% 0.95/0.99  fof(f35,plain,(
% 0.95/0.99    ( ! [X0,X1] : (v3_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f17])).
% 0.95/0.99  
% 0.95/0.99  fof(f42,plain,(
% 0.95/0.99    v2_pre_topc(sK2)),
% 0.95/0.99    inference(cnf_transformation,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f45,plain,(
% 0.95/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.95/0.99    inference(cnf_transformation,[],[f29])).
% 0.95/0.99  
% 0.95/0.99  fof(f2,axiom,(
% 0.95/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.95/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 0.95/0.99  
% 0.95/0.99  fof(f31,plain,(
% 0.95/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f2])).
% 0.95/0.99  
% 0.95/0.99  fof(f41,plain,(
% 0.95/0.99    ( ! [X0,X3,X1] : (v2_tex_2(X1,X0) | k9_subset_1(u1_struct_0(X0),X1,X3) != sK0(X0,X1) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.95/0.99    inference(cnf_transformation,[],[f26])).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1308,plain,
% 0.95/0.99      ( X0_44 != X1_44 | X2_44 != X1_44 | X2_44 = X0_44 ),
% 0.95/0.99      theory(equality) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1728,plain,
% 0.95/0.99      ( X0_44 != X1_44
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X2_44,X3_44) != X1_44
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X2_44,X3_44) = X0_44 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1308]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1792,plain,
% 0.95/0.99      ( X0_44 != k3_xboole_0(X1_44,X2_44)
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X1_44,X2_44) = X0_44
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X1_44,X2_44) != k3_xboole_0(X1_44,X2_44) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1728]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1793,plain,
% 0.95/0.99      ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != k3_xboole_0(k1_xboole_0,k1_xboole_0)
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = k1_xboole_0
% 0.95/0.99      | k1_xboole_0 != k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1792]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_3,plain,
% 0.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 0.95/0.99      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f33]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1305,plain,
% 0.95/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(X0_47))
% 0.95/0.99      | k9_subset_1(X0_47,X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1718,plain,
% 0.95/0.99      ( ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X1_44,X0_44) = k3_xboole_0(X1_44,X0_44) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1305]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1721,plain,
% 0.95/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1718]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1678,plain,
% 0.95/0.99      ( k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) != X2_44
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) = sK0(sK2,X0_44)
% 0.95/0.99      | sK0(sK2,X0_44) != X2_44 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1308]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1679,plain,
% 0.95/0.99      ( k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) = sK0(sK2,k1_xboole_0)
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 0.95/0.99      | sK0(sK2,k1_xboole_0) != k1_xboole_0 ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1678]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_4,plain,
% 0.95/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.95/0.99      inference(cnf_transformation,[],[f34]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1304,plain,
% 0.95/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0_47)) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_4]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1637,plain,
% 0.95/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1304]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_2,plain,
% 0.95/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 0.95/0.99      inference(cnf_transformation,[],[f32]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_7,plain,
% 0.95/0.99      ( v2_tex_2(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | r1_tarski(sK0(X1,X0),X0)
% 0.95/0.99      | ~ l1_pre_topc(X1) ),
% 0.95/0.99      inference(cnf_transformation,[],[f40]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_15,negated_conjecture,
% 0.95/0.99      ( l1_pre_topc(sK2) ),
% 0.95/0.99      inference(cnf_transformation,[],[f43]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_378,plain,
% 0.95/0.99      ( v2_tex_2(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | r1_tarski(sK0(X1,X0),X0)
% 0.95/0.99      | sK2 != X1 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_15]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_379,plain,
% 0.95/0.99      ( v2_tex_2(X0,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | r1_tarski(sK0(sK2,X0),X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_561,plain,
% 0.95/0.99      ( v2_tex_2(X0,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | sK0(sK2,X0) != X1
% 0.95/0.99      | k1_xboole_0 != X0
% 0.95/0.99      | k1_xboole_0 = X1 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_379]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_562,plain,
% 0.95/0.99      ( v2_tex_2(k1_xboole_0,sK2)
% 0.95/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_561]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_570,plain,
% 0.95/0.99      ( v2_tex_2(k1_xboole_0,sK2) | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
% 0.95/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_562,c_4]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1293,plain,
% 0.95/0.99      ( v2_tex_2(k1_xboole_0,sK2) | k1_xboole_0 = sK0(sK2,k1_xboole_0) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_570]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1541,plain,
% 0.95/0.99      ( k1_xboole_0 = sK0(sK2,k1_xboole_0)
% 0.95/0.99      | v2_tex_2(k1_xboole_0,sK2) = iProver_top ),
% 0.95/0.99      inference(predicate_to_equality,[status(thm)],[c_1293]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_12,negated_conjecture,
% 0.95/0.99      ( ~ v2_tex_2(sK3,sK2) ),
% 0.95/0.99      inference(cnf_transformation,[],[f46]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1303,negated_conjecture,
% 0.95/0.99      ( ~ v2_tex_2(sK3,sK2) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1533,plain,
% 0.95/0.99      ( v2_tex_2(sK3,sK2) != iProver_top ),
% 0.95/0.99      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_0,plain,
% 0.95/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 0.95/0.99      inference(cnf_transformation,[],[f30]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_14,negated_conjecture,
% 0.95/0.99      ( v1_xboole_0(sK3) ),
% 0.95/0.99      inference(cnf_transformation,[],[f44]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_229,plain,
% 0.95/0.99      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_230,plain,
% 0.95/0.99      ( k1_xboole_0 = sK3 ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_229]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1300,plain,
% 0.95/0.99      ( k1_xboole_0 = sK3 ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_230]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1551,plain,
% 0.95/0.99      ( v2_tex_2(k1_xboole_0,sK2) != iProver_top ),
% 0.95/0.99      inference(light_normalisation,[status(thm)],[c_1533,c_1300]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1557,plain,
% 0.95/0.99      ( sK0(sK2,k1_xboole_0) = k1_xboole_0 ),
% 0.95/0.99      inference(forward_subsumption_resolution,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_1541,c_1551]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_5,plain,
% 0.95/0.99      ( v3_pre_topc(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ v2_pre_topc(X1)
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | ~ v1_xboole_0(X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f35]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_16,negated_conjecture,
% 0.95/0.99      ( v2_pre_topc(sK2) ),
% 0.95/0.99      inference(cnf_transformation,[],[f42]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_193,plain,
% 0.95/0.99      ( v3_pre_topc(X0,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | ~ v1_xboole_0(X0)
% 0.95/0.99      | sK2 != X1 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_16]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_194,plain,
% 0.95/0.99      ( v3_pre_topc(X0,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | ~ l1_pre_topc(sK2)
% 0.95/0.99      | ~ v1_xboole_0(X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_193]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_198,plain,
% 0.95/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | v3_pre_topc(X0,sK2)
% 0.95/0.99      | ~ v1_xboole_0(X0) ),
% 0.95/0.99      inference(global_propositional_subsumption,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_194,c_15]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_199,plain,
% 0.95/0.99      ( v3_pre_topc(X0,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | ~ v1_xboole_0(X0) ),
% 0.95/0.99      inference(renaming,[status(thm)],[c_198]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_218,plain,
% 0.95/0.99      ( v3_pre_topc(X0,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | sK3 != X0 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_199,c_14]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_219,plain,
% 0.95/0.99      ( v3_pre_topc(sK3,sK2)
% 0.95/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_218]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_13,negated_conjecture,
% 0.95/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 0.95/0.99      inference(cnf_transformation,[],[f45]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_221,plain,
% 0.95/0.99      ( v3_pre_topc(sK3,sK2) ),
% 0.95/0.99      inference(global_propositional_subsumption,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_219,c_13]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1301,plain,
% 0.95/0.99      ( v3_pre_topc(sK3,sK2) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_221]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1535,plain,
% 0.95/0.99      ( v3_pre_topc(sK3,sK2) = iProver_top ),
% 0.95/0.99      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1544,plain,
% 0.95/0.99      ( v3_pre_topc(k1_xboole_0,sK2) = iProver_top ),
% 0.95/0.99      inference(light_normalisation,[status(thm)],[c_1535,c_1300]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1606,plain,
% 0.95/0.99      ( v3_pre_topc(k1_xboole_0,sK2) ),
% 0.95/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1544]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1603,plain,
% 0.95/0.99      ( ~ v2_tex_2(k1_xboole_0,sK2) ),
% 0.95/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1551]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1,plain,
% 0.95/0.99      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f31]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_501,plain,
% 0.95/0.99      ( k3_xboole_0(X0,X1) != X2 | k1_xboole_0 != X0 | k1_xboole_0 = X2 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_2]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_502,plain,
% 0.95/0.99      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_501]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1297,plain,
% 0.95/0.99      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0_44) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_502]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1338,plain,
% 0.95/0.99      ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1297]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_6,plain,
% 0.95/0.99      ( v2_tex_2(X0,X1)
% 0.95/0.99      | ~ v3_pre_topc(X2,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ l1_pre_topc(X1)
% 0.95/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0) ),
% 0.95/0.99      inference(cnf_transformation,[],[f41]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_393,plain,
% 0.95/0.99      ( v2_tex_2(X0,X1)
% 0.95/0.99      | ~ v3_pre_topc(X2,X1)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(X1),X0,X2) != sK0(X1,X0)
% 0.95/0.99      | sK2 != X1 ),
% 0.95/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_394,plain,
% 0.95/0.99      ( v2_tex_2(X0,sK2)
% 0.95/0.99      | ~ v3_pre_topc(X1,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X0,X1) != sK0(sK2,X0) ),
% 0.95/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1298,plain,
% 0.95/0.99      ( v2_tex_2(X0_44,sK2)
% 0.95/0.99      | ~ v3_pre_topc(X1_44,sK2)
% 0.95/0.99      | ~ m1_subset_1(X0_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | ~ m1_subset_1(X1_44,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),X0_44,X1_44) != sK0(sK2,X0_44) ),
% 0.95/0.99      inference(subtyping,[status(esa)],[c_394]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(c_1336,plain,
% 0.95/0.99      ( v2_tex_2(k1_xboole_0,sK2)
% 0.95/0.99      | ~ v3_pre_topc(k1_xboole_0,sK2)
% 0.95/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 0.95/0.99      | k9_subset_1(u1_struct_0(sK2),k1_xboole_0,k1_xboole_0) != sK0(sK2,k1_xboole_0) ),
% 0.95/0.99      inference(instantiation,[status(thm)],[c_1298]) ).
% 0.95/0.99  
% 0.95/0.99  cnf(contradiction,plain,
% 0.95/0.99      ( $false ),
% 0.95/0.99      inference(minisat,
% 0.95/0.99                [status(thm)],
% 0.95/0.99                [c_1793,c_1721,c_1679,c_1637,c_1557,c_1606,c_1603,c_1338,
% 0.95/0.99                 c_1336]) ).
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 0.95/0.99  
% 0.95/0.99  ------                               Statistics
% 0.95/0.99  
% 0.95/0.99  ------ General
% 0.95/0.99  
% 0.95/0.99  abstr_ref_over_cycles:                  0
% 0.95/0.99  abstr_ref_under_cycles:                 0
% 0.95/0.99  gc_basic_clause_elim:                   0
% 0.95/0.99  forced_gc_time:                         0
% 0.95/0.99  parsing_time:                           0.011
% 0.95/0.99  unif_index_cands_time:                  0.
% 0.95/0.99  unif_index_add_time:                    0.
% 0.95/0.99  orderings_time:                         0.
% 0.95/0.99  out_proof_time:                         0.008
% 0.95/0.99  total_time:                             0.078
% 0.95/0.99  num_of_symbols:                         51
% 0.95/0.99  num_of_terms:                           1363
% 0.95/0.99  
% 0.95/0.99  ------ Preprocessing
% 0.95/0.99  
% 0.95/0.99  num_of_splits:                          0
% 0.95/0.99  num_of_split_atoms:                     0
% 0.95/0.99  num_of_reused_defs:                     0
% 0.95/0.99  num_eq_ax_congr_red:                    23
% 0.95/0.99  num_of_sem_filtered_clauses:            1
% 0.95/0.99  num_of_subtypes:                        4
% 0.95/0.99  monotx_restored_types:                  0
% 0.95/0.99  sat_num_of_epr_types:                   0
% 0.95/0.99  sat_num_of_non_cyclic_types:            0
% 0.95/0.99  sat_guarded_non_collapsed_types:        0
% 0.95/0.99  num_pure_diseq_elim:                    0
% 0.95/0.99  simp_replaced_by:                       0
% 0.95/0.99  res_preprocessed:                       75
% 0.95/0.99  prep_upred:                             0
% 0.95/0.99  prep_unflattend:                        45
% 0.95/0.99  smt_new_axioms:                         0
% 0.95/0.99  pred_elim_cands:                        3
% 0.95/0.99  pred_elim:                              4
% 0.95/0.99  pred_elim_cl:                           4
% 0.95/0.99  pred_elim_cycles:                       10
% 0.95/0.99  merged_defs:                            0
% 0.95/0.99  merged_defs_ncl:                        0
% 0.95/0.99  bin_hyper_res:                          0
% 0.95/0.99  prep_cycles:                            4
% 0.95/0.99  pred_elim_time:                         0.019
% 0.95/0.99  splitting_time:                         0.
% 0.95/0.99  sem_filter_time:                        0.
% 0.95/0.99  monotx_time:                            0.
% 0.95/0.99  subtype_inf_time:                       0.
% 0.95/0.99  
% 0.95/0.99  ------ Problem properties
% 0.95/0.99  
% 0.95/0.99  clauses:                                13
% 0.95/0.99  conjectures:                            2
% 0.95/0.99  epr:                                    3
% 0.95/0.99  horn:                                   11
% 0.95/0.99  ground:                                 5
% 0.95/0.99  unary:                                  6
% 0.95/0.99  binary:                                 2
% 0.95/0.99  lits:                                   30
% 0.95/0.99  lits_eq:                                6
% 0.95/0.99  fd_pure:                                0
% 0.95/0.99  fd_pseudo:                              0
% 0.95/0.99  fd_cond:                                0
% 0.95/0.99  fd_pseudo_cond:                         0
% 0.95/0.99  ac_symbols:                             0
% 0.95/0.99  
% 0.95/0.99  ------ Propositional Solver
% 0.95/0.99  
% 0.95/0.99  prop_solver_calls:                      25
% 0.95/0.99  prop_fast_solver_calls:                 624
% 0.95/0.99  smt_solver_calls:                       0
% 0.95/0.99  smt_fast_solver_calls:                  0
% 0.95/0.99  prop_num_of_clauses:                    323
% 0.95/0.99  prop_preprocess_simplified:             2144
% 0.95/0.99  prop_fo_subsumed:                       15
% 0.95/0.99  prop_solver_time:                       0.
% 0.95/0.99  smt_solver_time:                        0.
% 0.95/0.99  smt_fast_solver_time:                   0.
% 0.95/0.99  prop_fast_solver_time:                  0.
% 0.95/0.99  prop_unsat_core_time:                   0.
% 0.95/0.99  
% 0.95/0.99  ------ QBF
% 0.95/0.99  
% 0.95/0.99  qbf_q_res:                              0
% 0.95/0.99  qbf_num_tautologies:                    0
% 0.95/0.99  qbf_prep_cycles:                        0
% 0.95/0.99  
% 0.95/0.99  ------ BMC1
% 0.95/0.99  
% 0.95/0.99  bmc1_current_bound:                     -1
% 0.95/0.99  bmc1_last_solved_bound:                 -1
% 0.95/0.99  bmc1_unsat_core_size:                   -1
% 0.95/0.99  bmc1_unsat_core_parents_size:           -1
% 0.95/0.99  bmc1_merge_next_fun:                    0
% 0.95/0.99  bmc1_unsat_core_clauses_time:           0.
% 0.95/0.99  
% 0.95/0.99  ------ Instantiation
% 0.95/0.99  
% 0.95/0.99  inst_num_of_clauses:                    53
% 0.95/0.99  inst_num_in_passive:                    4
% 0.95/0.99  inst_num_in_active:                     41
% 0.95/0.99  inst_num_in_unprocessed:                7
% 0.95/0.99  inst_num_of_loops:                      46
% 0.95/0.99  inst_num_of_learning_restarts:          0
% 0.95/0.99  inst_num_moves_active_passive:          2
% 0.95/0.99  inst_lit_activity:                      0
% 0.95/0.99  inst_lit_activity_moves:                0
% 0.95/0.99  inst_num_tautologies:                   0
% 0.95/0.99  inst_num_prop_implied:                  0
% 0.95/0.99  inst_num_existing_simplified:           0
% 0.95/0.99  inst_num_eq_res_simplified:             0
% 0.95/0.99  inst_num_child_elim:                    0
% 0.95/0.99  inst_num_of_dismatching_blockings:      5
% 0.95/0.99  inst_num_of_non_proper_insts:           36
% 0.95/0.99  inst_num_of_duplicates:                 0
% 0.95/0.99  inst_inst_num_from_inst_to_res:         0
% 0.95/0.99  inst_dismatching_checking_time:         0.
% 0.95/0.99  
% 0.95/0.99  ------ Resolution
% 0.95/0.99  
% 0.95/0.99  res_num_of_clauses:                     0
% 0.95/0.99  res_num_in_passive:                     0
% 0.95/0.99  res_num_in_active:                      0
% 0.95/0.99  res_num_of_loops:                       79
% 0.95/0.99  res_forward_subset_subsumed:            0
% 0.95/0.99  res_backward_subset_subsumed:           0
% 0.95/0.99  res_forward_subsumed:                   0
% 0.95/0.99  res_backward_subsumed:                  0
% 0.95/0.99  res_forward_subsumption_resolution:     7
% 0.95/0.99  res_backward_subsumption_resolution:    0
% 0.95/0.99  res_clause_to_clause_subsumption:       84
% 0.95/0.99  res_orphan_elimination:                 0
% 0.95/0.99  res_tautology_del:                      4
% 0.95/0.99  res_num_eq_res_simplified:              0
% 0.95/0.99  res_num_sel_changes:                    0
% 0.95/0.99  res_moves_from_active_to_pass:          0
% 0.95/0.99  
% 0.95/0.99  ------ Superposition
% 0.95/0.99  
% 0.95/0.99  sup_time_total:                         0.
% 0.95/0.99  sup_time_generating:                    0.
% 0.95/0.99  sup_time_sim_full:                      0.
% 0.95/0.99  sup_time_sim_immed:                     0.
% 0.95/0.99  
% 0.95/0.99  sup_num_of_clauses:                     13
% 0.95/0.99  sup_num_in_active:                      8
% 0.95/0.99  sup_num_in_passive:                     5
% 0.95/0.99  sup_num_of_loops:                       8
% 0.95/0.99  sup_fw_superposition:                   0
% 0.95/0.99  sup_bw_superposition:                   1
% 0.95/0.99  sup_immediate_simplified:               0
% 0.95/0.99  sup_given_eliminated:                   0
% 0.95/0.99  comparisons_done:                       0
% 0.95/0.99  comparisons_avoided:                    0
% 0.95/0.99  
% 0.95/0.99  ------ Simplifications
% 0.95/0.99  
% 0.95/0.99  
% 0.95/0.99  sim_fw_subset_subsumed:                 0
% 0.95/0.99  sim_bw_subset_subsumed:                 0
% 0.95/0.99  sim_fw_subsumed:                        1
% 0.95/0.99  sim_bw_subsumed:                        0
% 0.95/0.99  sim_fw_subsumption_res:                 1
% 0.95/0.99  sim_bw_subsumption_res:                 0
% 0.95/0.99  sim_tautology_del:                      0
% 0.95/0.99  sim_eq_tautology_del:                   0
% 0.95/0.99  sim_eq_res_simp:                        0
% 0.95/0.99  sim_fw_demodulated:                     0
% 0.95/0.99  sim_bw_demodulated:                     0
% 0.95/0.99  sim_light_normalised:                   3
% 0.95/0.99  sim_joinable_taut:                      0
% 0.95/0.99  sim_joinable_simp:                      0
% 0.95/0.99  sim_ac_normalised:                      0
% 0.95/0.99  sim_smt_subsumption:                    0
% 0.95/0.99  
%------------------------------------------------------------------------------
