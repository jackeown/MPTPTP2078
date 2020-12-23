%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:06 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 324 expanded)
%              Number of clauses        :   68 ( 111 expanded)
%              Number of leaves         :   22 (  80 expanded)
%              Depth                    :   22
%              Number of atoms          :  437 (1287 expanded)
%              Number of equality atoms :  135 ( 205 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5,X6] :
                  ( ( r2_hidden(X6,X1)
                    & r2_hidden(X5,X6)
                    & r2_hidden(X4,X5)
                    & r2_hidden(X3,X4)
                    & r2_hidden(X2,X3) )
                 => r1_xboole_0(X2,X0) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).

fof(f56,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f45,f44])).

fof(f68,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f69,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f70,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] : k1_xboole_0 != k3_tarski(k2_tarski(k1_tarski(X0),X1)) ),
    inference(definition_unfolding,[],[f51,f50])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_8,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_333,plain,
    ( m1_subset_1(X0,X1)
    | X2 != X1
    | sK0(X2) != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_8])).

cnf(c_334,plain,
    ( m1_subset_1(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_1227,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_334])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1233,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1803,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1233])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1824,plain,
    ( v1_xboole_0(X0)
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1803])).

cnf(c_2246,plain,
    ( k1_xboole_0 = X0
    | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1803,c_0,c_1824])).

cnf(c_2247,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(renaming,[status(thm)],[c_2246])).

cnf(c_18,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_284,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_285,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_284])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_289,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_285,c_24,c_22])).

cnf(c_1230,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_2250,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2247,c_1230])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1234,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,X0) != iProver_top
    | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_21,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1231,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1236,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1653,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1231,c_1236])).

cnf(c_19,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_483,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_484,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_483])).

cnf(c_610,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_484])).

cnf(c_611,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_610])).

cnf(c_4,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_625,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_611,c_4])).

cnf(c_652,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_625])).

cnf(c_788,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_652])).

cnf(c_1219,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_788])).

cnf(c_1682,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1653,c_1219])).

cnf(c_1691,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1682])).

cnf(c_2034,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k1_tarski(X0) = k1_xboole_0
    | v2_tex_2(k1_tarski(X0),sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1234,c_1691])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_10,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_266,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_9,c_10])).

cnf(c_305,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_266,c_24])).

cnf(c_306,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_367,plain,
    ( sK3 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_21])).

cnf(c_368,plain,
    ( k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_924,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1354,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_1356,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1546,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK2))
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_924])).

cnf(c_1548,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_xboole_0(k1_xboole_0)
    | u1_struct_0(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1546])).

cnf(c_1,plain,
    ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3,plain,
    ( k3_tarski(k2_tarski(k1_tarski(X0),X1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1558,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1,c_3])).

cnf(c_2181,plain,
    ( v2_tex_2(k1_tarski(X0),sK2) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2034,c_22,c_21,c_306,c_368,c_1356,c_1548,c_1558])).

cnf(c_2189,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_2181])).

cnf(c_923,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1619,plain,
    ( X0 != X1
    | u1_struct_0(sK2) != X1
    | u1_struct_0(sK2) = X0 ),
    inference(instantiation,[status(thm)],[c_923])).

cnf(c_1942,plain,
    ( X0 != u1_struct_0(sK2)
    | u1_struct_0(sK2) = X0
    | u1_struct_0(sK2) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1619])).

cnf(c_1943,plain,
    ( u1_struct_0(sK2) != u1_struct_0(sK2)
    | u1_struct_0(sK2) = k1_xboole_0
    | k1_xboole_0 != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1942])).

cnf(c_922,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1635,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_922])).

cnf(c_1515,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
    | k1_xboole_0 = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_334])).

cnf(c_1520,plain,
    ( k1_xboole_0 = u1_struct_0(sK2)
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2250,c_2189,c_1943,c_1635,c_1548,c_1520,c_1356,c_368,c_306,c_21,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:24:56 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.49/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/0.98  
% 2.49/0.98  ------  iProver source info
% 2.49/0.98  
% 2.49/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.49/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/0.98  git: non_committed_changes: false
% 2.49/0.98  git: last_make_outside_of_git: false
% 2.49/0.98  
% 2.49/0.98  ------ 
% 2.49/0.98  
% 2.49/0.98  ------ Input Options
% 2.49/0.98  
% 2.49/0.98  --out_options                           all
% 2.49/0.98  --tptp_safe_out                         true
% 2.49/0.98  --problem_path                          ""
% 2.49/0.98  --include_path                          ""
% 2.49/0.98  --clausifier                            res/vclausify_rel
% 2.49/0.98  --clausifier_options                    --mode clausify
% 2.49/0.98  --stdin                                 false
% 2.49/0.98  --stats_out                             all
% 2.49/0.98  
% 2.49/0.98  ------ General Options
% 2.49/0.98  
% 2.49/0.98  --fof                                   false
% 2.49/0.98  --time_out_real                         305.
% 2.49/0.98  --time_out_virtual                      -1.
% 2.49/0.98  --symbol_type_check                     false
% 2.49/0.98  --clausify_out                          false
% 2.49/0.98  --sig_cnt_out                           false
% 2.49/0.98  --trig_cnt_out                          false
% 2.49/0.98  --trig_cnt_out_tolerance                1.
% 2.49/0.98  --trig_cnt_out_sk_spl                   false
% 2.49/0.98  --abstr_cl_out                          false
% 2.49/0.98  
% 2.49/0.98  ------ Global Options
% 2.49/0.98  
% 2.49/0.98  --schedule                              default
% 2.49/0.98  --add_important_lit                     false
% 2.49/0.98  --prop_solver_per_cl                    1000
% 2.49/0.98  --min_unsat_core                        false
% 2.49/0.98  --soft_assumptions                      false
% 2.49/0.98  --soft_lemma_size                       3
% 2.49/0.98  --prop_impl_unit_size                   0
% 2.49/0.98  --prop_impl_unit                        []
% 2.49/0.98  --share_sel_clauses                     true
% 2.49/0.98  --reset_solvers                         false
% 2.49/0.98  --bc_imp_inh                            [conj_cone]
% 2.49/0.98  --conj_cone_tolerance                   3.
% 2.49/0.98  --extra_neg_conj                        none
% 2.49/0.98  --large_theory_mode                     true
% 2.49/0.98  --prolific_symb_bound                   200
% 2.49/0.98  --lt_threshold                          2000
% 2.49/0.98  --clause_weak_htbl                      true
% 2.49/0.98  --gc_record_bc_elim                     false
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing Options
% 2.49/0.98  
% 2.49/0.98  --preprocessing_flag                    true
% 2.49/0.98  --time_out_prep_mult                    0.1
% 2.49/0.98  --splitting_mode                        input
% 2.49/0.98  --splitting_grd                         true
% 2.49/0.98  --splitting_cvd                         false
% 2.49/0.98  --splitting_cvd_svl                     false
% 2.49/0.98  --splitting_nvd                         32
% 2.49/0.98  --sub_typing                            true
% 2.49/0.98  --prep_gs_sim                           true
% 2.49/0.98  --prep_unflatten                        true
% 2.49/0.98  --prep_res_sim                          true
% 2.49/0.98  --prep_upred                            true
% 2.49/0.98  --prep_sem_filter                       exhaustive
% 2.49/0.98  --prep_sem_filter_out                   false
% 2.49/0.98  --pred_elim                             true
% 2.49/0.98  --res_sim_input                         true
% 2.49/0.98  --eq_ax_congr_red                       true
% 2.49/0.98  --pure_diseq_elim                       true
% 2.49/0.98  --brand_transform                       false
% 2.49/0.98  --non_eq_to_eq                          false
% 2.49/0.98  --prep_def_merge                        true
% 2.49/0.98  --prep_def_merge_prop_impl              false
% 2.49/0.98  --prep_def_merge_mbd                    true
% 2.49/0.98  --prep_def_merge_tr_red                 false
% 2.49/0.98  --prep_def_merge_tr_cl                  false
% 2.49/0.98  --smt_preprocessing                     true
% 2.49/0.98  --smt_ac_axioms                         fast
% 2.49/0.98  --preprocessed_out                      false
% 2.49/0.98  --preprocessed_stats                    false
% 2.49/0.98  
% 2.49/0.98  ------ Abstraction refinement Options
% 2.49/0.98  
% 2.49/0.98  --abstr_ref                             []
% 2.49/0.98  --abstr_ref_prep                        false
% 2.49/0.98  --abstr_ref_until_sat                   false
% 2.49/0.98  --abstr_ref_sig_restrict                funpre
% 2.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.98  --abstr_ref_under                       []
% 2.49/0.98  
% 2.49/0.98  ------ SAT Options
% 2.49/0.98  
% 2.49/0.98  --sat_mode                              false
% 2.49/0.98  --sat_fm_restart_options                ""
% 2.49/0.98  --sat_gr_def                            false
% 2.49/0.98  --sat_epr_types                         true
% 2.49/0.98  --sat_non_cyclic_types                  false
% 2.49/0.98  --sat_finite_models                     false
% 2.49/0.98  --sat_fm_lemmas                         false
% 2.49/0.98  --sat_fm_prep                           false
% 2.49/0.98  --sat_fm_uc_incr                        true
% 2.49/0.98  --sat_out_model                         small
% 2.49/0.98  --sat_out_clauses                       false
% 2.49/0.98  
% 2.49/0.98  ------ QBF Options
% 2.49/0.98  
% 2.49/0.98  --qbf_mode                              false
% 2.49/0.98  --qbf_elim_univ                         false
% 2.49/0.98  --qbf_dom_inst                          none
% 2.49/0.98  --qbf_dom_pre_inst                      false
% 2.49/0.98  --qbf_sk_in                             false
% 2.49/0.98  --qbf_pred_elim                         true
% 2.49/0.98  --qbf_split                             512
% 2.49/0.98  
% 2.49/0.98  ------ BMC1 Options
% 2.49/0.98  
% 2.49/0.98  --bmc1_incremental                      false
% 2.49/0.98  --bmc1_axioms                           reachable_all
% 2.49/0.98  --bmc1_min_bound                        0
% 2.49/0.98  --bmc1_max_bound                        -1
% 2.49/0.98  --bmc1_max_bound_default                -1
% 2.49/0.98  --bmc1_symbol_reachability              true
% 2.49/0.98  --bmc1_property_lemmas                  false
% 2.49/0.98  --bmc1_k_induction                      false
% 2.49/0.98  --bmc1_non_equiv_states                 false
% 2.49/0.98  --bmc1_deadlock                         false
% 2.49/0.98  --bmc1_ucm                              false
% 2.49/0.98  --bmc1_add_unsat_core                   none
% 2.49/0.98  --bmc1_unsat_core_children              false
% 2.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.98  --bmc1_out_stat                         full
% 2.49/0.98  --bmc1_ground_init                      false
% 2.49/0.98  --bmc1_pre_inst_next_state              false
% 2.49/0.98  --bmc1_pre_inst_state                   false
% 2.49/0.98  --bmc1_pre_inst_reach_state             false
% 2.49/0.98  --bmc1_out_unsat_core                   false
% 2.49/0.98  --bmc1_aig_witness_out                  false
% 2.49/0.98  --bmc1_verbose                          false
% 2.49/0.98  --bmc1_dump_clauses_tptp                false
% 2.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.98  --bmc1_dump_file                        -
% 2.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.98  --bmc1_ucm_extend_mode                  1
% 2.49/0.98  --bmc1_ucm_init_mode                    2
% 2.49/0.98  --bmc1_ucm_cone_mode                    none
% 2.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.98  --bmc1_ucm_relax_model                  4
% 2.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.98  --bmc1_ucm_layered_model                none
% 2.49/0.98  --bmc1_ucm_max_lemma_size               10
% 2.49/0.98  
% 2.49/0.98  ------ AIG Options
% 2.49/0.98  
% 2.49/0.98  --aig_mode                              false
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation Options
% 2.49/0.98  
% 2.49/0.98  --instantiation_flag                    true
% 2.49/0.98  --inst_sos_flag                         false
% 2.49/0.98  --inst_sos_phase                        true
% 2.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel_side                     num_symb
% 2.49/0.98  --inst_solver_per_active                1400
% 2.49/0.98  --inst_solver_calls_frac                1.
% 2.49/0.98  --inst_passive_queue_type               priority_queues
% 2.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.98  --inst_passive_queues_freq              [25;2]
% 2.49/0.98  --inst_dismatching                      true
% 2.49/0.98  --inst_eager_unprocessed_to_passive     true
% 2.49/0.98  --inst_prop_sim_given                   true
% 2.49/0.98  --inst_prop_sim_new                     false
% 2.49/0.98  --inst_subs_new                         false
% 2.49/0.98  --inst_eq_res_simp                      false
% 2.49/0.98  --inst_subs_given                       false
% 2.49/0.98  --inst_orphan_elimination               true
% 2.49/0.98  --inst_learning_loop_flag               true
% 2.49/0.98  --inst_learning_start                   3000
% 2.49/0.98  --inst_learning_factor                  2
% 2.49/0.98  --inst_start_prop_sim_after_learn       3
% 2.49/0.98  --inst_sel_renew                        solver
% 2.49/0.98  --inst_lit_activity_flag                true
% 2.49/0.98  --inst_restr_to_given                   false
% 2.49/0.98  --inst_activity_threshold               500
% 2.49/0.98  --inst_out_proof                        true
% 2.49/0.98  
% 2.49/0.98  ------ Resolution Options
% 2.49/0.98  
% 2.49/0.98  --resolution_flag                       true
% 2.49/0.98  --res_lit_sel                           adaptive
% 2.49/0.98  --res_lit_sel_side                      none
% 2.49/0.98  --res_ordering                          kbo
% 2.49/0.98  --res_to_prop_solver                    active
% 2.49/0.98  --res_prop_simpl_new                    false
% 2.49/0.98  --res_prop_simpl_given                  true
% 2.49/0.98  --res_passive_queue_type                priority_queues
% 2.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.98  --res_passive_queues_freq               [15;5]
% 2.49/0.98  --res_forward_subs                      full
% 2.49/0.98  --res_backward_subs                     full
% 2.49/0.98  --res_forward_subs_resolution           true
% 2.49/0.98  --res_backward_subs_resolution          true
% 2.49/0.98  --res_orphan_elimination                true
% 2.49/0.98  --res_time_limit                        2.
% 2.49/0.98  --res_out_proof                         true
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Options
% 2.49/0.98  
% 2.49/0.98  --superposition_flag                    true
% 2.49/0.98  --sup_passive_queue_type                priority_queues
% 2.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.98  --demod_completeness_check              fast
% 2.49/0.98  --demod_use_ground                      true
% 2.49/0.98  --sup_to_prop_solver                    passive
% 2.49/0.98  --sup_prop_simpl_new                    true
% 2.49/0.98  --sup_prop_simpl_given                  true
% 2.49/0.98  --sup_fun_splitting                     false
% 2.49/0.98  --sup_smt_interval                      50000
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Simplification Setup
% 2.49/0.98  
% 2.49/0.98  --sup_indices_passive                   []
% 2.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_full_bw                           [BwDemod]
% 2.49/0.98  --sup_immed_triv                        [TrivRules]
% 2.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_immed_bw_main                     []
% 2.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  
% 2.49/0.98  ------ Combination Options
% 2.49/0.98  
% 2.49/0.98  --comb_res_mult                         3
% 2.49/0.98  --comb_sup_mult                         2
% 2.49/0.98  --comb_inst_mult                        10
% 2.49/0.98  
% 2.49/0.98  ------ Debug Options
% 2.49/0.98  
% 2.49/0.98  --dbg_backtrace                         false
% 2.49/0.98  --dbg_dump_prop_clauses                 false
% 2.49/0.98  --dbg_dump_prop_clauses_file            -
% 2.49/0.98  --dbg_out_stat                          false
% 2.49/0.98  ------ Parsing...
% 2.49/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/0.98  ------ Proving...
% 2.49/0.98  ------ Problem Properties 
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  clauses                                 20
% 2.49/0.98  conjectures                             2
% 2.49/0.98  EPR                                     3
% 2.49/0.98  Horn                                    14
% 2.49/0.98  unary                                   7
% 2.49/0.98  binary                                  3
% 2.49/0.98  lits                                    47
% 2.49/0.98  lits eq                                 13
% 2.49/0.98  fd_pure                                 0
% 2.49/0.98  fd_pseudo                               0
% 2.49/0.98  fd_cond                                 8
% 2.49/0.98  fd_pseudo_cond                          0
% 2.49/0.98  AC symbols                              0
% 2.49/0.98  
% 2.49/0.98  ------ Schedule dynamic 5 is on 
% 2.49/0.98  
% 2.49/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  ------ 
% 2.49/0.98  Current options:
% 2.49/0.98  ------ 
% 2.49/0.98  
% 2.49/0.98  ------ Input Options
% 2.49/0.98  
% 2.49/0.98  --out_options                           all
% 2.49/0.98  --tptp_safe_out                         true
% 2.49/0.98  --problem_path                          ""
% 2.49/0.98  --include_path                          ""
% 2.49/0.98  --clausifier                            res/vclausify_rel
% 2.49/0.98  --clausifier_options                    --mode clausify
% 2.49/0.98  --stdin                                 false
% 2.49/0.98  --stats_out                             all
% 2.49/0.98  
% 2.49/0.98  ------ General Options
% 2.49/0.98  
% 2.49/0.98  --fof                                   false
% 2.49/0.98  --time_out_real                         305.
% 2.49/0.98  --time_out_virtual                      -1.
% 2.49/0.98  --symbol_type_check                     false
% 2.49/0.98  --clausify_out                          false
% 2.49/0.98  --sig_cnt_out                           false
% 2.49/0.98  --trig_cnt_out                          false
% 2.49/0.98  --trig_cnt_out_tolerance                1.
% 2.49/0.98  --trig_cnt_out_sk_spl                   false
% 2.49/0.98  --abstr_cl_out                          false
% 2.49/0.98  
% 2.49/0.98  ------ Global Options
% 2.49/0.98  
% 2.49/0.98  --schedule                              default
% 2.49/0.98  --add_important_lit                     false
% 2.49/0.98  --prop_solver_per_cl                    1000
% 2.49/0.98  --min_unsat_core                        false
% 2.49/0.98  --soft_assumptions                      false
% 2.49/0.98  --soft_lemma_size                       3
% 2.49/0.98  --prop_impl_unit_size                   0
% 2.49/0.98  --prop_impl_unit                        []
% 2.49/0.98  --share_sel_clauses                     true
% 2.49/0.98  --reset_solvers                         false
% 2.49/0.98  --bc_imp_inh                            [conj_cone]
% 2.49/0.98  --conj_cone_tolerance                   3.
% 2.49/0.98  --extra_neg_conj                        none
% 2.49/0.98  --large_theory_mode                     true
% 2.49/0.98  --prolific_symb_bound                   200
% 2.49/0.98  --lt_threshold                          2000
% 2.49/0.98  --clause_weak_htbl                      true
% 2.49/0.98  --gc_record_bc_elim                     false
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing Options
% 2.49/0.98  
% 2.49/0.98  --preprocessing_flag                    true
% 2.49/0.98  --time_out_prep_mult                    0.1
% 2.49/0.98  --splitting_mode                        input
% 2.49/0.98  --splitting_grd                         true
% 2.49/0.98  --splitting_cvd                         false
% 2.49/0.98  --splitting_cvd_svl                     false
% 2.49/0.98  --splitting_nvd                         32
% 2.49/0.98  --sub_typing                            true
% 2.49/0.98  --prep_gs_sim                           true
% 2.49/0.98  --prep_unflatten                        true
% 2.49/0.98  --prep_res_sim                          true
% 2.49/0.98  --prep_upred                            true
% 2.49/0.98  --prep_sem_filter                       exhaustive
% 2.49/0.98  --prep_sem_filter_out                   false
% 2.49/0.98  --pred_elim                             true
% 2.49/0.98  --res_sim_input                         true
% 2.49/0.98  --eq_ax_congr_red                       true
% 2.49/0.98  --pure_diseq_elim                       true
% 2.49/0.98  --brand_transform                       false
% 2.49/0.98  --non_eq_to_eq                          false
% 2.49/0.98  --prep_def_merge                        true
% 2.49/0.98  --prep_def_merge_prop_impl              false
% 2.49/0.98  --prep_def_merge_mbd                    true
% 2.49/0.98  --prep_def_merge_tr_red                 false
% 2.49/0.98  --prep_def_merge_tr_cl                  false
% 2.49/0.98  --smt_preprocessing                     true
% 2.49/0.98  --smt_ac_axioms                         fast
% 2.49/0.98  --preprocessed_out                      false
% 2.49/0.98  --preprocessed_stats                    false
% 2.49/0.98  
% 2.49/0.98  ------ Abstraction refinement Options
% 2.49/0.98  
% 2.49/0.98  --abstr_ref                             []
% 2.49/0.98  --abstr_ref_prep                        false
% 2.49/0.98  --abstr_ref_until_sat                   false
% 2.49/0.98  --abstr_ref_sig_restrict                funpre
% 2.49/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/0.98  --abstr_ref_under                       []
% 2.49/0.98  
% 2.49/0.98  ------ SAT Options
% 2.49/0.98  
% 2.49/0.98  --sat_mode                              false
% 2.49/0.98  --sat_fm_restart_options                ""
% 2.49/0.98  --sat_gr_def                            false
% 2.49/0.98  --sat_epr_types                         true
% 2.49/0.98  --sat_non_cyclic_types                  false
% 2.49/0.98  --sat_finite_models                     false
% 2.49/0.98  --sat_fm_lemmas                         false
% 2.49/0.98  --sat_fm_prep                           false
% 2.49/0.98  --sat_fm_uc_incr                        true
% 2.49/0.98  --sat_out_model                         small
% 2.49/0.98  --sat_out_clauses                       false
% 2.49/0.98  
% 2.49/0.98  ------ QBF Options
% 2.49/0.98  
% 2.49/0.98  --qbf_mode                              false
% 2.49/0.98  --qbf_elim_univ                         false
% 2.49/0.98  --qbf_dom_inst                          none
% 2.49/0.98  --qbf_dom_pre_inst                      false
% 2.49/0.98  --qbf_sk_in                             false
% 2.49/0.98  --qbf_pred_elim                         true
% 2.49/0.98  --qbf_split                             512
% 2.49/0.98  
% 2.49/0.98  ------ BMC1 Options
% 2.49/0.98  
% 2.49/0.98  --bmc1_incremental                      false
% 2.49/0.98  --bmc1_axioms                           reachable_all
% 2.49/0.98  --bmc1_min_bound                        0
% 2.49/0.98  --bmc1_max_bound                        -1
% 2.49/0.98  --bmc1_max_bound_default                -1
% 2.49/0.98  --bmc1_symbol_reachability              true
% 2.49/0.98  --bmc1_property_lemmas                  false
% 2.49/0.98  --bmc1_k_induction                      false
% 2.49/0.98  --bmc1_non_equiv_states                 false
% 2.49/0.98  --bmc1_deadlock                         false
% 2.49/0.98  --bmc1_ucm                              false
% 2.49/0.98  --bmc1_add_unsat_core                   none
% 2.49/0.98  --bmc1_unsat_core_children              false
% 2.49/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/0.98  --bmc1_out_stat                         full
% 2.49/0.98  --bmc1_ground_init                      false
% 2.49/0.98  --bmc1_pre_inst_next_state              false
% 2.49/0.98  --bmc1_pre_inst_state                   false
% 2.49/0.98  --bmc1_pre_inst_reach_state             false
% 2.49/0.98  --bmc1_out_unsat_core                   false
% 2.49/0.98  --bmc1_aig_witness_out                  false
% 2.49/0.98  --bmc1_verbose                          false
% 2.49/0.98  --bmc1_dump_clauses_tptp                false
% 2.49/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.49/0.98  --bmc1_dump_file                        -
% 2.49/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.49/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.49/0.98  --bmc1_ucm_extend_mode                  1
% 2.49/0.98  --bmc1_ucm_init_mode                    2
% 2.49/0.98  --bmc1_ucm_cone_mode                    none
% 2.49/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.49/0.98  --bmc1_ucm_relax_model                  4
% 2.49/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.49/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/0.98  --bmc1_ucm_layered_model                none
% 2.49/0.98  --bmc1_ucm_max_lemma_size               10
% 2.49/0.98  
% 2.49/0.98  ------ AIG Options
% 2.49/0.98  
% 2.49/0.98  --aig_mode                              false
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation Options
% 2.49/0.98  
% 2.49/0.98  --instantiation_flag                    true
% 2.49/0.98  --inst_sos_flag                         false
% 2.49/0.98  --inst_sos_phase                        true
% 2.49/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/0.98  --inst_lit_sel_side                     none
% 2.49/0.98  --inst_solver_per_active                1400
% 2.49/0.98  --inst_solver_calls_frac                1.
% 2.49/0.98  --inst_passive_queue_type               priority_queues
% 2.49/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/0.98  --inst_passive_queues_freq              [25;2]
% 2.49/0.98  --inst_dismatching                      true
% 2.49/0.98  --inst_eager_unprocessed_to_passive     true
% 2.49/0.98  --inst_prop_sim_given                   true
% 2.49/0.98  --inst_prop_sim_new                     false
% 2.49/0.98  --inst_subs_new                         false
% 2.49/0.98  --inst_eq_res_simp                      false
% 2.49/0.98  --inst_subs_given                       false
% 2.49/0.98  --inst_orphan_elimination               true
% 2.49/0.98  --inst_learning_loop_flag               true
% 2.49/0.98  --inst_learning_start                   3000
% 2.49/0.98  --inst_learning_factor                  2
% 2.49/0.98  --inst_start_prop_sim_after_learn       3
% 2.49/0.98  --inst_sel_renew                        solver
% 2.49/0.98  --inst_lit_activity_flag                true
% 2.49/0.98  --inst_restr_to_given                   false
% 2.49/0.98  --inst_activity_threshold               500
% 2.49/0.98  --inst_out_proof                        true
% 2.49/0.98  
% 2.49/0.98  ------ Resolution Options
% 2.49/0.98  
% 2.49/0.98  --resolution_flag                       false
% 2.49/0.98  --res_lit_sel                           adaptive
% 2.49/0.98  --res_lit_sel_side                      none
% 2.49/0.98  --res_ordering                          kbo
% 2.49/0.98  --res_to_prop_solver                    active
% 2.49/0.98  --res_prop_simpl_new                    false
% 2.49/0.98  --res_prop_simpl_given                  true
% 2.49/0.98  --res_passive_queue_type                priority_queues
% 2.49/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/0.98  --res_passive_queues_freq               [15;5]
% 2.49/0.98  --res_forward_subs                      full
% 2.49/0.98  --res_backward_subs                     full
% 2.49/0.98  --res_forward_subs_resolution           true
% 2.49/0.98  --res_backward_subs_resolution          true
% 2.49/0.98  --res_orphan_elimination                true
% 2.49/0.98  --res_time_limit                        2.
% 2.49/0.98  --res_out_proof                         true
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Options
% 2.49/0.98  
% 2.49/0.98  --superposition_flag                    true
% 2.49/0.98  --sup_passive_queue_type                priority_queues
% 2.49/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.49/0.98  --demod_completeness_check              fast
% 2.49/0.98  --demod_use_ground                      true
% 2.49/0.98  --sup_to_prop_solver                    passive
% 2.49/0.98  --sup_prop_simpl_new                    true
% 2.49/0.98  --sup_prop_simpl_given                  true
% 2.49/0.98  --sup_fun_splitting                     false
% 2.49/0.98  --sup_smt_interval                      50000
% 2.49/0.98  
% 2.49/0.98  ------ Superposition Simplification Setup
% 2.49/0.98  
% 2.49/0.98  --sup_indices_passive                   []
% 2.49/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_full_bw                           [BwDemod]
% 2.49/0.98  --sup_immed_triv                        [TrivRules]
% 2.49/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_immed_bw_main                     []
% 2.49/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/0.98  
% 2.49/0.98  ------ Combination Options
% 2.49/0.98  
% 2.49/0.98  --comb_res_mult                         3
% 2.49/0.98  --comb_sup_mult                         2
% 2.49/0.98  --comb_inst_mult                        10
% 2.49/0.98  
% 2.49/0.98  ------ Debug Options
% 2.49/0.98  
% 2.49/0.98  --dbg_backtrace                         false
% 2.49/0.98  --dbg_dump_prop_clauses                 false
% 2.49/0.98  --dbg_dump_prop_clauses_file            -
% 2.49/0.98  --dbg_out_stat                          false
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  ------ Proving...
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  % SZS status Theorem for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  fof(f8,axiom,(
% 2.49/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f22,plain,(
% 2.49/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.49/0.98    inference(ennf_transformation,[],[f8])).
% 2.49/0.98  
% 2.49/0.98  fof(f54,plain,(
% 2.49/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f22])).
% 2.49/0.98  
% 2.49/0.98  fof(f10,axiom,(
% 2.49/0.98    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5,X6] : ((r2_hidden(X6,X1) & r2_hidden(X5,X6) & r2_hidden(X4,X5) & r2_hidden(X3,X4) & r2_hidden(X2,X3)) => r1_xboole_0(X2,X0)) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f18,plain,(
% 2.49/0.98    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.49/0.98    inference(pure_predicate_removal,[],[f10])).
% 2.49/0.98  
% 2.49/0.98  fof(f25,plain,(
% 2.49/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.49/0.98    inference(ennf_transformation,[],[f18])).
% 2.49/0.98  
% 2.49/0.98  fof(f37,plain,(
% 2.49/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.49/0.98    introduced(choice_axiom,[])).
% 2.49/0.98  
% 2.49/0.98  fof(f38,plain,(
% 2.49/0.98    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f37])).
% 2.49/0.98  
% 2.49/0.98  fof(f56,plain,(
% 2.49/0.98    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.49/0.98    inference(cnf_transformation,[],[f38])).
% 2.49/0.98  
% 2.49/0.98  fof(f13,axiom,(
% 2.49/0.98    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f29,plain,(
% 2.49/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.49/0.98    inference(ennf_transformation,[],[f13])).
% 2.49/0.98  
% 2.49/0.98  fof(f30,plain,(
% 2.49/0.98    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.49/0.98    inference(flattening,[],[f29])).
% 2.49/0.98  
% 2.49/0.98  fof(f59,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f30])).
% 2.49/0.98  
% 2.49/0.98  fof(f1,axiom,(
% 2.49/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f19,plain,(
% 2.49/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f1])).
% 2.49/0.98  
% 2.49/0.98  fof(f47,plain,(
% 2.49/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f19])).
% 2.49/0.98  
% 2.49/0.98  fof(f15,axiom,(
% 2.49/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f33,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.49/0.98    inference(ennf_transformation,[],[f15])).
% 2.49/0.98  
% 2.49/0.98  fof(f34,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.49/0.98    inference(flattening,[],[f33])).
% 2.49/0.98  
% 2.49/0.98  fof(f66,plain,(
% 2.49/0.98    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f34])).
% 2.49/0.98  
% 2.49/0.98  fof(f16,conjecture,(
% 2.49/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f17,negated_conjecture,(
% 2.49/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.49/0.98    inference(negated_conjecture,[],[f16])).
% 2.49/0.98  
% 2.49/0.98  fof(f35,plain,(
% 2.49/0.98    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.49/0.98    inference(ennf_transformation,[],[f17])).
% 2.49/0.98  
% 2.49/0.98  fof(f36,plain,(
% 2.49/0.98    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.49/0.98    inference(flattening,[],[f35])).
% 2.49/0.98  
% 2.49/0.98  fof(f45,plain,(
% 2.49/0.98    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 2.49/0.98    introduced(choice_axiom,[])).
% 2.49/0.98  
% 2.49/0.98  fof(f44,plain,(
% 2.49/0.98    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.49/0.98    introduced(choice_axiom,[])).
% 2.49/0.98  
% 2.49/0.98  fof(f46,plain,(
% 2.49/0.98    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f45,f44])).
% 2.49/0.98  
% 2.49/0.98  fof(f68,plain,(
% 2.49/0.98    v2_pre_topc(sK2)),
% 2.49/0.98    inference(cnf_transformation,[],[f46])).
% 2.49/0.98  
% 2.49/0.98  fof(f67,plain,(
% 2.49/0.98    ~v2_struct_0(sK2)),
% 2.49/0.98    inference(cnf_transformation,[],[f46])).
% 2.49/0.98  
% 2.49/0.98  fof(f69,plain,(
% 2.49/0.98    l1_pre_topc(sK2)),
% 2.49/0.98    inference(cnf_transformation,[],[f46])).
% 2.49/0.98  
% 2.49/0.98  fof(f7,axiom,(
% 2.49/0.98    ! [X0,X1] : (m1_subset_1(X1,X0) => (k1_xboole_0 != X0 => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f20,plain,(
% 2.49/0.98    ! [X0,X1] : ((m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0) | ~m1_subset_1(X1,X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f7])).
% 2.49/0.98  
% 2.49/0.98  fof(f21,plain,(
% 2.49/0.98    ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0))),
% 2.49/0.98    inference(flattening,[],[f20])).
% 2.49/0.98  
% 2.49/0.98  fof(f53,plain,(
% 2.49/0.98    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) | k1_xboole_0 = X0 | ~m1_subset_1(X1,X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f21])).
% 2.49/0.98  
% 2.49/0.98  fof(f70,plain,(
% 2.49/0.98    v1_xboole_0(sK3)),
% 2.49/0.98    inference(cnf_transformation,[],[f46])).
% 2.49/0.98  
% 2.49/0.98  fof(f72,plain,(
% 2.49/0.98    v3_tex_2(sK3,sK2)),
% 2.49/0.98    inference(cnf_transformation,[],[f46])).
% 2.49/0.98  
% 2.49/0.98  fof(f3,axiom,(
% 2.49/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f49,plain,(
% 2.49/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f3])).
% 2.49/0.98  
% 2.49/0.98  fof(f14,axiom,(
% 2.49/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f31,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f14])).
% 2.49/0.98  
% 2.49/0.98  fof(f32,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(flattening,[],[f31])).
% 2.49/0.98  
% 2.49/0.98  fof(f39,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(nnf_transformation,[],[f32])).
% 2.49/0.98  
% 2.49/0.98  fof(f40,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(flattening,[],[f39])).
% 2.49/0.98  
% 2.49/0.98  fof(f41,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(rectify,[],[f40])).
% 2.49/0.98  
% 2.49/0.98  fof(f42,plain,(
% 2.49/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.49/0.98    introduced(choice_axiom,[])).
% 2.49/0.98  
% 2.49/0.98  fof(f43,plain,(
% 2.49/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 2.49/0.98  
% 2.49/0.98  fof(f61,plain,(
% 2.49/0.98    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f43])).
% 2.49/0.98  
% 2.49/0.98  fof(f6,axiom,(
% 2.49/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f52,plain,(
% 2.49/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f6])).
% 2.49/0.98  
% 2.49/0.98  fof(f11,axiom,(
% 2.49/0.98    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f26,plain,(
% 2.49/0.98    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.49/0.98    inference(ennf_transformation,[],[f11])).
% 2.49/0.98  
% 2.49/0.98  fof(f57,plain,(
% 2.49/0.98    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f26])).
% 2.49/0.98  
% 2.49/0.98  fof(f12,axiom,(
% 2.49/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f27,plain,(
% 2.49/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.49/0.98    inference(ennf_transformation,[],[f12])).
% 2.49/0.98  
% 2.49/0.98  fof(f28,plain,(
% 2.49/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.49/0.98    inference(flattening,[],[f27])).
% 2.49/0.98  
% 2.49/0.98  fof(f58,plain,(
% 2.49/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f28])).
% 2.49/0.98  
% 2.49/0.98  fof(f2,axiom,(
% 2.49/0.98    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f48,plain,(
% 2.49/0.98    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.49/0.98    inference(cnf_transformation,[],[f2])).
% 2.49/0.98  
% 2.49/0.98  fof(f4,axiom,(
% 2.49/0.98    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f50,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.49/0.98    inference(cnf_transformation,[],[f4])).
% 2.49/0.98  
% 2.49/0.98  fof(f73,plain,(
% 2.49/0.98    ( ! [X0] : (k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0) )),
% 2.49/0.98    inference(definition_unfolding,[],[f48,f50])).
% 2.49/0.98  
% 2.49/0.98  fof(f5,axiom,(
% 2.49/0.98    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.49/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/0.98  
% 2.49/0.98  fof(f51,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.49/0.98    inference(cnf_transformation,[],[f5])).
% 2.49/0.98  
% 2.49/0.98  fof(f74,plain,(
% 2.49/0.98    ( ! [X0,X1] : (k1_xboole_0 != k3_tarski(k2_tarski(k1_tarski(X0),X1))) )),
% 2.49/0.98    inference(definition_unfolding,[],[f51,f50])).
% 2.49/0.98  
% 2.49/0.98  cnf(c_6,plain,
% 2.49/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.49/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_8,plain,
% 2.49/0.98      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_333,plain,
% 2.49/0.98      ( m1_subset_1(X0,X1)
% 2.49/0.98      | X2 != X1
% 2.49/0.98      | sK0(X2) != X0
% 2.49/0.98      | k1_xboole_0 = X2 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_6,c_8]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_334,plain,
% 2.49/0.98      ( m1_subset_1(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_333]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1227,plain,
% 2.49/0.98      ( k1_xboole_0 = X0 | m1_subset_1(sK0(X0),X0) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_334]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_11,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,X1)
% 2.49/0.98      | v1_xboole_0(X1)
% 2.49/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1233,plain,
% 2.49/0.98      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.49/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.49/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1803,plain,
% 2.49/0.98      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.49/0.98      | k1_xboole_0 = X0
% 2.49/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1227,c_1233]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_0,plain,
% 2.49/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1824,plain,
% 2.49/0.98      ( v1_xboole_0(X0)
% 2.49/0.98      | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.49/0.98      | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1803]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2246,plain,
% 2.49/0.98      ( k1_xboole_0 = X0 | k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_1803,c_0,c_1824]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2247,plain,
% 2.49/0.98      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(renaming,[status(thm)],[c_2246]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_18,plain,
% 2.49/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.49/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.49/0.98      | ~ v2_pre_topc(X0)
% 2.49/0.98      | v2_struct_0(X0)
% 2.49/0.98      | ~ l1_pre_topc(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_23,negated_conjecture,
% 2.49/0.98      ( v2_pre_topc(sK2) ),
% 2.49/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_284,plain,
% 2.49/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.49/0.98      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.49/0.98      | v2_struct_0(X0)
% 2.49/0.98      | ~ l1_pre_topc(X0)
% 2.49/0.98      | sK2 != X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_285,plain,
% 2.49/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.49/0.98      | v2_struct_0(sK2)
% 2.49/0.98      | ~ l1_pre_topc(sK2) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_284]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_24,negated_conjecture,
% 2.49/0.98      ( ~ v2_struct_0(sK2) ),
% 2.49/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_22,negated_conjecture,
% 2.49/0.98      ( l1_pre_topc(sK2) ),
% 2.49/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_289,plain,
% 2.49/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_285,c_24,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1230,plain,
% 2.49/0.98      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
% 2.49/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2250,plain,
% 2.49/0.98      ( u1_struct_0(sK2) = k1_xboole_0
% 2.49/0.98      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
% 2.49/0.98      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_2247,c_1230]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_5,plain,
% 2.49/0.98      ( ~ m1_subset_1(X0,X1)
% 2.49/0.98      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 2.49/0.98      | k1_xboole_0 = X1 ),
% 2.49/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1234,plain,
% 2.49/0.98      ( k1_xboole_0 = X0
% 2.49/0.98      | m1_subset_1(X1,X0) != iProver_top
% 2.49/0.98      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_21,negated_conjecture,
% 2.49/0.98      ( v1_xboole_0(sK3) ),
% 2.49/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1231,plain,
% 2.49/0.98      ( v1_xboole_0(sK3) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1236,plain,
% 2.49/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1653,plain,
% 2.49/0.98      ( sK3 = k1_xboole_0 ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1231,c_1236]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_19,negated_conjecture,
% 2.49/0.98      ( v3_tex_2(sK3,sK2) ),
% 2.49/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2,plain,
% 2.49/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f49]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_16,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,X1)
% 2.49/0.98      | ~ v3_tex_2(X2,X1)
% 2.49/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.98      | ~ r1_tarski(X2,X0)
% 2.49/0.98      | ~ l1_pre_topc(X1)
% 2.49/0.98      | X0 = X2 ),
% 2.49/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_483,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,X1)
% 2.49/0.98      | ~ v3_tex_2(X2,X1)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.49/0.98      | ~ r1_tarski(X2,X0)
% 2.49/0.98      | X2 = X0
% 2.49/0.98      | sK2 != X1 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_484,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ v3_tex_2(X1,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | ~ r1_tarski(X1,X0)
% 2.49/0.98      | X1 = X0 ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_483]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_610,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ v3_tex_2(X1,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | X0 != X2
% 2.49/0.98      | X0 = X1
% 2.49/0.98      | k1_xboole_0 != X1 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_2,c_484]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_611,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | X0 = k1_xboole_0 ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_610]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_4,plain,
% 2.49/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.49/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_625,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | X0 = k1_xboole_0 ),
% 2.49/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_611,c_4]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_652,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | sK2 != sK2
% 2.49/0.98      | sK3 != k1_xboole_0
% 2.49/0.98      | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_625]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_788,plain,
% 2.49/0.98      ( ~ v2_tex_2(X0,sK2)
% 2.49/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.49/0.98      | sK3 != k1_xboole_0
% 2.49/0.98      | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_652]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1219,plain,
% 2.49/0.98      ( sK3 != k1_xboole_0
% 2.49/0.98      | k1_xboole_0 = X0
% 2.49/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_788]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1682,plain,
% 2.49/0.98      ( k1_xboole_0 = X0
% 2.49/0.98      | k1_xboole_0 != k1_xboole_0
% 2.49/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.49/0.98      inference(demodulation,[status(thm)],[c_1653,c_1219]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1691,plain,
% 2.49/0.98      ( k1_xboole_0 = X0
% 2.49/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 2.49/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.49/0.98      inference(equality_resolution_simp,[status(thm)],[c_1682]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2034,plain,
% 2.49/0.98      ( u1_struct_0(sK2) = k1_xboole_0
% 2.49/0.98      | k1_tarski(X0) = k1_xboole_0
% 2.49/0.98      | v2_tex_2(k1_tarski(X0),sK2) != iProver_top
% 2.49/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1234,c_1691]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_9,plain,
% 2.49/0.98      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.49/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_10,plain,
% 2.49/0.98      ( v2_struct_0(X0)
% 2.49/0.98      | ~ l1_struct_0(X0)
% 2.49/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.49/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_266,plain,
% 2.49/0.98      ( v2_struct_0(X0)
% 2.49/0.98      | ~ l1_pre_topc(X0)
% 2.49/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.49/0.98      inference(resolution,[status(thm)],[c_9,c_10]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_305,plain,
% 2.49/0.98      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_266,c_24]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_306,plain,
% 2.49/0.98      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_305]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_367,plain,
% 2.49/0.98      ( sK3 != X0 | k1_xboole_0 = X0 ),
% 2.49/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_21]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_368,plain,
% 2.49/0.98      ( k1_xboole_0 = sK3 ),
% 2.49/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_924,plain,
% 2.49/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.49/0.98      theory(equality) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1354,plain,
% 2.49/0.98      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | X0 != sK3 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_924]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1356,plain,
% 2.49/0.98      ( ~ v1_xboole_0(sK3)
% 2.49/0.98      | v1_xboole_0(k1_xboole_0)
% 2.49/0.98      | k1_xboole_0 != sK3 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1546,plain,
% 2.49/0.98      ( ~ v1_xboole_0(X0)
% 2.49/0.98      | v1_xboole_0(u1_struct_0(sK2))
% 2.49/0.98      | u1_struct_0(sK2) != X0 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_924]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1548,plain,
% 2.49/0.98      ( v1_xboole_0(u1_struct_0(sK2))
% 2.49/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.49/0.98      | u1_struct_0(sK2) != k1_xboole_0 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_1546]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1,plain,
% 2.49/0.98      ( k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_3,plain,
% 2.49/0.98      ( k3_tarski(k2_tarski(k1_tarski(X0),X1)) != k1_xboole_0 ),
% 2.49/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1558,plain,
% 2.49/0.98      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1,c_3]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2181,plain,
% 2.49/0.98      ( v2_tex_2(k1_tarski(X0),sK2) != iProver_top
% 2.49/0.98      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.49/0.98      inference(global_propositional_subsumption,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_2034,c_22,c_21,c_306,c_368,c_1356,c_1548,c_1558]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_2189,plain,
% 2.49/0.98      ( u1_struct_0(sK2) = k1_xboole_0
% 2.49/0.98      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top ),
% 2.49/0.98      inference(superposition,[status(thm)],[c_1227,c_2181]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_923,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1619,plain,
% 2.49/0.98      ( X0 != X1 | u1_struct_0(sK2) != X1 | u1_struct_0(sK2) = X0 ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_923]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1942,plain,
% 2.49/0.98      ( X0 != u1_struct_0(sK2)
% 2.49/0.98      | u1_struct_0(sK2) = X0
% 2.49/0.98      | u1_struct_0(sK2) != u1_struct_0(sK2) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_1619]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1943,plain,
% 2.49/0.98      ( u1_struct_0(sK2) != u1_struct_0(sK2)
% 2.49/0.98      | u1_struct_0(sK2) = k1_xboole_0
% 2.49/0.98      | k1_xboole_0 != u1_struct_0(sK2) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_1942]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_922,plain,( X0 = X0 ),theory(equality) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1635,plain,
% 2.49/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK2) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_922]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1515,plain,
% 2.49/0.98      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
% 2.49/0.98      | k1_xboole_0 = u1_struct_0(sK2) ),
% 2.49/0.98      inference(instantiation,[status(thm)],[c_334]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(c_1520,plain,
% 2.49/0.98      ( k1_xboole_0 = u1_struct_0(sK2)
% 2.49/0.98      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top ),
% 2.49/0.98      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 2.49/0.98  
% 2.49/0.98  cnf(contradiction,plain,
% 2.49/0.98      ( $false ),
% 2.49/0.98      inference(minisat,
% 2.49/0.98                [status(thm)],
% 2.49/0.98                [c_2250,c_2189,c_1943,c_1635,c_1548,c_1520,c_1356,c_368,
% 2.49/0.98                 c_306,c_21,c_22]) ).
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/0.98  
% 2.49/0.98  ------                               Statistics
% 2.49/0.98  
% 2.49/0.98  ------ General
% 2.49/0.98  
% 2.49/0.98  abstr_ref_over_cycles:                  0
% 2.49/0.98  abstr_ref_under_cycles:                 0
% 2.49/0.98  gc_basic_clause_elim:                   0
% 2.49/0.98  forced_gc_time:                         0
% 2.49/0.98  parsing_time:                           0.009
% 2.49/0.98  unif_index_cands_time:                  0.
% 2.49/0.98  unif_index_add_time:                    0.
% 2.49/0.98  orderings_time:                         0.
% 2.49/0.98  out_proof_time:                         0.01
% 2.49/0.98  total_time:                             0.105
% 2.49/0.98  num_of_symbols:                         53
% 2.49/0.98  num_of_terms:                           1522
% 2.49/0.98  
% 2.49/0.98  ------ Preprocessing
% 2.49/0.98  
% 2.49/0.98  num_of_splits:                          3
% 2.49/0.98  num_of_split_atoms:                     1
% 2.49/0.98  num_of_reused_defs:                     2
% 2.49/0.98  num_eq_ax_congr_red:                    14
% 2.49/0.98  num_of_sem_filtered_clauses:            1
% 2.49/0.98  num_of_subtypes:                        0
% 2.49/0.98  monotx_restored_types:                  0
% 2.49/0.98  sat_num_of_epr_types:                   0
% 2.49/0.98  sat_num_of_non_cyclic_types:            0
% 2.49/0.98  sat_guarded_non_collapsed_types:        0
% 2.49/0.98  num_pure_diseq_elim:                    0
% 2.49/0.98  simp_replaced_by:                       0
% 2.49/0.98  res_preprocessed:                       101
% 2.49/0.98  prep_upred:                             0
% 2.49/0.98  prep_unflattend:                        30
% 2.49/0.98  smt_new_axioms:                         0
% 2.49/0.98  pred_elim_cands:                        3
% 2.49/0.98  pred_elim:                              7
% 2.49/0.98  pred_elim_cl:                           8
% 2.49/0.98  pred_elim_cycles:                       11
% 2.49/0.98  merged_defs:                            0
% 2.49/0.98  merged_defs_ncl:                        0
% 2.49/0.98  bin_hyper_res:                          0
% 2.49/0.98  prep_cycles:                            4
% 2.49/0.98  pred_elim_time:                         0.011
% 2.49/0.98  splitting_time:                         0.
% 2.49/0.98  sem_filter_time:                        0.
% 2.49/0.98  monotx_time:                            0.
% 2.49/0.98  subtype_inf_time:                       0.
% 2.49/0.98  
% 2.49/0.98  ------ Problem properties
% 2.49/0.98  
% 2.49/0.98  clauses:                                20
% 2.49/0.98  conjectures:                            2
% 2.49/0.98  epr:                                    3
% 2.49/0.98  horn:                                   14
% 2.49/0.98  ground:                                 7
% 2.49/0.98  unary:                                  7
% 2.49/0.98  binary:                                 3
% 2.49/0.98  lits:                                   47
% 2.49/0.98  lits_eq:                                13
% 2.49/0.98  fd_pure:                                0
% 2.49/0.98  fd_pseudo:                              0
% 2.49/0.98  fd_cond:                                8
% 2.49/0.98  fd_pseudo_cond:                         0
% 2.49/0.98  ac_symbols:                             0
% 2.49/0.98  
% 2.49/0.98  ------ Propositional Solver
% 2.49/0.98  
% 2.49/0.98  prop_solver_calls:                      27
% 2.49/0.98  prop_fast_solver_calls:                 691
% 2.49/0.98  smt_solver_calls:                       0
% 2.49/0.98  smt_fast_solver_calls:                  0
% 2.49/0.98  prop_num_of_clauses:                    623
% 2.49/0.98  prop_preprocess_simplified:             3131
% 2.49/0.98  prop_fo_subsumed:                       17
% 2.49/0.98  prop_solver_time:                       0.
% 2.49/0.98  smt_solver_time:                        0.
% 2.49/0.98  smt_fast_solver_time:                   0.
% 2.49/0.98  prop_fast_solver_time:                  0.
% 2.49/0.98  prop_unsat_core_time:                   0.
% 2.49/0.98  
% 2.49/0.98  ------ QBF
% 2.49/0.98  
% 2.49/0.98  qbf_q_res:                              0
% 2.49/0.98  qbf_num_tautologies:                    0
% 2.49/0.98  qbf_prep_cycles:                        0
% 2.49/0.98  
% 2.49/0.98  ------ BMC1
% 2.49/0.98  
% 2.49/0.98  bmc1_current_bound:                     -1
% 2.49/0.98  bmc1_last_solved_bound:                 -1
% 2.49/0.98  bmc1_unsat_core_size:                   -1
% 2.49/0.98  bmc1_unsat_core_parents_size:           -1
% 2.49/0.98  bmc1_merge_next_fun:                    0
% 2.49/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.49/0.98  
% 2.49/0.98  ------ Instantiation
% 2.49/0.98  
% 2.49/0.98  inst_num_of_clauses:                    180
% 2.49/0.98  inst_num_in_passive:                    50
% 2.49/0.98  inst_num_in_active:                     128
% 2.49/0.98  inst_num_in_unprocessed:                2
% 2.49/0.98  inst_num_of_loops:                      150
% 2.49/0.98  inst_num_of_learning_restarts:          0
% 2.49/0.98  inst_num_moves_active_passive:          19
% 2.49/0.98  inst_lit_activity:                      0
% 2.49/0.98  inst_lit_activity_moves:                0
% 2.49/0.98  inst_num_tautologies:                   0
% 2.49/0.98  inst_num_prop_implied:                  0
% 2.49/0.98  inst_num_existing_simplified:           0
% 2.49/0.98  inst_num_eq_res_simplified:             0
% 2.49/0.98  inst_num_child_elim:                    0
% 2.49/0.98  inst_num_of_dismatching_blockings:      21
% 2.49/0.98  inst_num_of_non_proper_insts:           137
% 2.49/0.98  inst_num_of_duplicates:                 0
% 2.49/0.98  inst_inst_num_from_inst_to_res:         0
% 2.49/0.98  inst_dismatching_checking_time:         0.
% 2.49/0.98  
% 2.49/0.98  ------ Resolution
% 2.49/0.98  
% 2.49/0.98  res_num_of_clauses:                     0
% 2.49/0.98  res_num_in_passive:                     0
% 2.49/0.98  res_num_in_active:                      0
% 2.49/0.98  res_num_of_loops:                       105
% 2.49/0.98  res_forward_subset_subsumed:            16
% 2.49/0.98  res_backward_subset_subsumed:           0
% 2.49/0.98  res_forward_subsumed:                   0
% 2.49/0.98  res_backward_subsumed:                  0
% 2.49/0.98  res_forward_subsumption_resolution:     5
% 2.49/0.98  res_backward_subsumption_resolution:    0
% 2.49/0.98  res_clause_to_clause_subsumption:       60
% 2.49/0.98  res_orphan_elimination:                 0
% 2.49/0.98  res_tautology_del:                      33
% 2.49/0.98  res_num_eq_res_simplified:              1
% 2.49/0.98  res_num_sel_changes:                    0
% 2.49/0.98  res_moves_from_active_to_pass:          0
% 2.49/0.98  
% 2.49/0.98  ------ Superposition
% 2.49/0.98  
% 2.49/0.98  sup_time_total:                         0.
% 2.49/0.98  sup_time_generating:                    0.
% 2.49/0.98  sup_time_sim_full:                      0.
% 2.49/0.98  sup_time_sim_immed:                     0.
% 2.49/0.98  
% 2.49/0.98  sup_num_of_clauses:                     29
% 2.49/0.98  sup_num_in_active:                      24
% 2.49/0.98  sup_num_in_passive:                     5
% 2.49/0.98  sup_num_of_loops:                       29
% 2.49/0.98  sup_fw_superposition:                   11
% 2.49/0.98  sup_bw_superposition:                   6
% 2.49/0.98  sup_immediate_simplified:               1
% 2.49/0.98  sup_given_eliminated:                   0
% 2.49/0.98  comparisons_done:                       0
% 2.49/0.98  comparisons_avoided:                    5
% 2.49/0.98  
% 2.49/0.98  ------ Simplifications
% 2.49/0.98  
% 2.49/0.98  
% 2.49/0.98  sim_fw_subset_subsumed:                 0
% 2.49/0.98  sim_bw_subset_subsumed:                 3
% 2.49/0.98  sim_fw_subsumed:                        1
% 2.49/0.98  sim_bw_subsumed:                        0
% 2.49/0.98  sim_fw_subsumption_res:                 0
% 2.49/0.98  sim_bw_subsumption_res:                 0
% 2.49/0.98  sim_tautology_del:                      1
% 2.49/0.98  sim_eq_tautology_del:                   3
% 2.49/0.98  sim_eq_res_simp:                        1
% 2.49/0.98  sim_fw_demodulated:                     0
% 2.49/0.98  sim_bw_demodulated:                     4
% 2.49/0.98  sim_light_normalised:                   0
% 2.49/0.98  sim_joinable_taut:                      0
% 2.49/0.98  sim_joinable_simp:                      0
% 2.49/0.98  sim_ac_normalised:                      0
% 2.49/0.98  sim_smt_subsumption:                    0
% 2.49/0.98  
%------------------------------------------------------------------------------
