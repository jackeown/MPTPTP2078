%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:01 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 243 expanded)
%              Number of clauses        :   63 (  80 expanded)
%              Number of leaves         :   18 (  56 expanded)
%              Depth                    :   22
%              Number of atoms          :  421 (1004 expanded)
%              Number of equality atoms :   94 (  97 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
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

fof(f45,plain,
    ( v3_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & v1_xboole_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f44,f43])).

fof(f69,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f72,plain,(
    v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f28])).

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
    inference(flattening,[],[f38])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
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

fof(f42,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1462,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_173,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8,c_1])).

cnf(c_174,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_173])).

cnf(c_1450,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_174])).

cnf(c_2122,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1450])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1453,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2713,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2122,c_1453])).

cnf(c_13,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_14,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_315,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(resolution,[status(thm)],[c_13,c_14])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_354,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_315,c_28])).

cnf(c_355,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_357,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_26])).

cnf(c_1448,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_3046,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
    inference(superposition,[status(thm)],[c_2713,c_1448])).

cnf(c_22,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_333,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_334,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_338,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
    | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_28,c_26])).

cnf(c_1449,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_3054,plain,
    ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3046,c_1449])).

cnf(c_11,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1455,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_25,negated_conjecture,
    ( v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1451,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1460,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2032,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1451,c_1460])).

cnf(c_23,negated_conjecture,
    ( v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_20,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_542,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_543,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_669,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_543])).

cnf(c_670,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_669])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_684,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(k1_xboole_0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_670,c_10])).

cnf(c_711,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_684])).

cnf(c_852,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_711])).

cnf(c_1440,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_852])).

cnf(c_2090,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2032,c_1440])).

cnf(c_2099,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2090])).

cnf(c_2324,plain,
    ( k1_tarski(X0) = k1_xboole_0
    | v2_tex_2(k1_tarski(X0),sK2) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1455,c_2099])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1911,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_2345,plain,
    ( v2_tex_2(k1_tarski(X0),sK2) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2324,c_1911])).

cnf(c_2353,plain,
    ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_2345])).

cnf(c_1624,plain,
    ( m1_subset_1(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_174])).

cnf(c_1695,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1624])).

cnf(c_1696,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1695])).

cnf(c_1615,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1616,plain,
    ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1615])).

cnf(c_356,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_31,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3054,c_2353,c_1696,c_1616,c_356,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.24/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.01  
% 2.24/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.24/1.01  
% 2.24/1.01  ------  iProver source info
% 2.24/1.01  
% 2.24/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.24/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.24/1.01  git: non_committed_changes: false
% 2.24/1.01  git: last_make_outside_of_git: false
% 2.24/1.01  
% 2.24/1.01  ------ 
% 2.24/1.01  
% 2.24/1.01  ------ Input Options
% 2.24/1.01  
% 2.24/1.01  --out_options                           all
% 2.24/1.01  --tptp_safe_out                         true
% 2.24/1.01  --problem_path                          ""
% 2.24/1.01  --include_path                          ""
% 2.24/1.01  --clausifier                            res/vclausify_rel
% 2.24/1.01  --clausifier_options                    --mode clausify
% 2.24/1.01  --stdin                                 false
% 2.24/1.01  --stats_out                             all
% 2.24/1.01  
% 2.24/1.01  ------ General Options
% 2.24/1.01  
% 2.24/1.01  --fof                                   false
% 2.24/1.01  --time_out_real                         305.
% 2.24/1.01  --time_out_virtual                      -1.
% 2.24/1.01  --symbol_type_check                     false
% 2.24/1.01  --clausify_out                          false
% 2.24/1.01  --sig_cnt_out                           false
% 2.24/1.01  --trig_cnt_out                          false
% 2.24/1.01  --trig_cnt_out_tolerance                1.
% 2.24/1.01  --trig_cnt_out_sk_spl                   false
% 2.24/1.01  --abstr_cl_out                          false
% 2.24/1.01  
% 2.24/1.01  ------ Global Options
% 2.24/1.01  
% 2.24/1.01  --schedule                              default
% 2.24/1.01  --add_important_lit                     false
% 2.24/1.01  --prop_solver_per_cl                    1000
% 2.24/1.01  --min_unsat_core                        false
% 2.24/1.01  --soft_assumptions                      false
% 2.24/1.01  --soft_lemma_size                       3
% 2.24/1.01  --prop_impl_unit_size                   0
% 2.24/1.01  --prop_impl_unit                        []
% 2.24/1.01  --share_sel_clauses                     true
% 2.24/1.01  --reset_solvers                         false
% 2.24/1.01  --bc_imp_inh                            [conj_cone]
% 2.24/1.01  --conj_cone_tolerance                   3.
% 2.24/1.01  --extra_neg_conj                        none
% 2.24/1.01  --large_theory_mode                     true
% 2.24/1.01  --prolific_symb_bound                   200
% 2.24/1.01  --lt_threshold                          2000
% 2.24/1.01  --clause_weak_htbl                      true
% 2.24/1.01  --gc_record_bc_elim                     false
% 2.24/1.01  
% 2.24/1.01  ------ Preprocessing Options
% 2.24/1.01  
% 2.24/1.01  --preprocessing_flag                    true
% 2.24/1.01  --time_out_prep_mult                    0.1
% 2.24/1.01  --splitting_mode                        input
% 2.24/1.01  --splitting_grd                         true
% 2.24/1.01  --splitting_cvd                         false
% 2.24/1.01  --splitting_cvd_svl                     false
% 2.24/1.01  --splitting_nvd                         32
% 2.24/1.01  --sub_typing                            true
% 2.24/1.01  --prep_gs_sim                           true
% 2.24/1.01  --prep_unflatten                        true
% 2.24/1.01  --prep_res_sim                          true
% 2.24/1.01  --prep_upred                            true
% 2.24/1.01  --prep_sem_filter                       exhaustive
% 2.24/1.01  --prep_sem_filter_out                   false
% 2.24/1.01  --pred_elim                             true
% 2.24/1.01  --res_sim_input                         true
% 2.24/1.01  --eq_ax_congr_red                       true
% 2.24/1.01  --pure_diseq_elim                       true
% 2.24/1.01  --brand_transform                       false
% 2.24/1.01  --non_eq_to_eq                          false
% 2.24/1.01  --prep_def_merge                        true
% 2.24/1.01  --prep_def_merge_prop_impl              false
% 2.24/1.01  --prep_def_merge_mbd                    true
% 2.24/1.01  --prep_def_merge_tr_red                 false
% 2.24/1.01  --prep_def_merge_tr_cl                  false
% 2.24/1.01  --smt_preprocessing                     true
% 2.24/1.01  --smt_ac_axioms                         fast
% 2.24/1.01  --preprocessed_out                      false
% 2.24/1.01  --preprocessed_stats                    false
% 2.24/1.01  
% 2.24/1.01  ------ Abstraction refinement Options
% 2.24/1.01  
% 2.24/1.01  --abstr_ref                             []
% 2.24/1.01  --abstr_ref_prep                        false
% 2.24/1.01  --abstr_ref_until_sat                   false
% 2.24/1.01  --abstr_ref_sig_restrict                funpre
% 2.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.01  --abstr_ref_under                       []
% 2.24/1.01  
% 2.24/1.01  ------ SAT Options
% 2.24/1.01  
% 2.24/1.01  --sat_mode                              false
% 2.24/1.01  --sat_fm_restart_options                ""
% 2.24/1.01  --sat_gr_def                            false
% 2.24/1.01  --sat_epr_types                         true
% 2.24/1.01  --sat_non_cyclic_types                  false
% 2.24/1.01  --sat_finite_models                     false
% 2.24/1.01  --sat_fm_lemmas                         false
% 2.24/1.01  --sat_fm_prep                           false
% 2.24/1.01  --sat_fm_uc_incr                        true
% 2.24/1.01  --sat_out_model                         small
% 2.24/1.01  --sat_out_clauses                       false
% 2.24/1.01  
% 2.24/1.01  ------ QBF Options
% 2.24/1.01  
% 2.24/1.01  --qbf_mode                              false
% 2.24/1.01  --qbf_elim_univ                         false
% 2.24/1.01  --qbf_dom_inst                          none
% 2.24/1.01  --qbf_dom_pre_inst                      false
% 2.24/1.01  --qbf_sk_in                             false
% 2.24/1.01  --qbf_pred_elim                         true
% 2.24/1.01  --qbf_split                             512
% 2.24/1.01  
% 2.24/1.01  ------ BMC1 Options
% 2.24/1.01  
% 2.24/1.01  --bmc1_incremental                      false
% 2.24/1.01  --bmc1_axioms                           reachable_all
% 2.24/1.01  --bmc1_min_bound                        0
% 2.24/1.01  --bmc1_max_bound                        -1
% 2.24/1.01  --bmc1_max_bound_default                -1
% 2.24/1.01  --bmc1_symbol_reachability              true
% 2.24/1.01  --bmc1_property_lemmas                  false
% 2.24/1.01  --bmc1_k_induction                      false
% 2.24/1.01  --bmc1_non_equiv_states                 false
% 2.24/1.01  --bmc1_deadlock                         false
% 2.24/1.01  --bmc1_ucm                              false
% 2.24/1.01  --bmc1_add_unsat_core                   none
% 2.24/1.01  --bmc1_unsat_core_children              false
% 2.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.01  --bmc1_out_stat                         full
% 2.24/1.01  --bmc1_ground_init                      false
% 2.24/1.01  --bmc1_pre_inst_next_state              false
% 2.24/1.01  --bmc1_pre_inst_state                   false
% 2.24/1.01  --bmc1_pre_inst_reach_state             false
% 2.24/1.01  --bmc1_out_unsat_core                   false
% 2.24/1.01  --bmc1_aig_witness_out                  false
% 2.24/1.01  --bmc1_verbose                          false
% 2.24/1.01  --bmc1_dump_clauses_tptp                false
% 2.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.01  --bmc1_dump_file                        -
% 2.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.01  --bmc1_ucm_extend_mode                  1
% 2.24/1.01  --bmc1_ucm_init_mode                    2
% 2.24/1.01  --bmc1_ucm_cone_mode                    none
% 2.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.01  --bmc1_ucm_relax_model                  4
% 2.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.01  --bmc1_ucm_layered_model                none
% 2.24/1.01  --bmc1_ucm_max_lemma_size               10
% 2.24/1.01  
% 2.24/1.01  ------ AIG Options
% 2.24/1.01  
% 2.24/1.01  --aig_mode                              false
% 2.24/1.01  
% 2.24/1.01  ------ Instantiation Options
% 2.24/1.01  
% 2.24/1.01  --instantiation_flag                    true
% 2.24/1.01  --inst_sos_flag                         false
% 2.24/1.01  --inst_sos_phase                        true
% 2.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.01  --inst_lit_sel_side                     num_symb
% 2.24/1.01  --inst_solver_per_active                1400
% 2.24/1.01  --inst_solver_calls_frac                1.
% 2.24/1.01  --inst_passive_queue_type               priority_queues
% 2.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.01  --inst_passive_queues_freq              [25;2]
% 2.24/1.01  --inst_dismatching                      true
% 2.24/1.01  --inst_eager_unprocessed_to_passive     true
% 2.24/1.01  --inst_prop_sim_given                   true
% 2.24/1.01  --inst_prop_sim_new                     false
% 2.24/1.01  --inst_subs_new                         false
% 2.24/1.01  --inst_eq_res_simp                      false
% 2.24/1.01  --inst_subs_given                       false
% 2.24/1.01  --inst_orphan_elimination               true
% 2.24/1.01  --inst_learning_loop_flag               true
% 2.24/1.01  --inst_learning_start                   3000
% 2.24/1.01  --inst_learning_factor                  2
% 2.24/1.01  --inst_start_prop_sim_after_learn       3
% 2.24/1.01  --inst_sel_renew                        solver
% 2.24/1.01  --inst_lit_activity_flag                true
% 2.24/1.01  --inst_restr_to_given                   false
% 2.24/1.01  --inst_activity_threshold               500
% 2.24/1.01  --inst_out_proof                        true
% 2.24/1.01  
% 2.24/1.01  ------ Resolution Options
% 2.24/1.01  
% 2.24/1.01  --resolution_flag                       true
% 2.24/1.01  --res_lit_sel                           adaptive
% 2.24/1.01  --res_lit_sel_side                      none
% 2.24/1.01  --res_ordering                          kbo
% 2.24/1.01  --res_to_prop_solver                    active
% 2.24/1.01  --res_prop_simpl_new                    false
% 2.24/1.01  --res_prop_simpl_given                  true
% 2.24/1.01  --res_passive_queue_type                priority_queues
% 2.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.01  --res_passive_queues_freq               [15;5]
% 2.24/1.01  --res_forward_subs                      full
% 2.24/1.01  --res_backward_subs                     full
% 2.24/1.01  --res_forward_subs_resolution           true
% 2.24/1.01  --res_backward_subs_resolution          true
% 2.24/1.01  --res_orphan_elimination                true
% 2.24/1.01  --res_time_limit                        2.
% 2.24/1.01  --res_out_proof                         true
% 2.24/1.01  
% 2.24/1.01  ------ Superposition Options
% 2.24/1.01  
% 2.24/1.01  --superposition_flag                    true
% 2.24/1.01  --sup_passive_queue_type                priority_queues
% 2.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.01  --demod_completeness_check              fast
% 2.24/1.01  --demod_use_ground                      true
% 2.24/1.01  --sup_to_prop_solver                    passive
% 2.24/1.01  --sup_prop_simpl_new                    true
% 2.24/1.01  --sup_prop_simpl_given                  true
% 2.24/1.01  --sup_fun_splitting                     false
% 2.24/1.01  --sup_smt_interval                      50000
% 2.24/1.01  
% 2.24/1.01  ------ Superposition Simplification Setup
% 2.24/1.01  
% 2.24/1.01  --sup_indices_passive                   []
% 2.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_full_bw                           [BwDemod]
% 2.24/1.01  --sup_immed_triv                        [TrivRules]
% 2.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_immed_bw_main                     []
% 2.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.01  
% 2.24/1.01  ------ Combination Options
% 2.24/1.01  
% 2.24/1.01  --comb_res_mult                         3
% 2.24/1.01  --comb_sup_mult                         2
% 2.24/1.01  --comb_inst_mult                        10
% 2.24/1.01  
% 2.24/1.01  ------ Debug Options
% 2.24/1.01  
% 2.24/1.01  --dbg_backtrace                         false
% 2.24/1.01  --dbg_dump_prop_clauses                 false
% 2.24/1.01  --dbg_dump_prop_clauses_file            -
% 2.24/1.01  --dbg_out_stat                          false
% 2.24/1.01  ------ Parsing...
% 2.24/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.24/1.01  
% 2.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.24/1.01  
% 2.24/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.24/1.01  
% 2.24/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.24/1.01  ------ Proving...
% 2.24/1.01  ------ Problem Properties 
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  clauses                                 25
% 2.24/1.01  conjectures                             2
% 2.24/1.01  EPR                                     8
% 2.24/1.01  Horn                                    20
% 2.24/1.01  unary                                   7
% 2.24/1.01  binary                                  6
% 2.24/1.01  lits                                    59
% 2.24/1.01  lits eq                                 10
% 2.24/1.01  fd_pure                                 0
% 2.24/1.01  fd_pseudo                               0
% 2.24/1.01  fd_cond                                 5
% 2.24/1.01  fd_pseudo_cond                          0
% 2.24/1.01  AC symbols                              0
% 2.24/1.01  
% 2.24/1.01  ------ Schedule dynamic 5 is on 
% 2.24/1.01  
% 2.24/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  ------ 
% 2.24/1.01  Current options:
% 2.24/1.01  ------ 
% 2.24/1.01  
% 2.24/1.01  ------ Input Options
% 2.24/1.01  
% 2.24/1.01  --out_options                           all
% 2.24/1.01  --tptp_safe_out                         true
% 2.24/1.01  --problem_path                          ""
% 2.24/1.01  --include_path                          ""
% 2.24/1.01  --clausifier                            res/vclausify_rel
% 2.24/1.01  --clausifier_options                    --mode clausify
% 2.24/1.01  --stdin                                 false
% 2.24/1.01  --stats_out                             all
% 2.24/1.01  
% 2.24/1.01  ------ General Options
% 2.24/1.01  
% 2.24/1.01  --fof                                   false
% 2.24/1.01  --time_out_real                         305.
% 2.24/1.01  --time_out_virtual                      -1.
% 2.24/1.01  --symbol_type_check                     false
% 2.24/1.01  --clausify_out                          false
% 2.24/1.01  --sig_cnt_out                           false
% 2.24/1.01  --trig_cnt_out                          false
% 2.24/1.01  --trig_cnt_out_tolerance                1.
% 2.24/1.01  --trig_cnt_out_sk_spl                   false
% 2.24/1.01  --abstr_cl_out                          false
% 2.24/1.01  
% 2.24/1.01  ------ Global Options
% 2.24/1.01  
% 2.24/1.01  --schedule                              default
% 2.24/1.01  --add_important_lit                     false
% 2.24/1.01  --prop_solver_per_cl                    1000
% 2.24/1.01  --min_unsat_core                        false
% 2.24/1.01  --soft_assumptions                      false
% 2.24/1.01  --soft_lemma_size                       3
% 2.24/1.01  --prop_impl_unit_size                   0
% 2.24/1.01  --prop_impl_unit                        []
% 2.24/1.01  --share_sel_clauses                     true
% 2.24/1.01  --reset_solvers                         false
% 2.24/1.01  --bc_imp_inh                            [conj_cone]
% 2.24/1.01  --conj_cone_tolerance                   3.
% 2.24/1.01  --extra_neg_conj                        none
% 2.24/1.01  --large_theory_mode                     true
% 2.24/1.01  --prolific_symb_bound                   200
% 2.24/1.01  --lt_threshold                          2000
% 2.24/1.01  --clause_weak_htbl                      true
% 2.24/1.01  --gc_record_bc_elim                     false
% 2.24/1.01  
% 2.24/1.01  ------ Preprocessing Options
% 2.24/1.01  
% 2.24/1.01  --preprocessing_flag                    true
% 2.24/1.01  --time_out_prep_mult                    0.1
% 2.24/1.01  --splitting_mode                        input
% 2.24/1.01  --splitting_grd                         true
% 2.24/1.01  --splitting_cvd                         false
% 2.24/1.01  --splitting_cvd_svl                     false
% 2.24/1.01  --splitting_nvd                         32
% 2.24/1.01  --sub_typing                            true
% 2.24/1.01  --prep_gs_sim                           true
% 2.24/1.01  --prep_unflatten                        true
% 2.24/1.01  --prep_res_sim                          true
% 2.24/1.01  --prep_upred                            true
% 2.24/1.01  --prep_sem_filter                       exhaustive
% 2.24/1.01  --prep_sem_filter_out                   false
% 2.24/1.01  --pred_elim                             true
% 2.24/1.01  --res_sim_input                         true
% 2.24/1.01  --eq_ax_congr_red                       true
% 2.24/1.01  --pure_diseq_elim                       true
% 2.24/1.01  --brand_transform                       false
% 2.24/1.01  --non_eq_to_eq                          false
% 2.24/1.01  --prep_def_merge                        true
% 2.24/1.01  --prep_def_merge_prop_impl              false
% 2.24/1.01  --prep_def_merge_mbd                    true
% 2.24/1.01  --prep_def_merge_tr_red                 false
% 2.24/1.01  --prep_def_merge_tr_cl                  false
% 2.24/1.01  --smt_preprocessing                     true
% 2.24/1.01  --smt_ac_axioms                         fast
% 2.24/1.01  --preprocessed_out                      false
% 2.24/1.01  --preprocessed_stats                    false
% 2.24/1.01  
% 2.24/1.01  ------ Abstraction refinement Options
% 2.24/1.01  
% 2.24/1.01  --abstr_ref                             []
% 2.24/1.01  --abstr_ref_prep                        false
% 2.24/1.01  --abstr_ref_until_sat                   false
% 2.24/1.01  --abstr_ref_sig_restrict                funpre
% 2.24/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.01  --abstr_ref_under                       []
% 2.24/1.01  
% 2.24/1.01  ------ SAT Options
% 2.24/1.01  
% 2.24/1.01  --sat_mode                              false
% 2.24/1.01  --sat_fm_restart_options                ""
% 2.24/1.01  --sat_gr_def                            false
% 2.24/1.01  --sat_epr_types                         true
% 2.24/1.01  --sat_non_cyclic_types                  false
% 2.24/1.01  --sat_finite_models                     false
% 2.24/1.01  --sat_fm_lemmas                         false
% 2.24/1.01  --sat_fm_prep                           false
% 2.24/1.01  --sat_fm_uc_incr                        true
% 2.24/1.01  --sat_out_model                         small
% 2.24/1.01  --sat_out_clauses                       false
% 2.24/1.01  
% 2.24/1.01  ------ QBF Options
% 2.24/1.01  
% 2.24/1.01  --qbf_mode                              false
% 2.24/1.01  --qbf_elim_univ                         false
% 2.24/1.01  --qbf_dom_inst                          none
% 2.24/1.01  --qbf_dom_pre_inst                      false
% 2.24/1.01  --qbf_sk_in                             false
% 2.24/1.01  --qbf_pred_elim                         true
% 2.24/1.01  --qbf_split                             512
% 2.24/1.01  
% 2.24/1.01  ------ BMC1 Options
% 2.24/1.01  
% 2.24/1.01  --bmc1_incremental                      false
% 2.24/1.01  --bmc1_axioms                           reachable_all
% 2.24/1.01  --bmc1_min_bound                        0
% 2.24/1.01  --bmc1_max_bound                        -1
% 2.24/1.01  --bmc1_max_bound_default                -1
% 2.24/1.01  --bmc1_symbol_reachability              true
% 2.24/1.01  --bmc1_property_lemmas                  false
% 2.24/1.01  --bmc1_k_induction                      false
% 2.24/1.01  --bmc1_non_equiv_states                 false
% 2.24/1.01  --bmc1_deadlock                         false
% 2.24/1.01  --bmc1_ucm                              false
% 2.24/1.01  --bmc1_add_unsat_core                   none
% 2.24/1.01  --bmc1_unsat_core_children              false
% 2.24/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.01  --bmc1_out_stat                         full
% 2.24/1.01  --bmc1_ground_init                      false
% 2.24/1.01  --bmc1_pre_inst_next_state              false
% 2.24/1.01  --bmc1_pre_inst_state                   false
% 2.24/1.01  --bmc1_pre_inst_reach_state             false
% 2.24/1.01  --bmc1_out_unsat_core                   false
% 2.24/1.01  --bmc1_aig_witness_out                  false
% 2.24/1.01  --bmc1_verbose                          false
% 2.24/1.01  --bmc1_dump_clauses_tptp                false
% 2.24/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.01  --bmc1_dump_file                        -
% 2.24/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.01  --bmc1_ucm_extend_mode                  1
% 2.24/1.01  --bmc1_ucm_init_mode                    2
% 2.24/1.01  --bmc1_ucm_cone_mode                    none
% 2.24/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.01  --bmc1_ucm_relax_model                  4
% 2.24/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.01  --bmc1_ucm_layered_model                none
% 2.24/1.01  --bmc1_ucm_max_lemma_size               10
% 2.24/1.01  
% 2.24/1.01  ------ AIG Options
% 2.24/1.01  
% 2.24/1.01  --aig_mode                              false
% 2.24/1.01  
% 2.24/1.01  ------ Instantiation Options
% 2.24/1.01  
% 2.24/1.01  --instantiation_flag                    true
% 2.24/1.01  --inst_sos_flag                         false
% 2.24/1.01  --inst_sos_phase                        true
% 2.24/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.01  --inst_lit_sel_side                     none
% 2.24/1.01  --inst_solver_per_active                1400
% 2.24/1.01  --inst_solver_calls_frac                1.
% 2.24/1.01  --inst_passive_queue_type               priority_queues
% 2.24/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.01  --inst_passive_queues_freq              [25;2]
% 2.24/1.01  --inst_dismatching                      true
% 2.24/1.01  --inst_eager_unprocessed_to_passive     true
% 2.24/1.01  --inst_prop_sim_given                   true
% 2.24/1.01  --inst_prop_sim_new                     false
% 2.24/1.01  --inst_subs_new                         false
% 2.24/1.01  --inst_eq_res_simp                      false
% 2.24/1.01  --inst_subs_given                       false
% 2.24/1.01  --inst_orphan_elimination               true
% 2.24/1.01  --inst_learning_loop_flag               true
% 2.24/1.01  --inst_learning_start                   3000
% 2.24/1.01  --inst_learning_factor                  2
% 2.24/1.01  --inst_start_prop_sim_after_learn       3
% 2.24/1.01  --inst_sel_renew                        solver
% 2.24/1.01  --inst_lit_activity_flag                true
% 2.24/1.01  --inst_restr_to_given                   false
% 2.24/1.01  --inst_activity_threshold               500
% 2.24/1.01  --inst_out_proof                        true
% 2.24/1.01  
% 2.24/1.01  ------ Resolution Options
% 2.24/1.01  
% 2.24/1.01  --resolution_flag                       false
% 2.24/1.01  --res_lit_sel                           adaptive
% 2.24/1.01  --res_lit_sel_side                      none
% 2.24/1.01  --res_ordering                          kbo
% 2.24/1.01  --res_to_prop_solver                    active
% 2.24/1.01  --res_prop_simpl_new                    false
% 2.24/1.01  --res_prop_simpl_given                  true
% 2.24/1.01  --res_passive_queue_type                priority_queues
% 2.24/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.01  --res_passive_queues_freq               [15;5]
% 2.24/1.01  --res_forward_subs                      full
% 2.24/1.01  --res_backward_subs                     full
% 2.24/1.01  --res_forward_subs_resolution           true
% 2.24/1.01  --res_backward_subs_resolution          true
% 2.24/1.01  --res_orphan_elimination                true
% 2.24/1.01  --res_time_limit                        2.
% 2.24/1.01  --res_out_proof                         true
% 2.24/1.01  
% 2.24/1.01  ------ Superposition Options
% 2.24/1.01  
% 2.24/1.01  --superposition_flag                    true
% 2.24/1.01  --sup_passive_queue_type                priority_queues
% 2.24/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.01  --demod_completeness_check              fast
% 2.24/1.01  --demod_use_ground                      true
% 2.24/1.01  --sup_to_prop_solver                    passive
% 2.24/1.01  --sup_prop_simpl_new                    true
% 2.24/1.01  --sup_prop_simpl_given                  true
% 2.24/1.01  --sup_fun_splitting                     false
% 2.24/1.01  --sup_smt_interval                      50000
% 2.24/1.01  
% 2.24/1.01  ------ Superposition Simplification Setup
% 2.24/1.01  
% 2.24/1.01  --sup_indices_passive                   []
% 2.24/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_full_bw                           [BwDemod]
% 2.24/1.01  --sup_immed_triv                        [TrivRules]
% 2.24/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_immed_bw_main                     []
% 2.24/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.01  
% 2.24/1.01  ------ Combination Options
% 2.24/1.01  
% 2.24/1.01  --comb_res_mult                         3
% 2.24/1.01  --comb_sup_mult                         2
% 2.24/1.01  --comb_inst_mult                        10
% 2.24/1.01  
% 2.24/1.01  ------ Debug Options
% 2.24/1.01  
% 2.24/1.01  --dbg_backtrace                         false
% 2.24/1.01  --dbg_dump_prop_clauses                 false
% 2.24/1.01  --dbg_dump_prop_clauses_file            -
% 2.24/1.01  --dbg_out_stat                          false
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  ------ Proving...
% 2.24/1.01  
% 2.24/1.01  
% 2.24/1.01  % SZS status Theorem for theBenchmark.p
% 2.24/1.01  
% 2.24/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.24/1.01  
% 2.24/1.01  fof(f1,axiom,(
% 2.24/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f33,plain,(
% 2.24/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.24/1.02    inference(nnf_transformation,[],[f1])).
% 2.24/1.02  
% 2.24/1.02  fof(f34,plain,(
% 2.24/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.24/1.02    inference(rectify,[],[f33])).
% 2.24/1.02  
% 2.24/1.02  fof(f35,plain,(
% 2.24/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.24/1.02    introduced(choice_axiom,[])).
% 2.24/1.02  
% 2.24/1.02  fof(f36,plain,(
% 2.24/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.24/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.24/1.02  
% 2.24/1.02  fof(f47,plain,(
% 2.24/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f36])).
% 2.24/1.02  
% 2.24/1.02  fof(f6,axiom,(
% 2.24/1.02    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f18,plain,(
% 2.24/1.02    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.24/1.02    inference(ennf_transformation,[],[f6])).
% 2.24/1.02  
% 2.24/1.02  fof(f37,plain,(
% 2.24/1.02    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.24/1.02    inference(nnf_transformation,[],[f18])).
% 2.24/1.02  
% 2.24/1.02  fof(f53,plain,(
% 2.24/1.02    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f37])).
% 2.24/1.02  
% 2.24/1.02  fof(f46,plain,(
% 2.24/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f36])).
% 2.24/1.02  
% 2.24/1.02  fof(f12,axiom,(
% 2.24/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f25,plain,(
% 2.24/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.24/1.02    inference(ennf_transformation,[],[f12])).
% 2.24/1.02  
% 2.24/1.02  fof(f26,plain,(
% 2.24/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.24/1.02    inference(flattening,[],[f25])).
% 2.24/1.02  
% 2.24/1.02  fof(f61,plain,(
% 2.24/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f26])).
% 2.24/1.02  
% 2.24/1.02  fof(f10,axiom,(
% 2.24/1.02    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f22,plain,(
% 2.24/1.02    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(ennf_transformation,[],[f10])).
% 2.24/1.02  
% 2.24/1.02  fof(f59,plain,(
% 2.24/1.02    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f22])).
% 2.24/1.02  
% 2.24/1.02  fof(f11,axiom,(
% 2.24/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f23,plain,(
% 2.24/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.24/1.02    inference(ennf_transformation,[],[f11])).
% 2.24/1.02  
% 2.24/1.02  fof(f24,plain,(
% 2.24/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.24/1.02    inference(flattening,[],[f23])).
% 2.24/1.02  
% 2.24/1.02  fof(f60,plain,(
% 2.24/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f24])).
% 2.24/1.02  
% 2.24/1.02  fof(f15,conjecture,(
% 2.24/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f16,negated_conjecture,(
% 2.24/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.24/1.02    inference(negated_conjecture,[],[f15])).
% 2.24/1.02  
% 2.24/1.02  fof(f31,plain,(
% 2.24/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.24/1.02    inference(ennf_transformation,[],[f16])).
% 2.24/1.02  
% 2.24/1.02  fof(f32,plain,(
% 2.24/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.24/1.02    inference(flattening,[],[f31])).
% 2.24/1.02  
% 2.24/1.02  fof(f44,plain,(
% 2.24/1.02    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK3))) )),
% 2.24/1.02    introduced(choice_axiom,[])).
% 2.24/1.02  
% 2.24/1.02  fof(f43,plain,(
% 2.24/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.24/1.02    introduced(choice_axiom,[])).
% 2.24/1.02  
% 2.24/1.02  fof(f45,plain,(
% 2.24/1.02    (v3_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) & v1_xboole_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.24/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f44,f43])).
% 2.24/1.02  
% 2.24/1.02  fof(f69,plain,(
% 2.24/1.02    ~v2_struct_0(sK2)),
% 2.24/1.02    inference(cnf_transformation,[],[f45])).
% 2.24/1.02  
% 2.24/1.02  fof(f71,plain,(
% 2.24/1.02    l1_pre_topc(sK2)),
% 2.24/1.02    inference(cnf_transformation,[],[f45])).
% 2.24/1.02  
% 2.24/1.02  fof(f14,axiom,(
% 2.24/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f29,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.24/1.02    inference(ennf_transformation,[],[f14])).
% 2.24/1.02  
% 2.24/1.02  fof(f30,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.24/1.02    inference(flattening,[],[f29])).
% 2.24/1.02  
% 2.24/1.02  fof(f68,plain,(
% 2.24/1.02    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f30])).
% 2.24/1.02  
% 2.24/1.02  fof(f70,plain,(
% 2.24/1.02    v2_pre_topc(sK2)),
% 2.24/1.02    inference(cnf_transformation,[],[f45])).
% 2.24/1.02  
% 2.24/1.02  fof(f8,axiom,(
% 2.24/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f19,plain,(
% 2.24/1.02    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.24/1.02    inference(ennf_transformation,[],[f8])).
% 2.24/1.02  
% 2.24/1.02  fof(f57,plain,(
% 2.24/1.02    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f19])).
% 2.24/1.02  
% 2.24/1.02  fof(f72,plain,(
% 2.24/1.02    v1_xboole_0(sK3)),
% 2.24/1.02    inference(cnf_transformation,[],[f45])).
% 2.24/1.02  
% 2.24/1.02  fof(f2,axiom,(
% 2.24/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f17,plain,(
% 2.24/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.24/1.02    inference(ennf_transformation,[],[f2])).
% 2.24/1.02  
% 2.24/1.02  fof(f48,plain,(
% 2.24/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f17])).
% 2.24/1.02  
% 2.24/1.02  fof(f74,plain,(
% 2.24/1.02    v3_tex_2(sK3,sK2)),
% 2.24/1.02    inference(cnf_transformation,[],[f45])).
% 2.24/1.02  
% 2.24/1.02  fof(f4,axiom,(
% 2.24/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f50,plain,(
% 2.24/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f4])).
% 2.24/1.02  
% 2.24/1.02  fof(f13,axiom,(
% 2.24/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f27,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(ennf_transformation,[],[f13])).
% 2.24/1.02  
% 2.24/1.02  fof(f28,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(flattening,[],[f27])).
% 2.24/1.02  
% 2.24/1.02  fof(f38,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(nnf_transformation,[],[f28])).
% 2.24/1.02  
% 2.24/1.02  fof(f39,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(flattening,[],[f38])).
% 2.24/1.02  
% 2.24/1.02  fof(f40,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(rectify,[],[f39])).
% 2.24/1.02  
% 2.24/1.02  fof(f41,plain,(
% 2.24/1.02    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.24/1.02    introduced(choice_axiom,[])).
% 2.24/1.02  
% 2.24/1.02  fof(f42,plain,(
% 2.24/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.24/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f40,f41])).
% 2.24/1.02  
% 2.24/1.02  fof(f63,plain,(
% 2.24/1.02    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f42])).
% 2.24/1.02  
% 2.24/1.02  fof(f7,axiom,(
% 2.24/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f56,plain,(
% 2.24/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.24/1.02    inference(cnf_transformation,[],[f7])).
% 2.24/1.02  
% 2.24/1.02  fof(f3,axiom,(
% 2.24/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f49,plain,(
% 2.24/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.24/1.02    inference(cnf_transformation,[],[f3])).
% 2.24/1.02  
% 2.24/1.02  fof(f5,axiom,(
% 2.24/1.02    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.24/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.24/1.02  
% 2.24/1.02  fof(f51,plain,(
% 2.24/1.02    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.24/1.02    inference(cnf_transformation,[],[f5])).
% 2.24/1.02  
% 2.24/1.02  cnf(c_0,plain,
% 2.24/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.24/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1462,plain,
% 2.24/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 2.24/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_8,plain,
% 2.24/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.24/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1,plain,
% 2.24/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.24/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_173,plain,
% 2.24/1.02      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.24/1.02      inference(global_propositional_subsumption,[status(thm)],[c_8,c_1]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_174,plain,
% 2.24/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.24/1.02      inference(renaming,[status(thm)],[c_173]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1450,plain,
% 2.24/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 2.24/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_174]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2122,plain,
% 2.24/1.02      ( m1_subset_1(sK0(X0),X0) = iProver_top
% 2.24/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_1462,c_1450]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_15,plain,
% 2.24/1.02      ( ~ m1_subset_1(X0,X1)
% 2.24/1.02      | v1_xboole_0(X1)
% 2.24/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.24/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1453,plain,
% 2.24/1.02      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.24/1.02      | m1_subset_1(X1,X0) != iProver_top
% 2.24/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2713,plain,
% 2.24/1.02      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.24/1.02      | v1_xboole_0(X0) = iProver_top ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_2122,c_1453]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_13,plain,
% 2.24/1.02      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.24/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_14,plain,
% 2.24/1.02      ( v2_struct_0(X0)
% 2.24/1.02      | ~ l1_struct_0(X0)
% 2.24/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.24/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_315,plain,
% 2.24/1.02      ( v2_struct_0(X0)
% 2.24/1.02      | ~ l1_pre_topc(X0)
% 2.24/1.02      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.24/1.02      inference(resolution,[status(thm)],[c_13,c_14]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_28,negated_conjecture,
% 2.24/1.02      ( ~ v2_struct_0(sK2) ),
% 2.24/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_354,plain,
% 2.24/1.02      ( ~ l1_pre_topc(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 2.24/1.02      inference(resolution_lifted,[status(thm)],[c_315,c_28]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_355,plain,
% 2.24/1.02      ( ~ l1_pre_topc(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.24/1.02      inference(unflattening,[status(thm)],[c_354]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_26,negated_conjecture,
% 2.24/1.02      ( l1_pre_topc(sK2) ),
% 2.24/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_357,plain,
% 2.24/1.02      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.24/1.02      inference(global_propositional_subsumption,
% 2.24/1.02                [status(thm)],
% 2.24/1.02                [c_355,c_26]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1448,plain,
% 2.24/1.02      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_3046,plain,
% 2.24/1.02      ( k6_domain_1(u1_struct_0(sK2),sK0(u1_struct_0(sK2))) = k1_tarski(sK0(u1_struct_0(sK2))) ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_2713,c_1448]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_22,plain,
% 2.24/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.24/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.24/1.02      | ~ v2_pre_topc(X0)
% 2.24/1.02      | v2_struct_0(X0)
% 2.24/1.02      | ~ l1_pre_topc(X0) ),
% 2.24/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_27,negated_conjecture,
% 2.24/1.02      ( v2_pre_topc(sK2) ),
% 2.24/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_333,plain,
% 2.24/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.24/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.24/1.02      | v2_struct_0(X0)
% 2.24/1.02      | ~ l1_pre_topc(X0)
% 2.24/1.02      | sK2 != X0 ),
% 2.24/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_334,plain,
% 2.24/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2))
% 2.24/1.02      | v2_struct_0(sK2)
% 2.24/1.02      | ~ l1_pre_topc(sK2) ),
% 2.24/1.02      inference(unflattening,[status(thm)],[c_333]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_338,plain,
% 2.24/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ),
% 2.24/1.02      inference(global_propositional_subsumption,
% 2.24/1.02                [status(thm)],
% 2.24/1.02                [c_334,c_28,c_26]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1449,plain,
% 2.24/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK2),X0),sK2) = iProver_top
% 2.24/1.02      | m1_subset_1(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_3054,plain,
% 2.24/1.02      ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) = iProver_top
% 2.24/1.02      | m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_3046,c_1449]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_11,plain,
% 2.24/1.02      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 2.24/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1455,plain,
% 2.24/1.02      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) = iProver_top
% 2.24/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_25,negated_conjecture,
% 2.24/1.02      ( v1_xboole_0(sK3) ),
% 2.24/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1451,plain,
% 2.24/1.02      ( v1_xboole_0(sK3) = iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2,plain,
% 2.24/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.24/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1460,plain,
% 2.24/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2032,plain,
% 2.24/1.02      ( sK3 = k1_xboole_0 ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_1451,c_1460]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_23,negated_conjecture,
% 2.24/1.02      ( v3_tex_2(sK3,sK2) ),
% 2.24/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_4,plain,
% 2.24/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.24/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_20,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,X1)
% 2.24/1.02      | ~ v3_tex_2(X2,X1)
% 2.24/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.24/1.02      | ~ r1_tarski(X2,X0)
% 2.24/1.02      | ~ l1_pre_topc(X1)
% 2.24/1.02      | X0 = X2 ),
% 2.24/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_542,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,X1)
% 2.24/1.02      | ~ v3_tex_2(X2,X1)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.24/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.24/1.02      | ~ r1_tarski(X2,X0)
% 2.24/1.02      | X2 = X0
% 2.24/1.02      | sK2 != X1 ),
% 2.24/1.02      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_543,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ v3_tex_2(X1,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | ~ r1_tarski(X1,X0)
% 2.24/1.02      | X1 = X0 ),
% 2.24/1.02      inference(unflattening,[status(thm)],[c_542]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_669,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ v3_tex_2(X1,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | X0 != X2
% 2.24/1.02      | X0 = X1
% 2.24/1.02      | k1_xboole_0 != X1 ),
% 2.24/1.02      inference(resolution_lifted,[status(thm)],[c_4,c_543]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_670,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | X0 = k1_xboole_0 ),
% 2.24/1.02      inference(unflattening,[status(thm)],[c_669]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_10,plain,
% 2.24/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.24/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_684,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ v3_tex_2(k1_xboole_0,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | X0 = k1_xboole_0 ),
% 2.24/1.02      inference(forward_subsumption_resolution,
% 2.24/1.02                [status(thm)],
% 2.24/1.02                [c_670,c_10]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_711,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | sK2 != sK2
% 2.24/1.02      | sK3 != k1_xboole_0
% 2.24/1.02      | k1_xboole_0 = X0 ),
% 2.24/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_684]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_852,plain,
% 2.24/1.02      ( ~ v2_tex_2(X0,sK2)
% 2.24/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.24/1.02      | sK3 != k1_xboole_0
% 2.24/1.02      | k1_xboole_0 = X0 ),
% 2.24/1.02      inference(equality_resolution_simp,[status(thm)],[c_711]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1440,plain,
% 2.24/1.02      ( sK3 != k1_xboole_0
% 2.24/1.02      | k1_xboole_0 = X0
% 2.24/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 2.24/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_852]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2090,plain,
% 2.24/1.02      ( k1_xboole_0 = X0
% 2.24/1.02      | k1_xboole_0 != k1_xboole_0
% 2.24/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 2.24/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.24/1.02      inference(demodulation,[status(thm)],[c_2032,c_1440]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2099,plain,
% 2.24/1.02      ( k1_xboole_0 = X0
% 2.24/1.02      | v2_tex_2(X0,sK2) != iProver_top
% 2.24/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.24/1.02      inference(equality_resolution_simp,[status(thm)],[c_2090]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2324,plain,
% 2.24/1.02      ( k1_tarski(X0) = k1_xboole_0
% 2.24/1.02      | v2_tex_2(k1_tarski(X0),sK2) != iProver_top
% 2.24/1.02      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_1455,c_2099]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_3,plain,
% 2.24/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.24/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_5,plain,
% 2.24/1.02      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.24/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1911,plain,
% 2.24/1.02      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2345,plain,
% 2.24/1.02      ( v2_tex_2(k1_tarski(X0),sK2) != iProver_top
% 2.24/1.02      | r2_hidden(X0,u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(global_propositional_subsumption,
% 2.24/1.02                [status(thm)],
% 2.24/1.02                [c_2324,c_1911]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_2353,plain,
% 2.24/1.02      ( v2_tex_2(k1_tarski(sK0(u1_struct_0(sK2))),sK2) != iProver_top
% 2.24/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.24/1.02      inference(superposition,[status(thm)],[c_1462,c_2345]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1624,plain,
% 2.24/1.02      ( m1_subset_1(X0,u1_struct_0(sK2))
% 2.24/1.02      | ~ r2_hidden(X0,u1_struct_0(sK2)) ),
% 2.24/1.02      inference(instantiation,[status(thm)],[c_174]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1695,plain,
% 2.24/1.02      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
% 2.24/1.02      | ~ r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
% 2.24/1.02      inference(instantiation,[status(thm)],[c_1624]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1696,plain,
% 2.24/1.02      ( m1_subset_1(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
% 2.24/1.02      | r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_1695]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1615,plain,
% 2.24/1.02      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2))
% 2.24/1.02      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.24/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_1616,plain,
% 2.24/1.02      ( r2_hidden(sK0(u1_struct_0(sK2)),u1_struct_0(sK2)) = iProver_top
% 2.24/1.02      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_1615]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_356,plain,
% 2.24/1.02      ( l1_pre_topc(sK2) != iProver_top
% 2.24/1.02      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(c_31,plain,
% 2.24/1.02      ( l1_pre_topc(sK2) = iProver_top ),
% 2.24/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.24/1.02  
% 2.24/1.02  cnf(contradiction,plain,
% 2.24/1.02      ( $false ),
% 2.24/1.02      inference(minisat,
% 2.24/1.02                [status(thm)],
% 2.24/1.02                [c_3054,c_2353,c_1696,c_1616,c_356,c_31]) ).
% 2.24/1.02  
% 2.24/1.02  
% 2.24/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.24/1.02  
% 2.24/1.02  ------                               Statistics
% 2.24/1.02  
% 2.24/1.02  ------ General
% 2.24/1.02  
% 2.24/1.02  abstr_ref_over_cycles:                  0
% 2.24/1.02  abstr_ref_under_cycles:                 0
% 2.24/1.02  gc_basic_clause_elim:                   0
% 2.24/1.02  forced_gc_time:                         0
% 2.24/1.02  parsing_time:                           0.008
% 2.24/1.02  unif_index_cands_time:                  0.
% 2.24/1.02  unif_index_add_time:                    0.
% 2.24/1.02  orderings_time:                         0.
% 2.24/1.02  out_proof_time:                         0.01
% 2.24/1.02  total_time:                             0.111
% 2.24/1.02  num_of_symbols:                         52
% 2.24/1.02  num_of_terms:                           1888
% 2.24/1.02  
% 2.24/1.02  ------ Preprocessing
% 2.24/1.02  
% 2.24/1.02  num_of_splits:                          3
% 2.24/1.02  num_of_split_atoms:                     1
% 2.24/1.02  num_of_reused_defs:                     2
% 2.24/1.02  num_eq_ax_congr_red:                    16
% 2.24/1.02  num_of_sem_filtered_clauses:            1
% 2.24/1.02  num_of_subtypes:                        0
% 2.24/1.02  monotx_restored_types:                  0
% 2.24/1.02  sat_num_of_epr_types:                   0
% 2.24/1.02  sat_num_of_non_cyclic_types:            0
% 2.24/1.02  sat_guarded_non_collapsed_types:        0
% 2.24/1.02  num_pure_diseq_elim:                    0
% 2.24/1.02  simp_replaced_by:                       0
% 2.24/1.02  res_preprocessed:                       120
% 2.24/1.02  prep_upred:                             0
% 2.24/1.02  prep_unflattend:                        40
% 2.24/1.02  smt_new_axioms:                         0
% 2.24/1.02  pred_elim_cands:                        4
% 2.24/1.02  pred_elim:                              6
% 2.24/1.02  pred_elim_cl:                           7
% 2.24/1.02  pred_elim_cycles:                       10
% 2.24/1.02  merged_defs:                            0
% 2.24/1.02  merged_defs_ncl:                        0
% 2.24/1.02  bin_hyper_res:                          0
% 2.24/1.02  prep_cycles:                            4
% 2.24/1.02  pred_elim_time:                         0.011
% 2.24/1.02  splitting_time:                         0.
% 2.24/1.02  sem_filter_time:                        0.
% 2.24/1.02  monotx_time:                            0.001
% 2.24/1.02  subtype_inf_time:                       0.
% 2.24/1.02  
% 2.24/1.02  ------ Problem properties
% 2.24/1.02  
% 2.24/1.02  clauses:                                25
% 2.24/1.02  conjectures:                            2
% 2.24/1.02  epr:                                    8
% 2.24/1.02  horn:                                   20
% 2.24/1.02  ground:                                 7
% 2.24/1.02  unary:                                  7
% 2.24/1.02  binary:                                 6
% 2.24/1.02  lits:                                   59
% 2.24/1.02  lits_eq:                                10
% 2.24/1.02  fd_pure:                                0
% 2.24/1.02  fd_pseudo:                              0
% 2.24/1.02  fd_cond:                                5
% 2.24/1.02  fd_pseudo_cond:                         0
% 2.24/1.02  ac_symbols:                             0
% 2.24/1.02  
% 2.24/1.02  ------ Propositional Solver
% 2.24/1.02  
% 2.24/1.02  prop_solver_calls:                      27
% 2.24/1.02  prop_fast_solver_calls:                 821
% 2.24/1.02  smt_solver_calls:                       0
% 2.24/1.02  smt_fast_solver_calls:                  0
% 2.24/1.02  prop_num_of_clauses:                    890
% 2.24/1.02  prop_preprocess_simplified:             4103
% 2.24/1.02  prop_fo_subsumed:                       16
% 2.24/1.02  prop_solver_time:                       0.
% 2.24/1.02  smt_solver_time:                        0.
% 2.24/1.02  smt_fast_solver_time:                   0.
% 2.24/1.02  prop_fast_solver_time:                  0.
% 2.24/1.02  prop_unsat_core_time:                   0.
% 2.24/1.02  
% 2.24/1.02  ------ QBF
% 2.24/1.02  
% 2.24/1.02  qbf_q_res:                              0
% 2.24/1.02  qbf_num_tautologies:                    0
% 2.24/1.02  qbf_prep_cycles:                        0
% 2.24/1.02  
% 2.24/1.02  ------ BMC1
% 2.24/1.02  
% 2.24/1.02  bmc1_current_bound:                     -1
% 2.24/1.02  bmc1_last_solved_bound:                 -1
% 2.24/1.02  bmc1_unsat_core_size:                   -1
% 2.24/1.02  bmc1_unsat_core_parents_size:           -1
% 2.24/1.02  bmc1_merge_next_fun:                    0
% 2.24/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.24/1.02  
% 2.24/1.02  ------ Instantiation
% 2.24/1.02  
% 2.24/1.02  inst_num_of_clauses:                    262
% 2.24/1.02  inst_num_in_passive:                    77
% 2.24/1.02  inst_num_in_active:                     149
% 2.24/1.02  inst_num_in_unprocessed:                36
% 2.24/1.02  inst_num_of_loops:                      210
% 2.24/1.02  inst_num_of_learning_restarts:          0
% 2.24/1.02  inst_num_moves_active_passive:          58
% 2.24/1.02  inst_lit_activity:                      0
% 2.24/1.02  inst_lit_activity_moves:                0
% 2.24/1.02  inst_num_tautologies:                   0
% 2.24/1.02  inst_num_prop_implied:                  0
% 2.24/1.02  inst_num_existing_simplified:           0
% 2.24/1.02  inst_num_eq_res_simplified:             0
% 2.24/1.02  inst_num_child_elim:                    0
% 2.24/1.02  inst_num_of_dismatching_blockings:      31
% 2.24/1.02  inst_num_of_non_proper_insts:           194
% 2.24/1.02  inst_num_of_duplicates:                 0
% 2.24/1.02  inst_inst_num_from_inst_to_res:         0
% 2.24/1.02  inst_dismatching_checking_time:         0.
% 2.24/1.02  
% 2.24/1.02  ------ Resolution
% 2.24/1.02  
% 2.24/1.02  res_num_of_clauses:                     0
% 2.24/1.02  res_num_in_passive:                     0
% 2.24/1.02  res_num_in_active:                      0
% 2.24/1.02  res_num_of_loops:                       124
% 2.24/1.02  res_forward_subset_subsumed:            50
% 2.24/1.02  res_backward_subset_subsumed:           0
% 2.24/1.02  res_forward_subsumed:                   0
% 2.24/1.02  res_backward_subsumed:                  0
% 2.24/1.02  res_forward_subsumption_resolution:     5
% 2.24/1.02  res_backward_subsumption_resolution:    0
% 2.24/1.02  res_clause_to_clause_subsumption:       97
% 2.24/1.02  res_orphan_elimination:                 0
% 2.24/1.02  res_tautology_del:                      21
% 2.24/1.02  res_num_eq_res_simplified:              1
% 2.24/1.02  res_num_sel_changes:                    0
% 2.24/1.02  res_moves_from_active_to_pass:          0
% 2.24/1.02  
% 2.24/1.02  ------ Superposition
% 2.24/1.02  
% 2.24/1.02  sup_time_total:                         0.
% 2.24/1.02  sup_time_generating:                    0.
% 2.24/1.02  sup_time_sim_full:                      0.
% 2.24/1.02  sup_time_sim_immed:                     0.
% 2.24/1.02  
% 2.24/1.02  sup_num_of_clauses:                     47
% 2.24/1.02  sup_num_in_active:                      36
% 2.24/1.02  sup_num_in_passive:                     11
% 2.24/1.02  sup_num_of_loops:                       41
% 2.24/1.02  sup_fw_superposition:                   25
% 2.24/1.02  sup_bw_superposition:                   19
% 2.24/1.02  sup_immediate_simplified:               9
% 2.24/1.02  sup_given_eliminated:                   0
% 2.24/1.02  comparisons_done:                       0
% 2.24/1.02  comparisons_avoided:                    3
% 2.24/1.02  
% 2.24/1.02  ------ Simplifications
% 2.24/1.02  
% 2.24/1.02  
% 2.24/1.02  sim_fw_subset_subsumed:                 6
% 2.24/1.02  sim_bw_subset_subsumed:                 3
% 2.24/1.02  sim_fw_subsumed:                        3
% 2.24/1.02  sim_bw_subsumed:                        0
% 2.24/1.02  sim_fw_subsumption_res:                 0
% 2.24/1.02  sim_bw_subsumption_res:                 0
% 2.24/1.02  sim_tautology_del:                      7
% 2.24/1.02  sim_eq_tautology_del:                   3
% 2.24/1.02  sim_eq_res_simp:                        1
% 2.24/1.02  sim_fw_demodulated:                     0
% 2.24/1.02  sim_bw_demodulated:                     4
% 2.24/1.02  sim_light_normalised:                   0
% 2.24/1.02  sim_joinable_taut:                      0
% 2.24/1.02  sim_joinable_simp:                      0
% 2.24/1.02  sim_ac_normalised:                      0
% 2.24/1.02  sim_smt_subsumption:                    0
% 2.24/1.02  
%------------------------------------------------------------------------------
