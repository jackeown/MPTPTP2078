%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:59 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 724 expanded)
%              Number of clauses        :   70 ( 201 expanded)
%              Number of leaves         :   20 ( 188 expanded)
%              Depth                    :   22
%              Number of atoms          :  464 (3321 expanded)
%              Number of equality atoms :  108 ( 208 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK1(X0))
        & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f38])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( v3_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & v1_xboole_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f46,f45])).

fof(f69,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f68,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f70,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f73,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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

fof(f30,plain,(
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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f5,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_10,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_24,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_340,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_24])).

cnf(c_341,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_343,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_25,c_23])).

cnf(c_1240,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_2,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_300,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | X2 != X3
    | sK0(X3) != X0
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_8])).

cnf(c_301,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(sK0(X0),X1)
    | k1_xboole_0 = X0 ),
    inference(unflattening,[status(thm)],[c_300])).

cnf(c_1242,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(sK0(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_2107,plain,
    ( sK1(sK3) = k1_xboole_0
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1240,c_1242])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_9,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_351,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_24])).

cnf(c_352,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_882,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1401,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK3))
    | sK1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_882])).

cnf(c_1403,plain,
    ( v1_xboole_0(sK1(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2440,plain,
    ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2107,c_25,c_23,c_0,c_352,c_1403])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1246,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2445,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2440,c_1246])).

cnf(c_26,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_28,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_342,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_353,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1480,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1391])).

cnf(c_1481,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1480])).

cnf(c_2542,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2445,c_26,c_28,c_342,c_353,c_1481])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1247,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2545,plain,
    ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1247])).

cnf(c_2760,plain,
    ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2545,c_25,c_26,c_23,c_28,c_0,c_342,c_352,c_353,c_1403,c_1481,c_2107])).

cnf(c_22,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1244,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1251,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1811,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1244,c_1251])).

cnf(c_20,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_457,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_458,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_584,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_458])).

cnf(c_585,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_599,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_585,c_5])).

cnf(c_626,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_599])).

cnf(c_766,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_626])).

cnf(c_1231,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_766])).

cnf(c_1815,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1811,c_1231])).

cnf(c_1822,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_1815])).

cnf(c_2768,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2760,c_1822])).

cnf(c_19,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_322,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_323,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_327,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_323,c_25,c_23])).

cnf(c_1241,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_2546,plain,
    ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
    | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1241])).

cnf(c_2981,plain,
    ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2768,c_25,c_23,c_0,c_352,c_1403,c_2107,c_2546])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1250,plain,
    ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2989,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2981,c_1250])).

cnf(c_87,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2989,c_87])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:54:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.40/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.40/1.00  
% 2.40/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.00  
% 2.40/1.00  ------  iProver source info
% 2.40/1.00  
% 2.40/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.00  git: non_committed_changes: false
% 2.40/1.00  git: last_make_outside_of_git: false
% 2.40/1.00  
% 2.40/1.00  ------ 
% 2.40/1.00  
% 2.40/1.00  ------ Input Options
% 2.40/1.00  
% 2.40/1.00  --out_options                           all
% 2.40/1.00  --tptp_safe_out                         true
% 2.40/1.00  --problem_path                          ""
% 2.40/1.00  --include_path                          ""
% 2.40/1.00  --clausifier                            res/vclausify_rel
% 2.40/1.00  --clausifier_options                    --mode clausify
% 2.40/1.00  --stdin                                 false
% 2.40/1.00  --stats_out                             all
% 2.40/1.00  
% 2.40/1.00  ------ General Options
% 2.40/1.00  
% 2.40/1.00  --fof                                   false
% 2.40/1.00  --time_out_real                         305.
% 2.40/1.00  --time_out_virtual                      -1.
% 2.40/1.00  --symbol_type_check                     false
% 2.40/1.00  --clausify_out                          false
% 2.40/1.00  --sig_cnt_out                           false
% 2.40/1.00  --trig_cnt_out                          false
% 2.40/1.00  --trig_cnt_out_tolerance                1.
% 2.40/1.00  --trig_cnt_out_sk_spl                   false
% 2.40/1.00  --abstr_cl_out                          false
% 2.40/1.00  
% 2.40/1.00  ------ Global Options
% 2.40/1.00  
% 2.40/1.00  --schedule                              default
% 2.40/1.00  --add_important_lit                     false
% 2.40/1.00  --prop_solver_per_cl                    1000
% 2.40/1.00  --min_unsat_core                        false
% 2.40/1.00  --soft_assumptions                      false
% 2.40/1.00  --soft_lemma_size                       3
% 2.40/1.00  --prop_impl_unit_size                   0
% 2.40/1.00  --prop_impl_unit                        []
% 2.40/1.00  --share_sel_clauses                     true
% 2.40/1.00  --reset_solvers                         false
% 2.40/1.00  --bc_imp_inh                            [conj_cone]
% 2.40/1.00  --conj_cone_tolerance                   3.
% 2.40/1.00  --extra_neg_conj                        none
% 2.40/1.00  --large_theory_mode                     true
% 2.40/1.00  --prolific_symb_bound                   200
% 2.40/1.00  --lt_threshold                          2000
% 2.40/1.00  --clause_weak_htbl                      true
% 2.40/1.00  --gc_record_bc_elim                     false
% 2.40/1.00  
% 2.40/1.00  ------ Preprocessing Options
% 2.40/1.00  
% 2.40/1.00  --preprocessing_flag                    true
% 2.40/1.00  --time_out_prep_mult                    0.1
% 2.40/1.00  --splitting_mode                        input
% 2.40/1.00  --splitting_grd                         true
% 2.40/1.00  --splitting_cvd                         false
% 2.40/1.00  --splitting_cvd_svl                     false
% 2.40/1.00  --splitting_nvd                         32
% 2.40/1.00  --sub_typing                            true
% 2.40/1.00  --prep_gs_sim                           true
% 2.40/1.00  --prep_unflatten                        true
% 2.40/1.00  --prep_res_sim                          true
% 2.40/1.00  --prep_upred                            true
% 2.40/1.00  --prep_sem_filter                       exhaustive
% 2.40/1.00  --prep_sem_filter_out                   false
% 2.40/1.00  --pred_elim                             true
% 2.40/1.00  --res_sim_input                         true
% 2.40/1.00  --eq_ax_congr_red                       true
% 2.40/1.00  --pure_diseq_elim                       true
% 2.40/1.00  --brand_transform                       false
% 2.40/1.00  --non_eq_to_eq                          false
% 2.40/1.00  --prep_def_merge                        true
% 2.40/1.00  --prep_def_merge_prop_impl              false
% 2.40/1.00  --prep_def_merge_mbd                    true
% 2.40/1.00  --prep_def_merge_tr_red                 false
% 2.40/1.00  --prep_def_merge_tr_cl                  false
% 2.40/1.00  --smt_preprocessing                     true
% 2.40/1.00  --smt_ac_axioms                         fast
% 2.40/1.00  --preprocessed_out                      false
% 2.40/1.00  --preprocessed_stats                    false
% 2.40/1.00  
% 2.40/1.00  ------ Abstraction refinement Options
% 2.40/1.00  
% 2.40/1.00  --abstr_ref                             []
% 2.40/1.00  --abstr_ref_prep                        false
% 2.40/1.00  --abstr_ref_until_sat                   false
% 2.40/1.00  --abstr_ref_sig_restrict                funpre
% 2.40/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.00  --abstr_ref_under                       []
% 2.40/1.00  
% 2.40/1.00  ------ SAT Options
% 2.40/1.00  
% 2.40/1.00  --sat_mode                              false
% 2.40/1.00  --sat_fm_restart_options                ""
% 2.40/1.00  --sat_gr_def                            false
% 2.40/1.00  --sat_epr_types                         true
% 2.40/1.00  --sat_non_cyclic_types                  false
% 2.40/1.00  --sat_finite_models                     false
% 2.40/1.00  --sat_fm_lemmas                         false
% 2.40/1.00  --sat_fm_prep                           false
% 2.40/1.00  --sat_fm_uc_incr                        true
% 2.40/1.00  --sat_out_model                         small
% 2.40/1.00  --sat_out_clauses                       false
% 2.40/1.00  
% 2.40/1.00  ------ QBF Options
% 2.40/1.00  
% 2.40/1.00  --qbf_mode                              false
% 2.40/1.00  --qbf_elim_univ                         false
% 2.40/1.00  --qbf_dom_inst                          none
% 2.40/1.00  --qbf_dom_pre_inst                      false
% 2.40/1.00  --qbf_sk_in                             false
% 2.40/1.00  --qbf_pred_elim                         true
% 2.40/1.00  --qbf_split                             512
% 2.40/1.00  
% 2.40/1.00  ------ BMC1 Options
% 2.40/1.00  
% 2.40/1.00  --bmc1_incremental                      false
% 2.40/1.00  --bmc1_axioms                           reachable_all
% 2.40/1.00  --bmc1_min_bound                        0
% 2.40/1.00  --bmc1_max_bound                        -1
% 2.40/1.00  --bmc1_max_bound_default                -1
% 2.40/1.00  --bmc1_symbol_reachability              true
% 2.40/1.00  --bmc1_property_lemmas                  false
% 2.40/1.00  --bmc1_k_induction                      false
% 2.40/1.00  --bmc1_non_equiv_states                 false
% 2.40/1.00  --bmc1_deadlock                         false
% 2.40/1.00  --bmc1_ucm                              false
% 2.40/1.00  --bmc1_add_unsat_core                   none
% 2.40/1.00  --bmc1_unsat_core_children              false
% 2.40/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.00  --bmc1_out_stat                         full
% 2.40/1.00  --bmc1_ground_init                      false
% 2.40/1.00  --bmc1_pre_inst_next_state              false
% 2.40/1.00  --bmc1_pre_inst_state                   false
% 2.40/1.00  --bmc1_pre_inst_reach_state             false
% 2.40/1.00  --bmc1_out_unsat_core                   false
% 2.40/1.00  --bmc1_aig_witness_out                  false
% 2.40/1.00  --bmc1_verbose                          false
% 2.40/1.00  --bmc1_dump_clauses_tptp                false
% 2.40/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.00  --bmc1_dump_file                        -
% 2.40/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.00  --bmc1_ucm_extend_mode                  1
% 2.40/1.00  --bmc1_ucm_init_mode                    2
% 2.40/1.00  --bmc1_ucm_cone_mode                    none
% 2.40/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.00  --bmc1_ucm_relax_model                  4
% 2.40/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.00  --bmc1_ucm_layered_model                none
% 2.40/1.00  --bmc1_ucm_max_lemma_size               10
% 2.40/1.00  
% 2.40/1.00  ------ AIG Options
% 2.40/1.00  
% 2.40/1.00  --aig_mode                              false
% 2.40/1.00  
% 2.40/1.00  ------ Instantiation Options
% 2.40/1.00  
% 2.40/1.00  --instantiation_flag                    true
% 2.40/1.00  --inst_sos_flag                         false
% 2.40/1.00  --inst_sos_phase                        true
% 2.40/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.00  --inst_lit_sel_side                     num_symb
% 2.40/1.00  --inst_solver_per_active                1400
% 2.40/1.00  --inst_solver_calls_frac                1.
% 2.40/1.00  --inst_passive_queue_type               priority_queues
% 2.40/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.00  --inst_passive_queues_freq              [25;2]
% 2.40/1.00  --inst_dismatching                      true
% 2.40/1.00  --inst_eager_unprocessed_to_passive     true
% 2.40/1.00  --inst_prop_sim_given                   true
% 2.40/1.00  --inst_prop_sim_new                     false
% 2.40/1.00  --inst_subs_new                         false
% 2.40/1.00  --inst_eq_res_simp                      false
% 2.40/1.00  --inst_subs_given                       false
% 2.40/1.00  --inst_orphan_elimination               true
% 2.40/1.00  --inst_learning_loop_flag               true
% 2.40/1.00  --inst_learning_start                   3000
% 2.40/1.00  --inst_learning_factor                  2
% 2.40/1.00  --inst_start_prop_sim_after_learn       3
% 2.40/1.00  --inst_sel_renew                        solver
% 2.40/1.00  --inst_lit_activity_flag                true
% 2.40/1.00  --inst_restr_to_given                   false
% 2.40/1.00  --inst_activity_threshold               500
% 2.40/1.00  --inst_out_proof                        true
% 2.40/1.00  
% 2.40/1.00  ------ Resolution Options
% 2.40/1.00  
% 2.40/1.00  --resolution_flag                       true
% 2.40/1.00  --res_lit_sel                           adaptive
% 2.40/1.00  --res_lit_sel_side                      none
% 2.40/1.00  --res_ordering                          kbo
% 2.40/1.00  --res_to_prop_solver                    active
% 2.40/1.00  --res_prop_simpl_new                    false
% 2.40/1.00  --res_prop_simpl_given                  true
% 2.40/1.00  --res_passive_queue_type                priority_queues
% 2.40/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.00  --res_passive_queues_freq               [15;5]
% 2.40/1.00  --res_forward_subs                      full
% 2.40/1.00  --res_backward_subs                     full
% 2.40/1.00  --res_forward_subs_resolution           true
% 2.40/1.00  --res_backward_subs_resolution          true
% 2.40/1.00  --res_orphan_elimination                true
% 2.40/1.00  --res_time_limit                        2.
% 2.40/1.00  --res_out_proof                         true
% 2.40/1.00  
% 2.40/1.00  ------ Superposition Options
% 2.40/1.00  
% 2.40/1.00  --superposition_flag                    true
% 2.40/1.00  --sup_passive_queue_type                priority_queues
% 2.40/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.00  --demod_completeness_check              fast
% 2.40/1.00  --demod_use_ground                      true
% 2.40/1.00  --sup_to_prop_solver                    passive
% 2.40/1.00  --sup_prop_simpl_new                    true
% 2.40/1.00  --sup_prop_simpl_given                  true
% 2.40/1.00  --sup_fun_splitting                     false
% 2.40/1.00  --sup_smt_interval                      50000
% 2.40/1.00  
% 2.40/1.00  ------ Superposition Simplification Setup
% 2.40/1.00  
% 2.40/1.00  --sup_indices_passive                   []
% 2.40/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.00  --sup_full_bw                           [BwDemod]
% 2.40/1.00  --sup_immed_triv                        [TrivRules]
% 2.40/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.00  --sup_immed_bw_main                     []
% 2.40/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  ------ Parsing...
% 2.40/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/1.01  ------ Proving...
% 2.40/1.01  ------ Problem Properties 
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  clauses                                 22
% 2.40/1.01  conjectures                             2
% 2.40/1.01  EPR                                     4
% 2.40/1.01  Horn                                    16
% 2.40/1.01  unary                                   8
% 2.40/1.01  binary                                  3
% 2.40/1.01  lits                                    51
% 2.40/1.01  lits eq                                 10
% 2.40/1.01  fd_pure                                 0
% 2.40/1.01  fd_pseudo                               0
% 2.40/1.01  fd_cond                                 7
% 2.40/1.01  fd_pseudo_cond                          0
% 2.40/1.01  AC symbols                              0
% 2.40/1.01  
% 2.40/1.01  ------ Schedule dynamic 5 is on 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ 
% 2.40/1.01  Current options:
% 2.40/1.01  ------ 
% 2.40/1.01  
% 2.40/1.01  ------ Input Options
% 2.40/1.01  
% 2.40/1.01  --out_options                           all
% 2.40/1.01  --tptp_safe_out                         true
% 2.40/1.01  --problem_path                          ""
% 2.40/1.01  --include_path                          ""
% 2.40/1.01  --clausifier                            res/vclausify_rel
% 2.40/1.01  --clausifier_options                    --mode clausify
% 2.40/1.01  --stdin                                 false
% 2.40/1.01  --stats_out                             all
% 2.40/1.01  
% 2.40/1.01  ------ General Options
% 2.40/1.01  
% 2.40/1.01  --fof                                   false
% 2.40/1.01  --time_out_real                         305.
% 2.40/1.01  --time_out_virtual                      -1.
% 2.40/1.01  --symbol_type_check                     false
% 2.40/1.01  --clausify_out                          false
% 2.40/1.01  --sig_cnt_out                           false
% 2.40/1.01  --trig_cnt_out                          false
% 2.40/1.01  --trig_cnt_out_tolerance                1.
% 2.40/1.01  --trig_cnt_out_sk_spl                   false
% 2.40/1.01  --abstr_cl_out                          false
% 2.40/1.01  
% 2.40/1.01  ------ Global Options
% 2.40/1.01  
% 2.40/1.01  --schedule                              default
% 2.40/1.01  --add_important_lit                     false
% 2.40/1.01  --prop_solver_per_cl                    1000
% 2.40/1.01  --min_unsat_core                        false
% 2.40/1.01  --soft_assumptions                      false
% 2.40/1.01  --soft_lemma_size                       3
% 2.40/1.01  --prop_impl_unit_size                   0
% 2.40/1.01  --prop_impl_unit                        []
% 2.40/1.01  --share_sel_clauses                     true
% 2.40/1.01  --reset_solvers                         false
% 2.40/1.01  --bc_imp_inh                            [conj_cone]
% 2.40/1.01  --conj_cone_tolerance                   3.
% 2.40/1.01  --extra_neg_conj                        none
% 2.40/1.01  --large_theory_mode                     true
% 2.40/1.01  --prolific_symb_bound                   200
% 2.40/1.01  --lt_threshold                          2000
% 2.40/1.01  --clause_weak_htbl                      true
% 2.40/1.01  --gc_record_bc_elim                     false
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing Options
% 2.40/1.01  
% 2.40/1.01  --preprocessing_flag                    true
% 2.40/1.01  --time_out_prep_mult                    0.1
% 2.40/1.01  --splitting_mode                        input
% 2.40/1.01  --splitting_grd                         true
% 2.40/1.01  --splitting_cvd                         false
% 2.40/1.01  --splitting_cvd_svl                     false
% 2.40/1.01  --splitting_nvd                         32
% 2.40/1.01  --sub_typing                            true
% 2.40/1.01  --prep_gs_sim                           true
% 2.40/1.01  --prep_unflatten                        true
% 2.40/1.01  --prep_res_sim                          true
% 2.40/1.01  --prep_upred                            true
% 2.40/1.01  --prep_sem_filter                       exhaustive
% 2.40/1.01  --prep_sem_filter_out                   false
% 2.40/1.01  --pred_elim                             true
% 2.40/1.01  --res_sim_input                         true
% 2.40/1.01  --eq_ax_congr_red                       true
% 2.40/1.01  --pure_diseq_elim                       true
% 2.40/1.01  --brand_transform                       false
% 2.40/1.01  --non_eq_to_eq                          false
% 2.40/1.01  --prep_def_merge                        true
% 2.40/1.01  --prep_def_merge_prop_impl              false
% 2.40/1.01  --prep_def_merge_mbd                    true
% 2.40/1.01  --prep_def_merge_tr_red                 false
% 2.40/1.01  --prep_def_merge_tr_cl                  false
% 2.40/1.01  --smt_preprocessing                     true
% 2.40/1.01  --smt_ac_axioms                         fast
% 2.40/1.01  --preprocessed_out                      false
% 2.40/1.01  --preprocessed_stats                    false
% 2.40/1.01  
% 2.40/1.01  ------ Abstraction refinement Options
% 2.40/1.01  
% 2.40/1.01  --abstr_ref                             []
% 2.40/1.01  --abstr_ref_prep                        false
% 2.40/1.01  --abstr_ref_until_sat                   false
% 2.40/1.01  --abstr_ref_sig_restrict                funpre
% 2.40/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.01  --abstr_ref_under                       []
% 2.40/1.01  
% 2.40/1.01  ------ SAT Options
% 2.40/1.01  
% 2.40/1.01  --sat_mode                              false
% 2.40/1.01  --sat_fm_restart_options                ""
% 2.40/1.01  --sat_gr_def                            false
% 2.40/1.01  --sat_epr_types                         true
% 2.40/1.01  --sat_non_cyclic_types                  false
% 2.40/1.01  --sat_finite_models                     false
% 2.40/1.01  --sat_fm_lemmas                         false
% 2.40/1.01  --sat_fm_prep                           false
% 2.40/1.01  --sat_fm_uc_incr                        true
% 2.40/1.01  --sat_out_model                         small
% 2.40/1.01  --sat_out_clauses                       false
% 2.40/1.01  
% 2.40/1.01  ------ QBF Options
% 2.40/1.01  
% 2.40/1.01  --qbf_mode                              false
% 2.40/1.01  --qbf_elim_univ                         false
% 2.40/1.01  --qbf_dom_inst                          none
% 2.40/1.01  --qbf_dom_pre_inst                      false
% 2.40/1.01  --qbf_sk_in                             false
% 2.40/1.01  --qbf_pred_elim                         true
% 2.40/1.01  --qbf_split                             512
% 2.40/1.01  
% 2.40/1.01  ------ BMC1 Options
% 2.40/1.01  
% 2.40/1.01  --bmc1_incremental                      false
% 2.40/1.01  --bmc1_axioms                           reachable_all
% 2.40/1.01  --bmc1_min_bound                        0
% 2.40/1.01  --bmc1_max_bound                        -1
% 2.40/1.01  --bmc1_max_bound_default                -1
% 2.40/1.01  --bmc1_symbol_reachability              true
% 2.40/1.01  --bmc1_property_lemmas                  false
% 2.40/1.01  --bmc1_k_induction                      false
% 2.40/1.01  --bmc1_non_equiv_states                 false
% 2.40/1.01  --bmc1_deadlock                         false
% 2.40/1.01  --bmc1_ucm                              false
% 2.40/1.01  --bmc1_add_unsat_core                   none
% 2.40/1.01  --bmc1_unsat_core_children              false
% 2.40/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.01  --bmc1_out_stat                         full
% 2.40/1.01  --bmc1_ground_init                      false
% 2.40/1.01  --bmc1_pre_inst_next_state              false
% 2.40/1.01  --bmc1_pre_inst_state                   false
% 2.40/1.01  --bmc1_pre_inst_reach_state             false
% 2.40/1.01  --bmc1_out_unsat_core                   false
% 2.40/1.01  --bmc1_aig_witness_out                  false
% 2.40/1.01  --bmc1_verbose                          false
% 2.40/1.01  --bmc1_dump_clauses_tptp                false
% 2.40/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.01  --bmc1_dump_file                        -
% 2.40/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.01  --bmc1_ucm_extend_mode                  1
% 2.40/1.01  --bmc1_ucm_init_mode                    2
% 2.40/1.01  --bmc1_ucm_cone_mode                    none
% 2.40/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.01  --bmc1_ucm_relax_model                  4
% 2.40/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.01  --bmc1_ucm_layered_model                none
% 2.40/1.01  --bmc1_ucm_max_lemma_size               10
% 2.40/1.01  
% 2.40/1.01  ------ AIG Options
% 2.40/1.01  
% 2.40/1.01  --aig_mode                              false
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation Options
% 2.40/1.01  
% 2.40/1.01  --instantiation_flag                    true
% 2.40/1.01  --inst_sos_flag                         false
% 2.40/1.01  --inst_sos_phase                        true
% 2.40/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.01  --inst_lit_sel_side                     none
% 2.40/1.01  --inst_solver_per_active                1400
% 2.40/1.01  --inst_solver_calls_frac                1.
% 2.40/1.01  --inst_passive_queue_type               priority_queues
% 2.40/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.01  --inst_passive_queues_freq              [25;2]
% 2.40/1.01  --inst_dismatching                      true
% 2.40/1.01  --inst_eager_unprocessed_to_passive     true
% 2.40/1.01  --inst_prop_sim_given                   true
% 2.40/1.01  --inst_prop_sim_new                     false
% 2.40/1.01  --inst_subs_new                         false
% 2.40/1.01  --inst_eq_res_simp                      false
% 2.40/1.01  --inst_subs_given                       false
% 2.40/1.01  --inst_orphan_elimination               true
% 2.40/1.01  --inst_learning_loop_flag               true
% 2.40/1.01  --inst_learning_start                   3000
% 2.40/1.01  --inst_learning_factor                  2
% 2.40/1.01  --inst_start_prop_sim_after_learn       3
% 2.40/1.01  --inst_sel_renew                        solver
% 2.40/1.01  --inst_lit_activity_flag                true
% 2.40/1.01  --inst_restr_to_given                   false
% 2.40/1.01  --inst_activity_threshold               500
% 2.40/1.01  --inst_out_proof                        true
% 2.40/1.01  
% 2.40/1.01  ------ Resolution Options
% 2.40/1.01  
% 2.40/1.01  --resolution_flag                       false
% 2.40/1.01  --res_lit_sel                           adaptive
% 2.40/1.01  --res_lit_sel_side                      none
% 2.40/1.01  --res_ordering                          kbo
% 2.40/1.01  --res_to_prop_solver                    active
% 2.40/1.01  --res_prop_simpl_new                    false
% 2.40/1.01  --res_prop_simpl_given                  true
% 2.40/1.01  --res_passive_queue_type                priority_queues
% 2.40/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.01  --res_passive_queues_freq               [15;5]
% 2.40/1.01  --res_forward_subs                      full
% 2.40/1.01  --res_backward_subs                     full
% 2.40/1.01  --res_forward_subs_resolution           true
% 2.40/1.01  --res_backward_subs_resolution          true
% 2.40/1.01  --res_orphan_elimination                true
% 2.40/1.01  --res_time_limit                        2.
% 2.40/1.01  --res_out_proof                         true
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Options
% 2.40/1.01  
% 2.40/1.01  --superposition_flag                    true
% 2.40/1.01  --sup_passive_queue_type                priority_queues
% 2.40/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.01  --demod_completeness_check              fast
% 2.40/1.01  --demod_use_ground                      true
% 2.40/1.01  --sup_to_prop_solver                    passive
% 2.40/1.01  --sup_prop_simpl_new                    true
% 2.40/1.01  --sup_prop_simpl_given                  true
% 2.40/1.01  --sup_fun_splitting                     false
% 2.40/1.01  --sup_smt_interval                      50000
% 2.40/1.01  
% 2.40/1.01  ------ Superposition Simplification Setup
% 2.40/1.01  
% 2.40/1.01  --sup_indices_passive                   []
% 2.40/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_full_bw                           [BwDemod]
% 2.40/1.01  --sup_immed_triv                        [TrivRules]
% 2.40/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_immed_bw_main                     []
% 2.40/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.01  
% 2.40/1.01  ------ Combination Options
% 2.40/1.01  
% 2.40/1.01  --comb_res_mult                         3
% 2.40/1.01  --comb_sup_mult                         2
% 2.40/1.01  --comb_inst_mult                        10
% 2.40/1.01  
% 2.40/1.01  ------ Debug Options
% 2.40/1.01  
% 2.40/1.01  --dbg_backtrace                         false
% 2.40/1.01  --dbg_dump_prop_clauses                 false
% 2.40/1.01  --dbg_dump_prop_clauses_file            -
% 2.40/1.01  --dbg_out_stat                          false
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  ------ Proving...
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS status Theorem for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  fof(f10,axiom,(
% 2.40/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f17,plain,(
% 2.40/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/1.01    inference(pure_predicate_removal,[],[f10])).
% 2.40/1.01  
% 2.40/1.01  fof(f24,plain,(
% 2.40/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/1.01    inference(ennf_transformation,[],[f17])).
% 2.40/1.01  
% 2.40/1.01  fof(f25,plain,(
% 2.40/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.01    inference(flattening,[],[f24])).
% 2.40/1.01  
% 2.40/1.01  fof(f38,plain,(
% 2.40/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f39,plain,(
% 2.40/1.01    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f38])).
% 2.40/1.01  
% 2.40/1.01  fof(f57,plain,(
% 2.40/1.01    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f39])).
% 2.40/1.01  
% 2.40/1.01  fof(f15,conjecture,(
% 2.40/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f16,negated_conjecture,(
% 2.40/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.40/1.01    inference(negated_conjecture,[],[f15])).
% 2.40/1.01  
% 2.40/1.01  fof(f34,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/1.01    inference(ennf_transformation,[],[f16])).
% 2.40/1.01  
% 2.40/1.01  fof(f35,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/1.01    inference(flattening,[],[f34])).
% 2.40/1.01  
% 2.40/1.01  fof(f46,plain,(
% 2.40/1.01    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f45,plain,(
% 2.40/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f47,plain,(
% 2.40/1.01    (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f35,f46,f45])).
% 2.40/1.01  
% 2.40/1.01  fof(f69,plain,(
% 2.40/1.01    v2_pre_topc(sK3)),
% 2.40/1.01    inference(cnf_transformation,[],[f47])).
% 2.40/1.01  
% 2.40/1.01  fof(f68,plain,(
% 2.40/1.01    ~v2_struct_0(sK3)),
% 2.40/1.01    inference(cnf_transformation,[],[f47])).
% 2.40/1.01  
% 2.40/1.01  fof(f70,plain,(
% 2.40/1.01    l1_pre_topc(sK3)),
% 2.40/1.01    inference(cnf_transformation,[],[f47])).
% 2.40/1.01  
% 2.40/1.01  fof(f3,axiom,(
% 2.40/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f19,plain,(
% 2.40/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.40/1.01    inference(ennf_transformation,[],[f3])).
% 2.40/1.01  
% 2.40/1.01  fof(f36,plain,(
% 2.40/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f37,plain,(
% 2.40/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f36])).
% 2.40/1.01  
% 2.40/1.01  fof(f50,plain,(
% 2.40/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 2.40/1.01    inference(cnf_transformation,[],[f37])).
% 2.40/1.01  
% 2.40/1.01  fof(f9,axiom,(
% 2.40/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f22,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.40/1.01    inference(ennf_transformation,[],[f9])).
% 2.40/1.01  
% 2.40/1.01  fof(f23,plain,(
% 2.40/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.40/1.01    inference(flattening,[],[f22])).
% 2.40/1.01  
% 2.40/1.01  fof(f56,plain,(
% 2.40/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f23])).
% 2.40/1.01  
% 2.40/1.01  fof(f1,axiom,(
% 2.40/1.01    v1_xboole_0(k1_xboole_0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f48,plain,(
% 2.40/1.01    v1_xboole_0(k1_xboole_0)),
% 2.40/1.01    inference(cnf_transformation,[],[f1])).
% 2.40/1.01  
% 2.40/1.01  fof(f58,plain,(
% 2.40/1.01    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f39])).
% 2.40/1.01  
% 2.40/1.01  fof(f12,axiom,(
% 2.40/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f28,plain,(
% 2.40/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.40/1.01    inference(ennf_transformation,[],[f12])).
% 2.40/1.01  
% 2.40/1.01  fof(f29,plain,(
% 2.40/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.40/1.01    inference(flattening,[],[f28])).
% 2.40/1.01  
% 2.40/1.01  fof(f60,plain,(
% 2.40/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f29])).
% 2.40/1.01  
% 2.40/1.01  fof(f7,axiom,(
% 2.40/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f20,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.40/1.01    inference(ennf_transformation,[],[f7])).
% 2.40/1.01  
% 2.40/1.01  fof(f54,plain,(
% 2.40/1.01    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f20])).
% 2.40/1.01  
% 2.40/1.01  fof(f11,axiom,(
% 2.40/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f26,plain,(
% 2.40/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.40/1.01    inference(ennf_transformation,[],[f11])).
% 2.40/1.01  
% 2.40/1.01  fof(f27,plain,(
% 2.40/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.40/1.01    inference(flattening,[],[f26])).
% 2.40/1.01  
% 2.40/1.01  fof(f59,plain,(
% 2.40/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f27])).
% 2.40/1.01  
% 2.40/1.01  fof(f71,plain,(
% 2.40/1.01    v1_xboole_0(sK4)),
% 2.40/1.01    inference(cnf_transformation,[],[f47])).
% 2.40/1.01  
% 2.40/1.01  fof(f2,axiom,(
% 2.40/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f18,plain,(
% 2.40/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.40/1.01    inference(ennf_transformation,[],[f2])).
% 2.40/1.01  
% 2.40/1.01  fof(f49,plain,(
% 2.40/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f18])).
% 2.40/1.01  
% 2.40/1.01  fof(f73,plain,(
% 2.40/1.01    v3_tex_2(sK4,sK3)),
% 2.40/1.01    inference(cnf_transformation,[],[f47])).
% 2.40/1.01  
% 2.40/1.01  fof(f4,axiom,(
% 2.40/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f51,plain,(
% 2.40/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f4])).
% 2.40/1.01  
% 2.40/1.01  fof(f13,axiom,(
% 2.40/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f30,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(ennf_transformation,[],[f13])).
% 2.40/1.01  
% 2.40/1.01  fof(f31,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(flattening,[],[f30])).
% 2.40/1.01  
% 2.40/1.01  fof(f40,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(nnf_transformation,[],[f31])).
% 2.40/1.01  
% 2.40/1.01  fof(f41,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(flattening,[],[f40])).
% 2.40/1.01  
% 2.40/1.01  fof(f42,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(rectify,[],[f41])).
% 2.40/1.01  
% 2.40/1.01  fof(f43,plain,(
% 2.40/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/1.01    introduced(choice_axiom,[])).
% 2.40/1.01  
% 2.40/1.01  fof(f44,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.40/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 2.40/1.01  
% 2.40/1.01  fof(f62,plain,(
% 2.40/1.01    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f44])).
% 2.40/1.01  
% 2.40/1.01  fof(f6,axiom,(
% 2.40/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f53,plain,(
% 2.40/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f6])).
% 2.40/1.01  
% 2.40/1.01  fof(f14,axiom,(
% 2.40/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f32,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/1.01    inference(ennf_transformation,[],[f14])).
% 2.40/1.01  
% 2.40/1.01  fof(f33,plain,(
% 2.40/1.01    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.01    inference(flattening,[],[f32])).
% 2.40/1.01  
% 2.40/1.01  fof(f67,plain,(
% 2.40/1.01    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.01    inference(cnf_transformation,[],[f33])).
% 2.40/1.01  
% 2.40/1.01  fof(f5,axiom,(
% 2.40/1.01    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 2.40/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.40/1.01  
% 2.40/1.01  fof(f52,plain,(
% 2.40/1.01    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 2.40/1.01    inference(cnf_transformation,[],[f5])).
% 2.40/1.01  
% 2.40/1.01  cnf(c_10,plain,
% 2.40/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.01      | v2_struct_0(X0)
% 2.40/1.01      | ~ v2_pre_topc(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_24,negated_conjecture,
% 2.40/1.01      ( v2_pre_topc(sK3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_340,plain,
% 2.40/1.01      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.40/1.01      | v2_struct_0(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0)
% 2.40/1.01      | sK3 != X0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_24]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_341,plain,
% 2.40/1.01      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | v2_struct_0(sK3)
% 2.40/1.01      | ~ l1_pre_topc(sK3) ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_340]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_25,negated_conjecture,
% 2.40/1.01      ( ~ v2_struct_0(sK3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_23,negated_conjecture,
% 2.40/1.01      ( l1_pre_topc(sK3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_343,plain,
% 2.40/1.01      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_341,c_25,c_23]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1240,plain,
% 2.40/1.01      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2,plain,
% 2.40/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 2.40/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_8,plain,
% 2.40/1.01      ( m1_subset_1(X0,X1)
% 2.40/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/1.01      | ~ r2_hidden(X0,X2) ),
% 2.40/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_300,plain,
% 2.40/1.01      ( m1_subset_1(X0,X1)
% 2.40/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.40/1.01      | X2 != X3
% 2.40/1.01      | sK0(X3) != X0
% 2.40/1.01      | k1_xboole_0 = X3 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_8]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_301,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/1.01      | m1_subset_1(sK0(X0),X1)
% 2.40/1.01      | k1_xboole_0 = X0 ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_300]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1242,plain,
% 2.40/1.01      ( k1_xboole_0 = X0
% 2.40/1.01      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.40/1.01      | m1_subset_1(sK0(X0),X1) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2107,plain,
% 2.40/1.01      ( sK1(sK3) = k1_xboole_0
% 2.40/1.01      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1240,c_1242]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_0,plain,
% 2.40/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_9,plain,
% 2.40/1.01      ( v2_struct_0(X0)
% 2.40/1.01      | ~ v2_pre_topc(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0)
% 2.40/1.01      | ~ v1_xboole_0(sK1(X0)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_351,plain,
% 2.40/1.01      ( v2_struct_0(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0)
% 2.40/1.01      | ~ v1_xboole_0(sK1(X0))
% 2.40/1.01      | sK3 != X0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_9,c_24]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_352,plain,
% 2.40/1.01      ( v2_struct_0(sK3) | ~ l1_pre_topc(sK3) | ~ v1_xboole_0(sK1(sK3)) ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_351]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_882,plain,
% 2.40/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.40/1.01      theory(equality) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1401,plain,
% 2.40/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1(sK3)) | sK1(sK3) != X0 ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_882]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1403,plain,
% 2.40/1.01      ( v1_xboole_0(sK1(sK3))
% 2.40/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.40/1.01      | sK1(sK3) != k1_xboole_0 ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2440,plain,
% 2.40/1.01      ( m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_2107,c_25,c_23,c_0,c_352,c_1403]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_12,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,X1)
% 2.40/1.01      | v1_xboole_0(X1)
% 2.40/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1246,plain,
% 2.40/1.01      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.40/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.40/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2445,plain,
% 2.40/1.01      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3)))
% 2.40/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2440,c_1246]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_26,plain,
% 2.40/1.01      ( v2_struct_0(sK3) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_28,plain,
% 2.40/1.01      ( l1_pre_topc(sK3) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_342,plain,
% 2.40/1.01      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.40/1.01      | v2_struct_0(sK3) = iProver_top
% 2.40/1.01      | l1_pre_topc(sK3) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_353,plain,
% 2.40/1.01      ( v2_struct_0(sK3) = iProver_top
% 2.40/1.01      | l1_pre_topc(sK3) != iProver_top
% 2.40/1.01      | v1_xboole_0(sK1(sK3)) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_6,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/1.01      | ~ v1_xboole_0(X1)
% 2.40/1.01      | v1_xboole_0(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1391,plain,
% 2.40/1.01      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
% 2.40/1.01      | ~ v1_xboole_0(X0)
% 2.40/1.01      | v1_xboole_0(sK1(sK3)) ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1480,plain,
% 2.40/1.01      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | ~ v1_xboole_0(u1_struct_0(sK3))
% 2.40/1.01      | v1_xboole_0(sK1(sK3)) ),
% 2.40/1.01      inference(instantiation,[status(thm)],[c_1391]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1481,plain,
% 2.40/1.01      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.40/1.01      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.40/1.01      | v1_xboole_0(sK1(sK3)) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1480]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2542,plain,
% 2.40/1.01      ( k6_domain_1(u1_struct_0(sK3),sK0(sK1(sK3))) = k1_tarski(sK0(sK1(sK3))) ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_2445,c_26,c_28,c_342,c_353,c_1481]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_11,plain,
% 2.40/1.01      ( ~ m1_subset_1(X0,X1)
% 2.40/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.40/1.01      | v1_xboole_0(X1) ),
% 2.40/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1247,plain,
% 2.40/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.40/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.40/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2545,plain,
% 2.40/1.01      ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.40/1.01      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top
% 2.40/1.01      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2542,c_1247]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2760,plain,
% 2.40/1.01      ( m1_subset_1(k1_tarski(sK0(sK1(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_2545,c_25,c_26,c_23,c_28,c_0,c_342,c_352,c_353,c_1403,
% 2.40/1.01                 c_1481,c_2107]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_22,negated_conjecture,
% 2.40/1.01      ( v1_xboole_0(sK4) ),
% 2.40/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1244,plain,
% 2.40/1.01      ( v1_xboole_0(sK4) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1,plain,
% 2.40/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.40/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1251,plain,
% 2.40/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1811,plain,
% 2.40/1.01      ( sK4 = k1_xboole_0 ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_1244,c_1251]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_20,negated_conjecture,
% 2.40/1.01      ( v3_tex_2(sK4,sK3) ),
% 2.40/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_3,plain,
% 2.40/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_17,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,X1)
% 2.40/1.01      | ~ v3_tex_2(X2,X1)
% 2.40/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.01      | ~ r1_tarski(X2,X0)
% 2.40/1.01      | ~ l1_pre_topc(X1)
% 2.40/1.01      | X0 = X2 ),
% 2.40/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_457,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,X1)
% 2.40/1.01      | ~ v3_tex_2(X2,X1)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.01      | ~ r1_tarski(X2,X0)
% 2.40/1.01      | X2 = X0
% 2.40/1.01      | sK3 != X1 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_458,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ v3_tex_2(X1,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | ~ r1_tarski(X1,X0)
% 2.40/1.01      | X1 = X0 ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_457]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_584,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ v3_tex_2(X1,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | X0 != X2
% 2.40/1.01      | X0 = X1
% 2.40/1.01      | k1_xboole_0 != X1 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_458]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_585,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | X0 = k1_xboole_0 ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_584]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_5,plain,
% 2.40/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_599,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | X0 = k1_xboole_0 ),
% 2.40/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_585,c_5]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_626,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | sK3 != sK3
% 2.40/1.01      | sK4 != k1_xboole_0
% 2.40/1.01      | k1_xboole_0 = X0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_599]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_766,plain,
% 2.40/1.01      ( ~ v2_tex_2(X0,sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.40/1.01      | sK4 != k1_xboole_0
% 2.40/1.01      | k1_xboole_0 = X0 ),
% 2.40/1.01      inference(equality_resolution_simp,[status(thm)],[c_626]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1231,plain,
% 2.40/1.01      ( sK4 != k1_xboole_0
% 2.40/1.01      | k1_xboole_0 = X0
% 2.40/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.40/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_766]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1815,plain,
% 2.40/1.01      ( k1_xboole_0 = X0
% 2.40/1.01      | k1_xboole_0 != k1_xboole_0
% 2.40/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.40/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.40/1.01      inference(demodulation,[status(thm)],[c_1811,c_1231]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1822,plain,
% 2.40/1.01      ( k1_xboole_0 = X0
% 2.40/1.01      | v2_tex_2(X0,sK3) != iProver_top
% 2.40/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.40/1.01      inference(equality_resolution_simp,[status(thm)],[c_1815]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2768,plain,
% 2.40/1.01      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0
% 2.40/1.01      | v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2760,c_1822]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_19,plain,
% 2.40/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.40/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.40/1.01      | v2_struct_0(X0)
% 2.40/1.01      | ~ v2_pre_topc(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0) ),
% 2.40/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_322,plain,
% 2.40/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.40/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.40/1.01      | v2_struct_0(X0)
% 2.40/1.01      | ~ l1_pre_topc(X0)
% 2.40/1.01      | sK3 != X0 ),
% 2.40/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_323,plain,
% 2.40/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.40/1.01      | v2_struct_0(sK3)
% 2.40/1.01      | ~ l1_pre_topc(sK3) ),
% 2.40/1.01      inference(unflattening,[status(thm)],[c_322]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_327,plain,
% 2.40/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.40/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_323,c_25,c_23]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1241,plain,
% 2.40/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 2.40/1.01      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2546,plain,
% 2.40/1.01      ( v2_tex_2(k1_tarski(sK0(sK1(sK3))),sK3) = iProver_top
% 2.40/1.01      | m1_subset_1(sK0(sK1(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2542,c_1241]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2981,plain,
% 2.40/1.01      ( k1_tarski(sK0(sK1(sK3))) = k1_xboole_0 ),
% 2.40/1.01      inference(global_propositional_subsumption,
% 2.40/1.01                [status(thm)],
% 2.40/1.01                [c_2768,c_25,c_23,c_0,c_352,c_1403,c_2107,c_2546]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_4,plain,
% 2.40/1.01      ( ~ v1_xboole_0(k1_tarski(X0)) ),
% 2.40/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_1250,plain,
% 2.40/1.01      ( v1_xboole_0(k1_tarski(X0)) != iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_2989,plain,
% 2.40/1.01      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.40/1.01      inference(superposition,[status(thm)],[c_2981,c_1250]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(c_87,plain,
% 2.40/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.40/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.40/1.01  
% 2.40/1.01  cnf(contradiction,plain,
% 2.40/1.01      ( $false ),
% 2.40/1.01      inference(minisat,[status(thm)],[c_2989,c_87]) ).
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.01  
% 2.40/1.01  ------                               Statistics
% 2.40/1.01  
% 2.40/1.01  ------ General
% 2.40/1.01  
% 2.40/1.01  abstr_ref_over_cycles:                  0
% 2.40/1.01  abstr_ref_under_cycles:                 0
% 2.40/1.01  gc_basic_clause_elim:                   0
% 2.40/1.01  forced_gc_time:                         0
% 2.40/1.01  parsing_time:                           0.009
% 2.40/1.01  unif_index_cands_time:                  0.
% 2.40/1.01  unif_index_add_time:                    0.
% 2.40/1.01  orderings_time:                         0.
% 2.40/1.01  out_proof_time:                         0.009
% 2.40/1.01  total_time:                             0.142
% 2.40/1.01  num_of_symbols:                         51
% 2.40/1.01  num_of_terms:                           1842
% 2.40/1.01  
% 2.40/1.01  ------ Preprocessing
% 2.40/1.01  
% 2.40/1.01  num_of_splits:                          3
% 2.40/1.01  num_of_split_atoms:                     1
% 2.40/1.01  num_of_reused_defs:                     2
% 2.40/1.01  num_eq_ax_congr_red:                    14
% 2.40/1.01  num_of_sem_filtered_clauses:            1
% 2.40/1.01  num_of_subtypes:                        0
% 2.40/1.01  monotx_restored_types:                  0
% 2.40/1.01  sat_num_of_epr_types:                   0
% 2.40/1.01  sat_num_of_non_cyclic_types:            0
% 2.40/1.01  sat_guarded_non_collapsed_types:        0
% 2.40/1.01  num_pure_diseq_elim:                    0
% 2.40/1.01  simp_replaced_by:                       0
% 2.40/1.01  res_preprocessed:                       106
% 2.40/1.01  prep_upred:                             0
% 2.40/1.01  prep_unflattend:                        25
% 2.40/1.01  smt_new_axioms:                         0
% 2.40/1.01  pred_elim_cands:                        3
% 2.40/1.01  pred_elim:                              6
% 2.40/1.01  pred_elim_cl:                           7
% 2.40/1.01  pred_elim_cycles:                       9
% 2.40/1.01  merged_defs:                            0
% 2.40/1.01  merged_defs_ncl:                        0
% 2.40/1.01  bin_hyper_res:                          0
% 2.40/1.01  prep_cycles:                            4
% 2.40/1.01  pred_elim_time:                         0.009
% 2.40/1.01  splitting_time:                         0.
% 2.40/1.01  sem_filter_time:                        0.
% 2.40/1.01  monotx_time:                            0.
% 2.40/1.01  subtype_inf_time:                       0.
% 2.40/1.01  
% 2.40/1.01  ------ Problem properties
% 2.40/1.01  
% 2.40/1.01  clauses:                                22
% 2.40/1.01  conjectures:                            2
% 2.40/1.01  epr:                                    4
% 2.40/1.01  horn:                                   16
% 2.40/1.01  ground:                                 9
% 2.40/1.01  unary:                                  8
% 2.40/1.01  binary:                                 3
% 2.40/1.01  lits:                                   51
% 2.40/1.01  lits_eq:                                10
% 2.40/1.01  fd_pure:                                0
% 2.40/1.01  fd_pseudo:                              0
% 2.40/1.01  fd_cond:                                7
% 2.40/1.01  fd_pseudo_cond:                         0
% 2.40/1.01  ac_symbols:                             0
% 2.40/1.01  
% 2.40/1.01  ------ Propositional Solver
% 2.40/1.01  
% 2.40/1.01  prop_solver_calls:                      27
% 2.40/1.01  prop_fast_solver_calls:                 697
% 2.40/1.01  smt_solver_calls:                       0
% 2.40/1.01  smt_fast_solver_calls:                  0
% 2.40/1.01  prop_num_of_clauses:                    935
% 2.40/1.01  prop_preprocess_simplified:             4060
% 2.40/1.01  prop_fo_subsumed:                       21
% 2.40/1.01  prop_solver_time:                       0.
% 2.40/1.01  smt_solver_time:                        0.
% 2.40/1.01  smt_fast_solver_time:                   0.
% 2.40/1.01  prop_fast_solver_time:                  0.
% 2.40/1.01  prop_unsat_core_time:                   0.
% 2.40/1.01  
% 2.40/1.01  ------ QBF
% 2.40/1.01  
% 2.40/1.01  qbf_q_res:                              0
% 2.40/1.01  qbf_num_tautologies:                    0
% 2.40/1.01  qbf_prep_cycles:                        0
% 2.40/1.01  
% 2.40/1.01  ------ BMC1
% 2.40/1.01  
% 2.40/1.01  bmc1_current_bound:                     -1
% 2.40/1.01  bmc1_last_solved_bound:                 -1
% 2.40/1.01  bmc1_unsat_core_size:                   -1
% 2.40/1.01  bmc1_unsat_core_parents_size:           -1
% 2.40/1.01  bmc1_merge_next_fun:                    0
% 2.40/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.01  
% 2.40/1.01  ------ Instantiation
% 2.40/1.01  
% 2.40/1.01  inst_num_of_clauses:                    268
% 2.40/1.01  inst_num_in_passive:                    128
% 2.40/1.01  inst_num_in_active:                     137
% 2.40/1.01  inst_num_in_unprocessed:                3
% 2.40/1.01  inst_num_of_loops:                      160
% 2.40/1.01  inst_num_of_learning_restarts:          0
% 2.40/1.01  inst_num_moves_active_passive:          21
% 2.40/1.01  inst_lit_activity:                      0
% 2.40/1.01  inst_lit_activity_moves:                0
% 2.40/1.01  inst_num_tautologies:                   0
% 2.40/1.01  inst_num_prop_implied:                  0
% 2.40/1.01  inst_num_existing_simplified:           0
% 2.40/1.01  inst_num_eq_res_simplified:             0
% 2.40/1.01  inst_num_child_elim:                    0
% 2.40/1.01  inst_num_of_dismatching_blockings:      59
% 2.40/1.01  inst_num_of_non_proper_insts:           187
% 2.40/1.01  inst_num_of_duplicates:                 0
% 2.40/1.01  inst_inst_num_from_inst_to_res:         0
% 2.40/1.01  inst_dismatching_checking_time:         0.
% 2.40/1.01  
% 2.40/1.01  ------ Resolution
% 2.40/1.01  
% 2.40/1.01  res_num_of_clauses:                     0
% 2.40/1.01  res_num_in_passive:                     0
% 2.40/1.01  res_num_in_active:                      0
% 2.40/1.01  res_num_of_loops:                       110
% 2.40/1.01  res_forward_subset_subsumed:            26
% 2.40/1.01  res_backward_subset_subsumed:           0
% 2.40/1.01  res_forward_subsumed:                   0
% 2.40/1.01  res_backward_subsumed:                  0
% 2.40/1.01  res_forward_subsumption_resolution:     5
% 2.40/1.01  res_backward_subsumption_resolution:    0
% 2.40/1.01  res_clause_to_clause_subsumption:       71
% 2.40/1.01  res_orphan_elimination:                 0
% 2.40/1.01  res_tautology_del:                      13
% 2.40/1.01  res_num_eq_res_simplified:              1
% 2.40/1.01  res_num_sel_changes:                    0
% 2.40/1.01  res_moves_from_active_to_pass:          0
% 2.40/1.01  
% 2.40/1.01  ------ Superposition
% 2.40/1.01  
% 2.40/1.01  sup_time_total:                         0.
% 2.40/1.01  sup_time_generating:                    0.
% 2.40/1.01  sup_time_sim_full:                      0.
% 2.40/1.01  sup_time_sim_immed:                     0.
% 2.40/1.01  
% 2.40/1.01  sup_num_of_clauses:                     33
% 2.40/1.01  sup_num_in_active:                      24
% 2.40/1.01  sup_num_in_passive:                     9
% 2.40/1.01  sup_num_of_loops:                       30
% 2.40/1.01  sup_fw_superposition:                   14
% 2.40/1.01  sup_bw_superposition:                   15
% 2.40/1.01  sup_immediate_simplified:               6
% 2.40/1.01  sup_given_eliminated:                   0
% 2.40/1.01  comparisons_done:                       0
% 2.40/1.01  comparisons_avoided:                    3
% 2.40/1.01  
% 2.40/1.01  ------ Simplifications
% 2.40/1.01  
% 2.40/1.01  
% 2.40/1.01  sim_fw_subset_subsumed:                 5
% 2.40/1.01  sim_bw_subset_subsumed:                 2
% 2.40/1.01  sim_fw_subsumed:                        1
% 2.40/1.01  sim_bw_subsumed:                        0
% 2.40/1.01  sim_fw_subsumption_res:                 0
% 2.40/1.01  sim_bw_subsumption_res:                 0
% 2.40/1.01  sim_tautology_del:                      1
% 2.40/1.01  sim_eq_tautology_del:                   3
% 2.40/1.01  sim_eq_res_simp:                        1
% 2.40/1.01  sim_fw_demodulated:                     0
% 2.40/1.01  sim_bw_demodulated:                     7
% 2.40/1.01  sim_light_normalised:                   0
% 2.40/1.01  sim_joinable_taut:                      0
% 2.40/1.01  sim_joinable_simp:                      0
% 2.40/1.01  sim_ac_normalised:                      0
% 2.40/1.01  sim_smt_subsumption:                    0
% 2.40/1.01  
%------------------------------------------------------------------------------
