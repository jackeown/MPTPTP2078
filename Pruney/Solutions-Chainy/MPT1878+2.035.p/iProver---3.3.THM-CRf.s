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
% DateTime   : Thu Dec  3 12:27:04 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 270 expanded)
%              Number of clauses        :   70 (  90 expanded)
%              Number of leaves         :   20 (  64 expanded)
%              Depth                    :   21
%              Number of atoms          :  468 (1137 expanded)
%              Number of equality atoms :  110 ( 127 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f46,f45])).

fof(f72,plain,(
    v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

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
    inference(nnf_transformation,[],[f29])).

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

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f69,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

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

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK1(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f5])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_7,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_347,plain,
    ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_7])).

cnf(c_348,plain,
    ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0))
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_1244,plain,
    ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0)) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_23,negated_conjecture,
    ( v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1249,plain,
    ( v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1253,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2063,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1249,c_1253])).

cnf(c_21,negated_conjecture,
    ( v3_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_491,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_492,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_618,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(X1,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_492])).

cnf(c_619,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_633,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ v3_tex_2(k1_xboole_0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_619,c_6])).

cnf(c_660,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_633])).

cnf(c_798,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | sK4 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_660])).

cnf(c_1234,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_798])).

cnf(c_2101,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2063,c_1234])).

cnf(c_2110,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2101])).

cnf(c_2973,plain,
    ( k1_tarski(sK0(u1_struct_0(sK3))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK3))),sK3) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1244,c_2110])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_27,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_29,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_12,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_306,plain,
    ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_25])).

cnf(c_307,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_308,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_317,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK1(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_318,plain,
    ( v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v1_xboole_0(sK1(sK3)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_319,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_pre_topc(sK3) != iProver_top
    | v1_xboole_0(sK1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X0 != X2
    | sK0(X2) != X3 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_10])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_1387,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_377])).

cnf(c_1470,plain,
    ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1471,plain,
    ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1470])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_335,plain,
    ( m1_subset_1(X0,X1)
    | v1_xboole_0(X2)
    | X1 != X2
    | sK0(X2) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_8])).

cnf(c_336,plain,
    ( m1_subset_1(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_1572,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_336])).

cnf(c_1573,plain,
    ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1572])).

cnf(c_907,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1586,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(u1_struct_0(sK3))
    | u1_struct_0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_907])).

cnf(c_1587,plain,
    ( u1_struct_0(sK3) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1586])).

cnf(c_1589,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1587])).

cnf(c_2104,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2063,c_1249])).

cnf(c_1245,plain,
    ( m1_subset_1(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1251,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2651,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1251])).

cnf(c_2686,plain,
    ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
    | k1_xboole_0 = X0 ),
    inference(superposition,[status(thm)],[c_2651,c_1253])).

cnf(c_20,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_288,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_289,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
    | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_26,c_24])).

cnf(c_1248,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_293])).

cnf(c_2733,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK3))),sK3) = iProver_top
    | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2686,c_1248])).

cnf(c_2996,plain,
    ( k1_tarski(sK0(u1_struct_0(sK3))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_27,c_29,c_308,c_319,c_1471,c_1573,c_1589,c_2104,c_2733])).

cnf(c_3,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1744,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3,c_5])).

cnf(c_2999,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2996,c_1744])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:04:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.48/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.48/0.99  
% 2.48/0.99  ------  iProver source info
% 2.48/0.99  
% 2.48/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.48/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.48/0.99  git: non_committed_changes: false
% 2.48/0.99  git: last_make_outside_of_git: false
% 2.48/0.99  
% 2.48/0.99  ------ 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options
% 2.48/0.99  
% 2.48/0.99  --out_options                           all
% 2.48/0.99  --tptp_safe_out                         true
% 2.48/0.99  --problem_path                          ""
% 2.48/0.99  --include_path                          ""
% 2.48/0.99  --clausifier                            res/vclausify_rel
% 2.48/0.99  --clausifier_options                    --mode clausify
% 2.48/0.99  --stdin                                 false
% 2.48/0.99  --stats_out                             all
% 2.48/0.99  
% 2.48/0.99  ------ General Options
% 2.48/0.99  
% 2.48/0.99  --fof                                   false
% 2.48/0.99  --time_out_real                         305.
% 2.48/0.99  --time_out_virtual                      -1.
% 2.48/0.99  --symbol_type_check                     false
% 2.48/0.99  --clausify_out                          false
% 2.48/0.99  --sig_cnt_out                           false
% 2.48/0.99  --trig_cnt_out                          false
% 2.48/0.99  --trig_cnt_out_tolerance                1.
% 2.48/0.99  --trig_cnt_out_sk_spl                   false
% 2.48/0.99  --abstr_cl_out                          false
% 2.48/0.99  
% 2.48/0.99  ------ Global Options
% 2.48/0.99  
% 2.48/0.99  --schedule                              default
% 2.48/0.99  --add_important_lit                     false
% 2.48/0.99  --prop_solver_per_cl                    1000
% 2.48/0.99  --min_unsat_core                        false
% 2.48/0.99  --soft_assumptions                      false
% 2.48/0.99  --soft_lemma_size                       3
% 2.48/0.99  --prop_impl_unit_size                   0
% 2.48/0.99  --prop_impl_unit                        []
% 2.48/0.99  --share_sel_clauses                     true
% 2.48/0.99  --reset_solvers                         false
% 2.48/0.99  --bc_imp_inh                            [conj_cone]
% 2.48/0.99  --conj_cone_tolerance                   3.
% 2.48/0.99  --extra_neg_conj                        none
% 2.48/0.99  --large_theory_mode                     true
% 2.48/0.99  --prolific_symb_bound                   200
% 2.48/0.99  --lt_threshold                          2000
% 2.48/0.99  --clause_weak_htbl                      true
% 2.48/0.99  --gc_record_bc_elim                     false
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing Options
% 2.48/0.99  
% 2.48/0.99  --preprocessing_flag                    true
% 2.48/0.99  --time_out_prep_mult                    0.1
% 2.48/0.99  --splitting_mode                        input
% 2.48/0.99  --splitting_grd                         true
% 2.48/0.99  --splitting_cvd                         false
% 2.48/0.99  --splitting_cvd_svl                     false
% 2.48/0.99  --splitting_nvd                         32
% 2.48/0.99  --sub_typing                            true
% 2.48/0.99  --prep_gs_sim                           true
% 2.48/0.99  --prep_unflatten                        true
% 2.48/0.99  --prep_res_sim                          true
% 2.48/0.99  --prep_upred                            true
% 2.48/0.99  --prep_sem_filter                       exhaustive
% 2.48/0.99  --prep_sem_filter_out                   false
% 2.48/0.99  --pred_elim                             true
% 2.48/0.99  --res_sim_input                         true
% 2.48/0.99  --eq_ax_congr_red                       true
% 2.48/0.99  --pure_diseq_elim                       true
% 2.48/0.99  --brand_transform                       false
% 2.48/0.99  --non_eq_to_eq                          false
% 2.48/0.99  --prep_def_merge                        true
% 2.48/0.99  --prep_def_merge_prop_impl              false
% 2.48/0.99  --prep_def_merge_mbd                    true
% 2.48/0.99  --prep_def_merge_tr_red                 false
% 2.48/0.99  --prep_def_merge_tr_cl                  false
% 2.48/0.99  --smt_preprocessing                     true
% 2.48/0.99  --smt_ac_axioms                         fast
% 2.48/0.99  --preprocessed_out                      false
% 2.48/0.99  --preprocessed_stats                    false
% 2.48/0.99  
% 2.48/0.99  ------ Abstraction refinement Options
% 2.48/0.99  
% 2.48/0.99  --abstr_ref                             []
% 2.48/0.99  --abstr_ref_prep                        false
% 2.48/0.99  --abstr_ref_until_sat                   false
% 2.48/0.99  --abstr_ref_sig_restrict                funpre
% 2.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.99  --abstr_ref_under                       []
% 2.48/0.99  
% 2.48/0.99  ------ SAT Options
% 2.48/0.99  
% 2.48/0.99  --sat_mode                              false
% 2.48/0.99  --sat_fm_restart_options                ""
% 2.48/0.99  --sat_gr_def                            false
% 2.48/0.99  --sat_epr_types                         true
% 2.48/0.99  --sat_non_cyclic_types                  false
% 2.48/0.99  --sat_finite_models                     false
% 2.48/0.99  --sat_fm_lemmas                         false
% 2.48/0.99  --sat_fm_prep                           false
% 2.48/0.99  --sat_fm_uc_incr                        true
% 2.48/0.99  --sat_out_model                         small
% 2.48/0.99  --sat_out_clauses                       false
% 2.48/0.99  
% 2.48/0.99  ------ QBF Options
% 2.48/0.99  
% 2.48/0.99  --qbf_mode                              false
% 2.48/0.99  --qbf_elim_univ                         false
% 2.48/0.99  --qbf_dom_inst                          none
% 2.48/0.99  --qbf_dom_pre_inst                      false
% 2.48/0.99  --qbf_sk_in                             false
% 2.48/0.99  --qbf_pred_elim                         true
% 2.48/0.99  --qbf_split                             512
% 2.48/0.99  
% 2.48/0.99  ------ BMC1 Options
% 2.48/0.99  
% 2.48/0.99  --bmc1_incremental                      false
% 2.48/0.99  --bmc1_axioms                           reachable_all
% 2.48/0.99  --bmc1_min_bound                        0
% 2.48/0.99  --bmc1_max_bound                        -1
% 2.48/0.99  --bmc1_max_bound_default                -1
% 2.48/0.99  --bmc1_symbol_reachability              true
% 2.48/0.99  --bmc1_property_lemmas                  false
% 2.48/0.99  --bmc1_k_induction                      false
% 2.48/0.99  --bmc1_non_equiv_states                 false
% 2.48/0.99  --bmc1_deadlock                         false
% 2.48/0.99  --bmc1_ucm                              false
% 2.48/0.99  --bmc1_add_unsat_core                   none
% 2.48/0.99  --bmc1_unsat_core_children              false
% 2.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.99  --bmc1_out_stat                         full
% 2.48/0.99  --bmc1_ground_init                      false
% 2.48/0.99  --bmc1_pre_inst_next_state              false
% 2.48/0.99  --bmc1_pre_inst_state                   false
% 2.48/0.99  --bmc1_pre_inst_reach_state             false
% 2.48/0.99  --bmc1_out_unsat_core                   false
% 2.48/0.99  --bmc1_aig_witness_out                  false
% 2.48/0.99  --bmc1_verbose                          false
% 2.48/0.99  --bmc1_dump_clauses_tptp                false
% 2.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.99  --bmc1_dump_file                        -
% 2.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.99  --bmc1_ucm_extend_mode                  1
% 2.48/0.99  --bmc1_ucm_init_mode                    2
% 2.48/0.99  --bmc1_ucm_cone_mode                    none
% 2.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.99  --bmc1_ucm_relax_model                  4
% 2.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.99  --bmc1_ucm_layered_model                none
% 2.48/0.99  --bmc1_ucm_max_lemma_size               10
% 2.48/0.99  
% 2.48/0.99  ------ AIG Options
% 2.48/0.99  
% 2.48/0.99  --aig_mode                              false
% 2.48/0.99  
% 2.48/0.99  ------ Instantiation Options
% 2.48/0.99  
% 2.48/0.99  --instantiation_flag                    true
% 2.48/0.99  --inst_sos_flag                         false
% 2.48/0.99  --inst_sos_phase                        true
% 2.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel_side                     num_symb
% 2.48/0.99  --inst_solver_per_active                1400
% 2.48/0.99  --inst_solver_calls_frac                1.
% 2.48/0.99  --inst_passive_queue_type               priority_queues
% 2.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.99  --inst_passive_queues_freq              [25;2]
% 2.48/0.99  --inst_dismatching                      true
% 2.48/0.99  --inst_eager_unprocessed_to_passive     true
% 2.48/0.99  --inst_prop_sim_given                   true
% 2.48/0.99  --inst_prop_sim_new                     false
% 2.48/0.99  --inst_subs_new                         false
% 2.48/0.99  --inst_eq_res_simp                      false
% 2.48/0.99  --inst_subs_given                       false
% 2.48/0.99  --inst_orphan_elimination               true
% 2.48/0.99  --inst_learning_loop_flag               true
% 2.48/0.99  --inst_learning_start                   3000
% 2.48/0.99  --inst_learning_factor                  2
% 2.48/0.99  --inst_start_prop_sim_after_learn       3
% 2.48/0.99  --inst_sel_renew                        solver
% 2.48/0.99  --inst_lit_activity_flag                true
% 2.48/0.99  --inst_restr_to_given                   false
% 2.48/0.99  --inst_activity_threshold               500
% 2.48/0.99  --inst_out_proof                        true
% 2.48/0.99  
% 2.48/0.99  ------ Resolution Options
% 2.48/0.99  
% 2.48/0.99  --resolution_flag                       true
% 2.48/0.99  --res_lit_sel                           adaptive
% 2.48/0.99  --res_lit_sel_side                      none
% 2.48/0.99  --res_ordering                          kbo
% 2.48/0.99  --res_to_prop_solver                    active
% 2.48/0.99  --res_prop_simpl_new                    false
% 2.48/0.99  --res_prop_simpl_given                  true
% 2.48/0.99  --res_passive_queue_type                priority_queues
% 2.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.99  --res_passive_queues_freq               [15;5]
% 2.48/0.99  --res_forward_subs                      full
% 2.48/0.99  --res_backward_subs                     full
% 2.48/0.99  --res_forward_subs_resolution           true
% 2.48/0.99  --res_backward_subs_resolution          true
% 2.48/0.99  --res_orphan_elimination                true
% 2.48/0.99  --res_time_limit                        2.
% 2.48/0.99  --res_out_proof                         true
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Options
% 2.48/0.99  
% 2.48/0.99  --superposition_flag                    true
% 2.48/0.99  --sup_passive_queue_type                priority_queues
% 2.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.99  --demod_completeness_check              fast
% 2.48/0.99  --demod_use_ground                      true
% 2.48/0.99  --sup_to_prop_solver                    passive
% 2.48/0.99  --sup_prop_simpl_new                    true
% 2.48/0.99  --sup_prop_simpl_given                  true
% 2.48/0.99  --sup_fun_splitting                     false
% 2.48/0.99  --sup_smt_interval                      50000
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Simplification Setup
% 2.48/0.99  
% 2.48/0.99  --sup_indices_passive                   []
% 2.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_full_bw                           [BwDemod]
% 2.48/0.99  --sup_immed_triv                        [TrivRules]
% 2.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_immed_bw_main                     []
% 2.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  
% 2.48/0.99  ------ Combination Options
% 2.48/0.99  
% 2.48/0.99  --comb_res_mult                         3
% 2.48/0.99  --comb_sup_mult                         2
% 2.48/0.99  --comb_inst_mult                        10
% 2.48/0.99  
% 2.48/0.99  ------ Debug Options
% 2.48/0.99  
% 2.48/0.99  --dbg_backtrace                         false
% 2.48/0.99  --dbg_dump_prop_clauses                 false
% 2.48/0.99  --dbg_dump_prop_clauses_file            -
% 2.48/0.99  --dbg_out_stat                          false
% 2.48/0.99  ------ Parsing...
% 2.48/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.48/0.99  ------ Proving...
% 2.48/0.99  ------ Problem Properties 
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  clauses                                 22
% 2.48/0.99  conjectures                             2
% 2.48/0.99  EPR                                     3
% 2.48/0.99  Horn                                    16
% 2.48/0.99  unary                                   8
% 2.48/0.99  binary                                  4
% 2.48/0.99  lits                                    50
% 2.48/0.99  lits eq                                 10
% 2.48/0.99  fd_pure                                 0
% 2.48/0.99  fd_pseudo                               0
% 2.48/0.99  fd_cond                                 5
% 2.48/0.99  fd_pseudo_cond                          0
% 2.48/0.99  AC symbols                              0
% 2.48/0.99  
% 2.48/0.99  ------ Schedule dynamic 5 is on 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  ------ 
% 2.48/0.99  Current options:
% 2.48/0.99  ------ 
% 2.48/0.99  
% 2.48/0.99  ------ Input Options
% 2.48/0.99  
% 2.48/0.99  --out_options                           all
% 2.48/0.99  --tptp_safe_out                         true
% 2.48/0.99  --problem_path                          ""
% 2.48/0.99  --include_path                          ""
% 2.48/0.99  --clausifier                            res/vclausify_rel
% 2.48/0.99  --clausifier_options                    --mode clausify
% 2.48/0.99  --stdin                                 false
% 2.48/0.99  --stats_out                             all
% 2.48/0.99  
% 2.48/0.99  ------ General Options
% 2.48/0.99  
% 2.48/0.99  --fof                                   false
% 2.48/0.99  --time_out_real                         305.
% 2.48/0.99  --time_out_virtual                      -1.
% 2.48/0.99  --symbol_type_check                     false
% 2.48/0.99  --clausify_out                          false
% 2.48/0.99  --sig_cnt_out                           false
% 2.48/0.99  --trig_cnt_out                          false
% 2.48/0.99  --trig_cnt_out_tolerance                1.
% 2.48/0.99  --trig_cnt_out_sk_spl                   false
% 2.48/0.99  --abstr_cl_out                          false
% 2.48/0.99  
% 2.48/0.99  ------ Global Options
% 2.48/0.99  
% 2.48/0.99  --schedule                              default
% 2.48/0.99  --add_important_lit                     false
% 2.48/0.99  --prop_solver_per_cl                    1000
% 2.48/0.99  --min_unsat_core                        false
% 2.48/0.99  --soft_assumptions                      false
% 2.48/0.99  --soft_lemma_size                       3
% 2.48/0.99  --prop_impl_unit_size                   0
% 2.48/0.99  --prop_impl_unit                        []
% 2.48/0.99  --share_sel_clauses                     true
% 2.48/0.99  --reset_solvers                         false
% 2.48/0.99  --bc_imp_inh                            [conj_cone]
% 2.48/0.99  --conj_cone_tolerance                   3.
% 2.48/0.99  --extra_neg_conj                        none
% 2.48/0.99  --large_theory_mode                     true
% 2.48/0.99  --prolific_symb_bound                   200
% 2.48/0.99  --lt_threshold                          2000
% 2.48/0.99  --clause_weak_htbl                      true
% 2.48/0.99  --gc_record_bc_elim                     false
% 2.48/0.99  
% 2.48/0.99  ------ Preprocessing Options
% 2.48/0.99  
% 2.48/0.99  --preprocessing_flag                    true
% 2.48/0.99  --time_out_prep_mult                    0.1
% 2.48/0.99  --splitting_mode                        input
% 2.48/0.99  --splitting_grd                         true
% 2.48/0.99  --splitting_cvd                         false
% 2.48/0.99  --splitting_cvd_svl                     false
% 2.48/0.99  --splitting_nvd                         32
% 2.48/0.99  --sub_typing                            true
% 2.48/0.99  --prep_gs_sim                           true
% 2.48/0.99  --prep_unflatten                        true
% 2.48/0.99  --prep_res_sim                          true
% 2.48/0.99  --prep_upred                            true
% 2.48/0.99  --prep_sem_filter                       exhaustive
% 2.48/0.99  --prep_sem_filter_out                   false
% 2.48/0.99  --pred_elim                             true
% 2.48/0.99  --res_sim_input                         true
% 2.48/0.99  --eq_ax_congr_red                       true
% 2.48/0.99  --pure_diseq_elim                       true
% 2.48/0.99  --brand_transform                       false
% 2.48/0.99  --non_eq_to_eq                          false
% 2.48/0.99  --prep_def_merge                        true
% 2.48/0.99  --prep_def_merge_prop_impl              false
% 2.48/0.99  --prep_def_merge_mbd                    true
% 2.48/0.99  --prep_def_merge_tr_red                 false
% 2.48/0.99  --prep_def_merge_tr_cl                  false
% 2.48/0.99  --smt_preprocessing                     true
% 2.48/0.99  --smt_ac_axioms                         fast
% 2.48/0.99  --preprocessed_out                      false
% 2.48/0.99  --preprocessed_stats                    false
% 2.48/0.99  
% 2.48/0.99  ------ Abstraction refinement Options
% 2.48/0.99  
% 2.48/0.99  --abstr_ref                             []
% 2.48/0.99  --abstr_ref_prep                        false
% 2.48/0.99  --abstr_ref_until_sat                   false
% 2.48/0.99  --abstr_ref_sig_restrict                funpre
% 2.48/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.48/0.99  --abstr_ref_under                       []
% 2.48/0.99  
% 2.48/0.99  ------ SAT Options
% 2.48/0.99  
% 2.48/0.99  --sat_mode                              false
% 2.48/0.99  --sat_fm_restart_options                ""
% 2.48/0.99  --sat_gr_def                            false
% 2.48/0.99  --sat_epr_types                         true
% 2.48/0.99  --sat_non_cyclic_types                  false
% 2.48/0.99  --sat_finite_models                     false
% 2.48/0.99  --sat_fm_lemmas                         false
% 2.48/0.99  --sat_fm_prep                           false
% 2.48/0.99  --sat_fm_uc_incr                        true
% 2.48/0.99  --sat_out_model                         small
% 2.48/0.99  --sat_out_clauses                       false
% 2.48/0.99  
% 2.48/0.99  ------ QBF Options
% 2.48/0.99  
% 2.48/0.99  --qbf_mode                              false
% 2.48/0.99  --qbf_elim_univ                         false
% 2.48/0.99  --qbf_dom_inst                          none
% 2.48/0.99  --qbf_dom_pre_inst                      false
% 2.48/0.99  --qbf_sk_in                             false
% 2.48/0.99  --qbf_pred_elim                         true
% 2.48/0.99  --qbf_split                             512
% 2.48/0.99  
% 2.48/0.99  ------ BMC1 Options
% 2.48/0.99  
% 2.48/0.99  --bmc1_incremental                      false
% 2.48/0.99  --bmc1_axioms                           reachable_all
% 2.48/0.99  --bmc1_min_bound                        0
% 2.48/0.99  --bmc1_max_bound                        -1
% 2.48/0.99  --bmc1_max_bound_default                -1
% 2.48/0.99  --bmc1_symbol_reachability              true
% 2.48/0.99  --bmc1_property_lemmas                  false
% 2.48/0.99  --bmc1_k_induction                      false
% 2.48/0.99  --bmc1_non_equiv_states                 false
% 2.48/0.99  --bmc1_deadlock                         false
% 2.48/0.99  --bmc1_ucm                              false
% 2.48/0.99  --bmc1_add_unsat_core                   none
% 2.48/0.99  --bmc1_unsat_core_children              false
% 2.48/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.48/0.99  --bmc1_out_stat                         full
% 2.48/0.99  --bmc1_ground_init                      false
% 2.48/0.99  --bmc1_pre_inst_next_state              false
% 2.48/0.99  --bmc1_pre_inst_state                   false
% 2.48/0.99  --bmc1_pre_inst_reach_state             false
% 2.48/0.99  --bmc1_out_unsat_core                   false
% 2.48/0.99  --bmc1_aig_witness_out                  false
% 2.48/0.99  --bmc1_verbose                          false
% 2.48/0.99  --bmc1_dump_clauses_tptp                false
% 2.48/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.48/0.99  --bmc1_dump_file                        -
% 2.48/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.48/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.48/0.99  --bmc1_ucm_extend_mode                  1
% 2.48/0.99  --bmc1_ucm_init_mode                    2
% 2.48/0.99  --bmc1_ucm_cone_mode                    none
% 2.48/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.48/0.99  --bmc1_ucm_relax_model                  4
% 2.48/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.48/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.48/0.99  --bmc1_ucm_layered_model                none
% 2.48/0.99  --bmc1_ucm_max_lemma_size               10
% 2.48/0.99  
% 2.48/0.99  ------ AIG Options
% 2.48/0.99  
% 2.48/0.99  --aig_mode                              false
% 2.48/0.99  
% 2.48/0.99  ------ Instantiation Options
% 2.48/0.99  
% 2.48/0.99  --instantiation_flag                    true
% 2.48/0.99  --inst_sos_flag                         false
% 2.48/0.99  --inst_sos_phase                        true
% 2.48/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.48/0.99  --inst_lit_sel_side                     none
% 2.48/0.99  --inst_solver_per_active                1400
% 2.48/0.99  --inst_solver_calls_frac                1.
% 2.48/0.99  --inst_passive_queue_type               priority_queues
% 2.48/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.48/0.99  --inst_passive_queues_freq              [25;2]
% 2.48/0.99  --inst_dismatching                      true
% 2.48/0.99  --inst_eager_unprocessed_to_passive     true
% 2.48/0.99  --inst_prop_sim_given                   true
% 2.48/0.99  --inst_prop_sim_new                     false
% 2.48/0.99  --inst_subs_new                         false
% 2.48/0.99  --inst_eq_res_simp                      false
% 2.48/0.99  --inst_subs_given                       false
% 2.48/0.99  --inst_orphan_elimination               true
% 2.48/0.99  --inst_learning_loop_flag               true
% 2.48/0.99  --inst_learning_start                   3000
% 2.48/0.99  --inst_learning_factor                  2
% 2.48/0.99  --inst_start_prop_sim_after_learn       3
% 2.48/0.99  --inst_sel_renew                        solver
% 2.48/0.99  --inst_lit_activity_flag                true
% 2.48/0.99  --inst_restr_to_given                   false
% 2.48/0.99  --inst_activity_threshold               500
% 2.48/0.99  --inst_out_proof                        true
% 2.48/0.99  
% 2.48/0.99  ------ Resolution Options
% 2.48/0.99  
% 2.48/0.99  --resolution_flag                       false
% 2.48/0.99  --res_lit_sel                           adaptive
% 2.48/0.99  --res_lit_sel_side                      none
% 2.48/0.99  --res_ordering                          kbo
% 2.48/0.99  --res_to_prop_solver                    active
% 2.48/0.99  --res_prop_simpl_new                    false
% 2.48/0.99  --res_prop_simpl_given                  true
% 2.48/0.99  --res_passive_queue_type                priority_queues
% 2.48/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.48/0.99  --res_passive_queues_freq               [15;5]
% 2.48/0.99  --res_forward_subs                      full
% 2.48/0.99  --res_backward_subs                     full
% 2.48/0.99  --res_forward_subs_resolution           true
% 2.48/0.99  --res_backward_subs_resolution          true
% 2.48/0.99  --res_orphan_elimination                true
% 2.48/0.99  --res_time_limit                        2.
% 2.48/0.99  --res_out_proof                         true
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Options
% 2.48/0.99  
% 2.48/0.99  --superposition_flag                    true
% 2.48/0.99  --sup_passive_queue_type                priority_queues
% 2.48/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.48/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.48/0.99  --demod_completeness_check              fast
% 2.48/0.99  --demod_use_ground                      true
% 2.48/0.99  --sup_to_prop_solver                    passive
% 2.48/0.99  --sup_prop_simpl_new                    true
% 2.48/0.99  --sup_prop_simpl_given                  true
% 2.48/0.99  --sup_fun_splitting                     false
% 2.48/0.99  --sup_smt_interval                      50000
% 2.48/0.99  
% 2.48/0.99  ------ Superposition Simplification Setup
% 2.48/0.99  
% 2.48/0.99  --sup_indices_passive                   []
% 2.48/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.48/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.48/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_full_bw                           [BwDemod]
% 2.48/0.99  --sup_immed_triv                        [TrivRules]
% 2.48/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.48/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_immed_bw_main                     []
% 2.48/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.48/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.48/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.48/0.99  
% 2.48/0.99  ------ Combination Options
% 2.48/0.99  
% 2.48/0.99  --comb_res_mult                         3
% 2.48/0.99  --comb_sup_mult                         2
% 2.48/0.99  --comb_inst_mult                        10
% 2.48/0.99  
% 2.48/0.99  ------ Debug Options
% 2.48/0.99  
% 2.48/0.99  --dbg_backtrace                         false
% 2.48/0.99  --dbg_dump_prop_clauses                 false
% 2.48/0.99  --dbg_dump_prop_clauses_file            -
% 2.48/0.99  --dbg_out_stat                          false
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  ------ Proving...
% 2.48/0.99  
% 2.48/0.99  
% 2.48/0.99  % SZS status Theorem for theBenchmark.p
% 2.48/0.99  
% 2.48/0.99   Resolution empty clause
% 2.48/0.99  
% 2.48/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.48/0.99  
% 2.48/0.99  fof(f1,axiom,(
% 2.48/0.99    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f34,plain,(
% 2.48/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.48/0.99    inference(nnf_transformation,[],[f1])).
% 2.48/0.99  
% 2.48/0.99  fof(f35,plain,(
% 2.48/0.99    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.48/0.99    inference(rectify,[],[f34])).
% 2.48/0.99  
% 2.48/0.99  fof(f36,plain,(
% 2.48/0.99    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f37,plain,(
% 2.48/0.99    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 2.48/0.99  
% 2.48/0.99  fof(f49,plain,(
% 2.48/0.99    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f37])).
% 2.48/0.99  
% 2.48/0.99  fof(f7,axiom,(
% 2.48/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f19,plain,(
% 2.48/0.99    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.48/0.99    inference(ennf_transformation,[],[f7])).
% 2.48/0.99  
% 2.48/0.99  fof(f55,plain,(
% 2.48/0.99    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f19])).
% 2.48/0.99  
% 2.48/0.99  fof(f15,conjecture,(
% 2.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f16,negated_conjecture,(
% 2.48/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.48/0.99    inference(negated_conjecture,[],[f15])).
% 2.48/0.99  
% 2.48/0.99  fof(f32,plain,(
% 2.48/0.99    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.48/0.99    inference(ennf_transformation,[],[f16])).
% 2.48/0.99  
% 2.48/0.99  fof(f33,plain,(
% 2.48/0.99    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.48/0.99    inference(flattening,[],[f32])).
% 2.48/0.99  
% 2.48/0.99  fof(f46,plain,(
% 2.48/0.99    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK4))) )),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f45,plain,(
% 2.48/0.99    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(X1)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f47,plain,(
% 2.48/0.99    (v3_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) & v1_xboole_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f33,f46,f45])).
% 2.48/0.99  
% 2.48/0.99  fof(f72,plain,(
% 2.48/0.99    v1_xboole_0(sK4)),
% 2.48/0.99    inference(cnf_transformation,[],[f47])).
% 2.48/0.99  
% 2.48/0.99  fof(f2,axiom,(
% 2.48/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f18,plain,(
% 2.48/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.48/0.99    inference(ennf_transformation,[],[f2])).
% 2.48/0.99  
% 2.48/0.99  fof(f50,plain,(
% 2.48/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f18])).
% 2.48/0.99  
% 2.48/0.99  fof(f74,plain,(
% 2.48/0.99    v3_tex_2(sK4,sK3)),
% 2.48/0.99    inference(cnf_transformation,[],[f47])).
% 2.48/0.99  
% 2.48/0.99  fof(f4,axiom,(
% 2.48/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f52,plain,(
% 2.48/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f4])).
% 2.48/0.99  
% 2.48/0.99  fof(f13,axiom,(
% 2.48/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f28,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(ennf_transformation,[],[f13])).
% 2.48/0.99  
% 2.48/0.99  fof(f29,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(flattening,[],[f28])).
% 2.48/0.99  
% 2.48/0.99  fof(f40,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(nnf_transformation,[],[f29])).
% 2.48/0.99  
% 2.48/0.99  fof(f41,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(flattening,[],[f40])).
% 2.48/0.99  
% 2.48/0.99  fof(f42,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(rectify,[],[f41])).
% 2.48/0.99  
% 2.48/0.99  fof(f43,plain,(
% 2.48/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f44,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f42,f43])).
% 2.48/0.99  
% 2.48/0.99  fof(f63,plain,(
% 2.48/0.99    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f44])).
% 2.48/0.99  
% 2.48/0.99  fof(f71,plain,(
% 2.48/0.99    l1_pre_topc(sK3)),
% 2.48/0.99    inference(cnf_transformation,[],[f47])).
% 2.48/0.99  
% 2.48/0.99  fof(f6,axiom,(
% 2.48/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f54,plain,(
% 2.48/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.48/0.99    inference(cnf_transformation,[],[f6])).
% 2.48/0.99  
% 2.48/0.99  fof(f69,plain,(
% 2.48/0.99    ~v2_struct_0(sK3)),
% 2.48/0.99    inference(cnf_transformation,[],[f47])).
% 2.48/0.99  
% 2.48/0.99  fof(f11,axiom,(
% 2.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f17,plain,(
% 2.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/0.99    inference(pure_predicate_removal,[],[f11])).
% 2.48/0.99  
% 2.48/0.99  fof(f24,plain,(
% 2.48/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.99    inference(ennf_transformation,[],[f17])).
% 2.48/0.99  
% 2.48/0.99  fof(f25,plain,(
% 2.48/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.99    inference(flattening,[],[f24])).
% 2.48/0.99  
% 2.48/0.99  fof(f38,plain,(
% 2.48/0.99    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.48/0.99    introduced(choice_axiom,[])).
% 2.48/0.99  
% 2.48/0.99  fof(f39,plain,(
% 2.48/0.99    ! [X0] : ((~v1_xboole_0(sK1(X0)) & m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f38])).
% 2.48/0.99  
% 2.48/0.99  fof(f59,plain,(
% 2.48/0.99    ( ! [X0] : (m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f39])).
% 2.48/0.99  
% 2.48/0.99  fof(f70,plain,(
% 2.48/0.99    v2_pre_topc(sK3)),
% 2.48/0.99    inference(cnf_transformation,[],[f47])).
% 2.48/0.99  
% 2.48/0.99  fof(f60,plain,(
% 2.48/0.99    ( ! [X0] : (~v1_xboole_0(sK1(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f39])).
% 2.48/0.99  
% 2.48/0.99  fof(f10,axiom,(
% 2.48/0.99    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f23,plain,(
% 2.48/0.99    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.48/0.99    inference(ennf_transformation,[],[f10])).
% 2.48/0.99  
% 2.48/0.99  fof(f58,plain,(
% 2.48/0.99    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f23])).
% 2.48/0.99  
% 2.48/0.99  fof(f8,axiom,(
% 2.48/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f20,plain,(
% 2.48/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.48/0.99    inference(ennf_transformation,[],[f8])).
% 2.48/0.99  
% 2.48/0.99  fof(f56,plain,(
% 2.48/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f20])).
% 2.48/0.99  
% 2.48/0.99  fof(f12,axiom,(
% 2.48/0.99    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f26,plain,(
% 2.48/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.48/0.99    inference(ennf_transformation,[],[f12])).
% 2.48/0.99  
% 2.48/0.99  fof(f27,plain,(
% 2.48/0.99    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.48/0.99    inference(flattening,[],[f26])).
% 2.48/0.99  
% 2.48/0.99  fof(f61,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f27])).
% 2.48/0.99  
% 2.48/0.99  fof(f14,axiom,(
% 2.48/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f30,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.48/0.99    inference(ennf_transformation,[],[f14])).
% 2.48/0.99  
% 2.48/0.99  fof(f31,plain,(
% 2.48/0.99    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.48/0.99    inference(flattening,[],[f30])).
% 2.48/0.99  
% 2.48/0.99  fof(f68,plain,(
% 2.48/0.99    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f31])).
% 2.48/0.99  
% 2.48/0.99  fof(f3,axiom,(
% 2.48/0.99    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f51,plain,(
% 2.48/0.99    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.48/0.99    inference(cnf_transformation,[],[f3])).
% 2.48/0.99  
% 2.48/0.99  fof(f5,axiom,(
% 2.48/0.99    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.48/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.48/0.99  
% 2.48/0.99  fof(f53,plain,(
% 2.48/0.99    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.48/0.99    inference(cnf_transformation,[],[f5])).
% 2.48/0.99  
% 2.48/0.99  cnf(c_0,plain,
% 2.48/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.48/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_7,plain,
% 2.48/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~ r2_hidden(X0,X1) ),
% 2.48/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_347,plain,
% 2.48/0.99      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
% 2.48/0.99      | v1_xboole_0(X2)
% 2.48/0.99      | X1 != X2
% 2.48/0.99      | sK0(X2) != X0 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_7]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_348,plain,
% 2.48/0.99      ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0)) | v1_xboole_0(X0) ),
% 2.48/0.99      inference(unflattening,[status(thm)],[c_347]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1244,plain,
% 2.48/0.99      ( m1_subset_1(k1_tarski(sK0(X0)),k1_zfmisc_1(X0)) = iProver_top
% 2.48/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_23,negated_conjecture,
% 2.48/0.99      ( v1_xboole_0(sK4) ),
% 2.48/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1249,plain,
% 2.48/0.99      ( v1_xboole_0(sK4) = iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2,plain,
% 2.48/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.48/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1253,plain,
% 2.48/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2063,plain,
% 2.48/0.99      ( sK4 = k1_xboole_0 ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_1249,c_1253]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_21,negated_conjecture,
% 2.48/0.99      ( v3_tex_2(sK4,sK3) ),
% 2.48/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_4,plain,
% 2.48/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.48/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_18,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,X1)
% 2.48/0.99      | ~ v3_tex_2(X2,X1)
% 2.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/0.99      | ~ r1_tarski(X2,X0)
% 2.48/0.99      | ~ l1_pre_topc(X1)
% 2.48/0.99      | X0 = X2 ),
% 2.48/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_24,negated_conjecture,
% 2.48/0.99      ( l1_pre_topc(sK3) ),
% 2.48/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_491,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,X1)
% 2.48/0.99      | ~ v3_tex_2(X2,X1)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.48/0.99      | ~ r1_tarski(X2,X0)
% 2.48/0.99      | X2 = X0
% 2.48/0.99      | sK3 != X1 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_492,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ v3_tex_2(X1,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | ~ r1_tarski(X1,X0)
% 2.48/0.99      | X1 = X0 ),
% 2.48/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_618,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ v3_tex_2(X1,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | X0 != X2
% 2.48/0.99      | X0 = X1
% 2.48/0.99      | k1_xboole_0 != X1 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_492]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_619,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | X0 = k1_xboole_0 ),
% 2.48/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_6,plain,
% 2.48/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.48/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_633,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ v3_tex_2(k1_xboole_0,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | X0 = k1_xboole_0 ),
% 2.48/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_619,c_6]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_660,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | sK3 != sK3
% 2.48/0.99      | sK4 != k1_xboole_0
% 2.48/0.99      | k1_xboole_0 = X0 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_633]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_798,plain,
% 2.48/0.99      ( ~ v2_tex_2(X0,sK3)
% 2.48/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | sK4 != k1_xboole_0
% 2.48/0.99      | k1_xboole_0 = X0 ),
% 2.48/0.99      inference(equality_resolution_simp,[status(thm)],[c_660]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_1234,plain,
% 2.48/0.99      ( sK4 != k1_xboole_0
% 2.48/0.99      | k1_xboole_0 = X0
% 2.48/0.99      | v2_tex_2(X0,sK3) != iProver_top
% 2.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_798]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2101,plain,
% 2.48/0.99      ( k1_xboole_0 = X0
% 2.48/0.99      | k1_xboole_0 != k1_xboole_0
% 2.48/0.99      | v2_tex_2(X0,sK3) != iProver_top
% 2.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.48/0.99      inference(demodulation,[status(thm)],[c_2063,c_1234]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2110,plain,
% 2.48/0.99      ( k1_xboole_0 = X0
% 2.48/0.99      | v2_tex_2(X0,sK3) != iProver_top
% 2.48/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top ),
% 2.48/0.99      inference(equality_resolution_simp,[status(thm)],[c_2101]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_2973,plain,
% 2.48/0.99      ( k1_tarski(sK0(u1_struct_0(sK3))) = k1_xboole_0
% 2.48/0.99      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK3))),sK3) != iProver_top
% 2.48/0.99      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.48/0.99      inference(superposition,[status(thm)],[c_1244,c_2110]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_26,negated_conjecture,
% 2.48/0.99      ( ~ v2_struct_0(sK3) ),
% 2.48/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_27,plain,
% 2.48/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_29,plain,
% 2.48/0.99      ( l1_pre_topc(sK3) = iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_12,plain,
% 2.48/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/0.99      | v2_struct_0(X0)
% 2.48/0.99      | ~ v2_pre_topc(X0)
% 2.48/0.99      | ~ l1_pre_topc(X0) ),
% 2.48/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_25,negated_conjecture,
% 2.48/0.99      ( v2_pre_topc(sK3) ),
% 2.48/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_306,plain,
% 2.48/0.99      ( m1_subset_1(sK1(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.48/0.99      | v2_struct_0(X0)
% 2.48/0.99      | ~ l1_pre_topc(X0)
% 2.48/0.99      | sK3 != X0 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_25]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_307,plain,
% 2.48/0.99      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/0.99      | v2_struct_0(sK3)
% 2.48/0.99      | ~ l1_pre_topc(sK3) ),
% 2.48/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_308,plain,
% 2.48/0.99      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top
% 2.48/0.99      | v2_struct_0(sK3) = iProver_top
% 2.48/0.99      | l1_pre_topc(sK3) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_11,plain,
% 2.48/0.99      ( v2_struct_0(X0)
% 2.48/0.99      | ~ v2_pre_topc(X0)
% 2.48/0.99      | ~ l1_pre_topc(X0)
% 2.48/0.99      | ~ v1_xboole_0(sK1(X0)) ),
% 2.48/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_317,plain,
% 2.48/0.99      ( v2_struct_0(X0)
% 2.48/0.99      | ~ l1_pre_topc(X0)
% 2.48/0.99      | ~ v1_xboole_0(sK1(X0))
% 2.48/0.99      | sK3 != X0 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_318,plain,
% 2.48/0.99      ( v2_struct_0(sK3) | ~ l1_pre_topc(sK3) | ~ v1_xboole_0(sK1(sK3)) ),
% 2.48/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_319,plain,
% 2.48/0.99      ( v2_struct_0(sK3) = iProver_top
% 2.48/0.99      | l1_pre_topc(sK3) != iProver_top
% 2.48/0.99      | v1_xboole_0(sK1(sK3)) != iProver_top ),
% 2.48/0.99      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_10,plain,
% 2.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/0.99      | ~ r2_hidden(X2,X0)
% 2.48/0.99      | ~ v1_xboole_0(X1) ),
% 2.48/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_376,plain,
% 2.48/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/0.99      | ~ v1_xboole_0(X1)
% 2.48/0.99      | v1_xboole_0(X2)
% 2.48/0.99      | X0 != X2
% 2.48/0.99      | sK0(X2) != X3 ),
% 2.48/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_10]) ).
% 2.48/0.99  
% 2.48/0.99  cnf(c_377,plain,
% 2.48/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.48/1.00      | ~ v1_xboole_0(X1)
% 2.48/1.00      | v1_xboole_0(X0) ),
% 2.48/1.00      inference(unflattening,[status(thm)],[c_376]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1387,plain,
% 2.48/1.00      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(X0))
% 2.48/1.00      | ~ v1_xboole_0(X0)
% 2.48/1.00      | v1_xboole_0(sK1(sK3)) ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_377]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1470,plain,
% 2.48/1.00      ( ~ m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.48/1.00      | ~ v1_xboole_0(u1_struct_0(sK3))
% 2.48/1.00      | v1_xboole_0(sK1(sK3)) ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_1387]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1471,plain,
% 2.48/1.00      ( m1_subset_1(sK1(sK3),k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.48/1.00      | v1_xboole_0(sK1(sK3)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_1470]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_8,plain,
% 2.48/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.48/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_335,plain,
% 2.48/1.00      ( m1_subset_1(X0,X1) | v1_xboole_0(X2) | X1 != X2 | sK0(X2) != X0 ),
% 2.48/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_8]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_336,plain,
% 2.48/1.00      ( m1_subset_1(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.48/1.00      inference(unflattening,[status(thm)],[c_335]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1572,plain,
% 2.48/1.00      ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3))
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_336]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1573,plain,
% 2.48/1.00      ( m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) = iProver_top
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_1572]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_907,plain,
% 2.48/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.48/1.00      theory(equality) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1586,plain,
% 2.48/1.00      ( ~ v1_xboole_0(X0)
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3))
% 2.48/1.00      | u1_struct_0(sK3) != X0 ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_907]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1587,plain,
% 2.48/1.00      ( u1_struct_0(sK3) != X0
% 2.48/1.00      | v1_xboole_0(X0) != iProver_top
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_1586]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1589,plain,
% 2.48/1.00      ( u1_struct_0(sK3) != k1_xboole_0
% 2.48/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top
% 2.48/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.48/1.00      inference(instantiation,[status(thm)],[c_1587]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2104,plain,
% 2.48/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.48/1.00      inference(demodulation,[status(thm)],[c_2063,c_1249]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1245,plain,
% 2.48/1.00      ( m1_subset_1(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_13,plain,
% 2.48/1.00      ( ~ m1_subset_1(X0,X1)
% 2.48/1.00      | v1_xboole_0(X1)
% 2.48/1.00      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.48/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1251,plain,
% 2.48/1.00      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.48/1.00      | m1_subset_1(X1,X0) != iProver_top
% 2.48/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2651,plain,
% 2.48/1.00      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0))
% 2.48/1.00      | v1_xboole_0(X0) = iProver_top ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_1245,c_1251]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2686,plain,
% 2.48/1.00      ( k6_domain_1(X0,sK0(X0)) = k1_tarski(sK0(X0)) | k1_xboole_0 = X0 ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_2651,c_1253]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_20,plain,
% 2.48/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.48/1.00      | v2_struct_0(X0)
% 2.48/1.00      | ~ v2_pre_topc(X0)
% 2.48/1.00      | ~ l1_pre_topc(X0) ),
% 2.48/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_288,plain,
% 2.48/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.48/1.00      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.48/1.00      | v2_struct_0(X0)
% 2.48/1.00      | ~ l1_pre_topc(X0)
% 2.48/1.00      | sK3 != X0 ),
% 2.48/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_289,plain,
% 2.48/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.48/1.00      | v2_struct_0(sK3)
% 2.48/1.00      | ~ l1_pre_topc(sK3) ),
% 2.48/1.00      inference(unflattening,[status(thm)],[c_288]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_293,plain,
% 2.48/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3)
% 2.48/1.00      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_289,c_26,c_24]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1248,plain,
% 2.48/1.00      ( v2_tex_2(k6_domain_1(u1_struct_0(sK3),X0),sK3) = iProver_top
% 2.48/1.00      | m1_subset_1(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.48/1.00      inference(predicate_to_equality,[status(thm)],[c_293]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2733,plain,
% 2.48/1.00      ( u1_struct_0(sK3) = k1_xboole_0
% 2.48/1.00      | v2_tex_2(k1_tarski(sK0(u1_struct_0(sK3))),sK3) = iProver_top
% 2.48/1.00      | m1_subset_1(sK0(u1_struct_0(sK3)),u1_struct_0(sK3)) != iProver_top ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_2686,c_1248]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2996,plain,
% 2.48/1.00      ( k1_tarski(sK0(u1_struct_0(sK3))) = k1_xboole_0 ),
% 2.48/1.00      inference(global_propositional_subsumption,
% 2.48/1.00                [status(thm)],
% 2.48/1.00                [c_2973,c_27,c_29,c_308,c_319,c_1471,c_1573,c_1589,c_2104,
% 2.48/1.00                 c_2733]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_3,plain,
% 2.48/1.00      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.48/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_5,plain,
% 2.48/1.00      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.48/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_1744,plain,
% 2.48/1.00      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.48/1.00      inference(superposition,[status(thm)],[c_3,c_5]) ).
% 2.48/1.00  
% 2.48/1.00  cnf(c_2999,plain,
% 2.48/1.00      ( $false ),
% 2.48/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_2996,c_1744]) ).
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.48/1.00  
% 2.48/1.00  ------                               Statistics
% 2.48/1.00  
% 2.48/1.00  ------ General
% 2.48/1.00  
% 2.48/1.00  abstr_ref_over_cycles:                  0
% 2.48/1.00  abstr_ref_under_cycles:                 0
% 2.48/1.00  gc_basic_clause_elim:                   0
% 2.48/1.00  forced_gc_time:                         0
% 2.48/1.00  parsing_time:                           0.01
% 2.48/1.00  unif_index_cands_time:                  0.
% 2.48/1.00  unif_index_add_time:                    0.
% 2.48/1.00  orderings_time:                         0.
% 2.48/1.00  out_proof_time:                         0.011
% 2.48/1.00  total_time:                             0.13
% 2.48/1.00  num_of_symbols:                         52
% 2.48/1.00  num_of_terms:                           2091
% 2.48/1.00  
% 2.48/1.00  ------ Preprocessing
% 2.48/1.00  
% 2.48/1.00  num_of_splits:                          3
% 2.48/1.00  num_of_split_atoms:                     1
% 2.48/1.00  num_of_reused_defs:                     2
% 2.48/1.00  num_eq_ax_congr_red:                    12
% 2.48/1.00  num_of_sem_filtered_clauses:            1
% 2.48/1.00  num_of_subtypes:                        0
% 2.48/1.00  monotx_restored_types:                  0
% 2.48/1.00  sat_num_of_epr_types:                   0
% 2.48/1.00  sat_num_of_non_cyclic_types:            0
% 2.48/1.00  sat_guarded_non_collapsed_types:        0
% 2.48/1.00  num_pure_diseq_elim:                    0
% 2.48/1.00  simp_replaced_by:                       0
% 2.48/1.00  res_preprocessed:                       111
% 2.48/1.00  prep_upred:                             0
% 2.48/1.00  prep_unflattend:                        31
% 2.48/1.00  smt_new_axioms:                         0
% 2.48/1.00  pred_elim_cands:                        3
% 2.48/1.00  pred_elim:                              6
% 2.48/1.00  pred_elim_cl:                           8
% 2.48/1.00  pred_elim_cycles:                       9
% 2.48/1.00  merged_defs:                            0
% 2.48/1.00  merged_defs_ncl:                        0
% 2.48/1.00  bin_hyper_res:                          0
% 2.48/1.00  prep_cycles:                            4
% 2.48/1.00  pred_elim_time:                         0.01
% 2.48/1.00  splitting_time:                         0.
% 2.48/1.00  sem_filter_time:                        0.
% 2.48/1.00  monotx_time:                            0.
% 2.48/1.00  subtype_inf_time:                       0.
% 2.48/1.00  
% 2.48/1.00  ------ Problem properties
% 2.48/1.00  
% 2.48/1.00  clauses:                                22
% 2.48/1.00  conjectures:                            2
% 2.48/1.00  epr:                                    3
% 2.48/1.00  horn:                                   16
% 2.48/1.00  ground:                                 8
% 2.48/1.00  unary:                                  8
% 2.48/1.00  binary:                                 4
% 2.48/1.00  lits:                                   50
% 2.48/1.00  lits_eq:                                10
% 2.48/1.00  fd_pure:                                0
% 2.48/1.00  fd_pseudo:                              0
% 2.48/1.00  fd_cond:                                5
% 2.48/1.00  fd_pseudo_cond:                         0
% 2.48/1.00  ac_symbols:                             0
% 2.48/1.00  
% 2.48/1.00  ------ Propositional Solver
% 2.48/1.00  
% 2.48/1.00  prop_solver_calls:                      28
% 2.48/1.00  prop_fast_solver_calls:                 757
% 2.48/1.00  smt_solver_calls:                       0
% 2.48/1.00  smt_fast_solver_calls:                  0
% 2.48/1.00  prop_num_of_clauses:                    925
% 2.48/1.00  prop_preprocess_simplified:             3725
% 2.48/1.00  prop_fo_subsumed:                       29
% 2.48/1.00  prop_solver_time:                       0.
% 2.48/1.00  smt_solver_time:                        0.
% 2.48/1.00  smt_fast_solver_time:                   0.
% 2.48/1.00  prop_fast_solver_time:                  0.
% 2.48/1.00  prop_unsat_core_time:                   0.
% 2.48/1.00  
% 2.48/1.00  ------ QBF
% 2.48/1.00  
% 2.48/1.00  qbf_q_res:                              0
% 2.48/1.00  qbf_num_tautologies:                    0
% 2.48/1.00  qbf_prep_cycles:                        0
% 2.48/1.00  
% 2.48/1.00  ------ BMC1
% 2.48/1.00  
% 2.48/1.00  bmc1_current_bound:                     -1
% 2.48/1.00  bmc1_last_solved_bound:                 -1
% 2.48/1.00  bmc1_unsat_core_size:                   -1
% 2.48/1.00  bmc1_unsat_core_parents_size:           -1
% 2.48/1.00  bmc1_merge_next_fun:                    0
% 2.48/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.48/1.00  
% 2.48/1.00  ------ Instantiation
% 2.48/1.00  
% 2.48/1.00  inst_num_of_clauses:                    287
% 2.48/1.00  inst_num_in_passive:                    91
% 2.48/1.00  inst_num_in_active:                     196
% 2.48/1.00  inst_num_in_unprocessed:                0
% 2.48/1.00  inst_num_of_loops:                      220
% 2.48/1.00  inst_num_of_learning_restarts:          0
% 2.48/1.00  inst_num_moves_active_passive:          21
% 2.48/1.00  inst_lit_activity:                      0
% 2.48/1.00  inst_lit_activity_moves:                0
% 2.48/1.00  inst_num_tautologies:                   0
% 2.48/1.00  inst_num_prop_implied:                  0
% 2.48/1.00  inst_num_existing_simplified:           0
% 2.48/1.00  inst_num_eq_res_simplified:             0
% 2.48/1.00  inst_num_child_elim:                    0
% 2.48/1.00  inst_num_of_dismatching_blockings:      64
% 2.48/1.00  inst_num_of_non_proper_insts:           262
% 2.48/1.00  inst_num_of_duplicates:                 0
% 2.48/1.00  inst_inst_num_from_inst_to_res:         0
% 2.48/1.00  inst_dismatching_checking_time:         0.
% 2.48/1.00  
% 2.48/1.00  ------ Resolution
% 2.48/1.00  
% 2.48/1.00  res_num_of_clauses:                     0
% 2.48/1.00  res_num_in_passive:                     0
% 2.48/1.00  res_num_in_active:                      0
% 2.48/1.00  res_num_of_loops:                       115
% 2.48/1.00  res_forward_subset_subsumed:            30
% 2.48/1.00  res_backward_subset_subsumed:           0
% 2.48/1.00  res_forward_subsumed:                   0
% 2.48/1.00  res_backward_subsumed:                  0
% 2.48/1.00  res_forward_subsumption_resolution:     5
% 2.48/1.00  res_backward_subsumption_resolution:    0
% 2.48/1.00  res_clause_to_clause_subsumption:       81
% 2.48/1.00  res_orphan_elimination:                 0
% 2.48/1.00  res_tautology_del:                      31
% 2.48/1.00  res_num_eq_res_simplified:              1
% 2.48/1.00  res_num_sel_changes:                    0
% 2.48/1.00  res_moves_from_active_to_pass:          0
% 2.48/1.00  
% 2.48/1.00  ------ Superposition
% 2.48/1.00  
% 2.48/1.00  sup_time_total:                         0.
% 2.48/1.00  sup_time_generating:                    0.
% 2.48/1.00  sup_time_sim_full:                      0.
% 2.48/1.00  sup_time_sim_immed:                     0.
% 2.48/1.00  
% 2.48/1.00  sup_num_of_clauses:                     41
% 2.48/1.00  sup_num_in_active:                      36
% 2.48/1.00  sup_num_in_passive:                     5
% 2.48/1.00  sup_num_of_loops:                       43
% 2.48/1.00  sup_fw_superposition:                   18
% 2.48/1.00  sup_bw_superposition:                   18
% 2.48/1.00  sup_immediate_simplified:               5
% 2.48/1.00  sup_given_eliminated:                   0
% 2.48/1.00  comparisons_done:                       0
% 2.48/1.00  comparisons_avoided:                    8
% 2.48/1.00  
% 2.48/1.00  ------ Simplifications
% 2.48/1.00  
% 2.48/1.00  
% 2.48/1.00  sim_fw_subset_subsumed:                 4
% 2.48/1.00  sim_bw_subset_subsumed:                 3
% 2.48/1.00  sim_fw_subsumed:                        1
% 2.48/1.00  sim_bw_subsumed:                        0
% 2.48/1.00  sim_fw_subsumption_res:                 1
% 2.48/1.00  sim_bw_subsumption_res:                 0
% 2.48/1.00  sim_tautology_del:                      2
% 2.48/1.00  sim_eq_tautology_del:                   3
% 2.48/1.00  sim_eq_res_simp:                        1
% 2.48/1.00  sim_fw_demodulated:                     0
% 2.48/1.00  sim_bw_demodulated:                     4
% 2.48/1.00  sim_light_normalised:                   0
% 2.48/1.00  sim_joinable_taut:                      0
% 2.48/1.00  sim_joinable_simp:                      0
% 2.48/1.00  sim_ac_normalised:                      0
% 2.48/1.00  sim_smt_subsumption:                    0
% 2.48/1.00  
%------------------------------------------------------------------------------
