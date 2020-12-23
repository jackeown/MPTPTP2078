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
% DateTime   : Thu Dec  3 12:26:28 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 266 expanded)
%              Number of clauses        :   57 (  77 expanded)
%              Number of leaves         :   17 (  75 expanded)
%              Depth                    :   21
%              Number of atoms          :  380 (1332 expanded)
%              Number of equality atoms :  113 ( 260 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,X1)
                 => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tex_2(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( r2_hidden(X2,X1)
                   => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)))
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & r2_hidden(X2,sK4)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK4,X0)
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & r2_hidden(X2,X1)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & v2_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & v2_tex_2(X1,sK3)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f36,f35,f34])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f63])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                  | ~ r1_tarski(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ? [X2] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
                  & r1_tarski(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
                & r1_tarski(sK2(X0,X1),X1)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).

fof(f40,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f63])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f20])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).

fof(f38,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f62,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1978,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1983,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1975,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1981,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_299,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_300,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_299])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_304,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_300,c_22,c_21])).

cnf(c_305,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_304])).

cnf(c_1973,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_305])).

cnf(c_2488,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_1973])).

cnf(c_2910,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1975,c_2488])).

cnf(c_18,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_27,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2952,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2910,c_27])).

cnf(c_3142,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) != iProver_top
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_2952])).

cnf(c_3206,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1983,c_3142])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1980,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2423,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1975,c_1980])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1984,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3391,plain,
    ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2423,c_1984])).

cnf(c_5440,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3206,c_3391])).

cnf(c_5450,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
    inference(superposition,[status(thm)],[c_1978,c_5440])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1977,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1979,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3017,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1977,c_1979])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1987,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3743,plain,
    ( r2_hidden(X0,sK4) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3391,c_1987])).

cnf(c_29,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3553,plain,
    ( ~ r1_tarski(sK4,X0)
    | r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4238,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_3553])).

cnf(c_4241,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4238])).

cnf(c_2171,plain,
    ( ~ r2_hidden(X0,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4240,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_2171])).

cnf(c_4243,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4240])).

cnf(c_4279,plain,
    ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3743,c_29,c_2423,c_4241,c_4243])).

cnf(c_4284,plain,
    ( k2_enumset1(sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(superposition,[status(thm)],[c_3017,c_4279])).

cnf(c_5457,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(light_normalisation,[status(thm)],[c_5450,c_4284])).

cnf(c_1485,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2181,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1485])).

cnf(c_1486,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2133,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_2180,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_2133])).

cnf(c_15,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f62])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5457,c_2181,c_2180,c_15])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:50:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.44/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/0.93  
% 2.44/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.93  
% 2.44/0.93  ------  iProver source info
% 2.44/0.93  
% 2.44/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.93  git: non_committed_changes: false
% 2.44/0.93  git: last_make_outside_of_git: false
% 2.44/0.93  
% 2.44/0.93  ------ 
% 2.44/0.93  
% 2.44/0.93  ------ Input Options
% 2.44/0.93  
% 2.44/0.93  --out_options                           all
% 2.44/0.93  --tptp_safe_out                         true
% 2.44/0.93  --problem_path                          ""
% 2.44/0.93  --include_path                          ""
% 2.44/0.93  --clausifier                            res/vclausify_rel
% 2.44/0.93  --clausifier_options                    --mode clausify
% 2.44/0.93  --stdin                                 false
% 2.44/0.93  --stats_out                             all
% 2.44/0.93  
% 2.44/0.93  ------ General Options
% 2.44/0.93  
% 2.44/0.93  --fof                                   false
% 2.44/0.93  --time_out_real                         305.
% 2.44/0.93  --time_out_virtual                      -1.
% 2.44/0.93  --symbol_type_check                     false
% 2.44/0.93  --clausify_out                          false
% 2.44/0.93  --sig_cnt_out                           false
% 2.44/0.93  --trig_cnt_out                          false
% 2.44/0.93  --trig_cnt_out_tolerance                1.
% 2.44/0.93  --trig_cnt_out_sk_spl                   false
% 2.44/0.93  --abstr_cl_out                          false
% 2.44/0.93  
% 2.44/0.93  ------ Global Options
% 2.44/0.93  
% 2.44/0.93  --schedule                              default
% 2.44/0.93  --add_important_lit                     false
% 2.44/0.93  --prop_solver_per_cl                    1000
% 2.44/0.93  --min_unsat_core                        false
% 2.44/0.93  --soft_assumptions                      false
% 2.44/0.93  --soft_lemma_size                       3
% 2.44/0.93  --prop_impl_unit_size                   0
% 2.44/0.93  --prop_impl_unit                        []
% 2.44/0.93  --share_sel_clauses                     true
% 2.44/0.93  --reset_solvers                         false
% 2.44/0.93  --bc_imp_inh                            [conj_cone]
% 2.44/0.93  --conj_cone_tolerance                   3.
% 2.44/0.93  --extra_neg_conj                        none
% 2.44/0.93  --large_theory_mode                     true
% 2.44/0.93  --prolific_symb_bound                   200
% 2.44/0.93  --lt_threshold                          2000
% 2.44/0.93  --clause_weak_htbl                      true
% 2.44/0.93  --gc_record_bc_elim                     false
% 2.44/0.93  
% 2.44/0.93  ------ Preprocessing Options
% 2.44/0.93  
% 2.44/0.93  --preprocessing_flag                    true
% 2.44/0.93  --time_out_prep_mult                    0.1
% 2.44/0.93  --splitting_mode                        input
% 2.44/0.93  --splitting_grd                         true
% 2.44/0.93  --splitting_cvd                         false
% 2.44/0.93  --splitting_cvd_svl                     false
% 2.44/0.93  --splitting_nvd                         32
% 2.44/0.93  --sub_typing                            true
% 2.44/0.93  --prep_gs_sim                           true
% 2.44/0.93  --prep_unflatten                        true
% 2.44/0.93  --prep_res_sim                          true
% 2.44/0.93  --prep_upred                            true
% 2.44/0.93  --prep_sem_filter                       exhaustive
% 2.44/0.93  --prep_sem_filter_out                   false
% 2.44/0.93  --pred_elim                             true
% 2.44/0.93  --res_sim_input                         true
% 2.44/0.93  --eq_ax_congr_red                       true
% 2.44/0.93  --pure_diseq_elim                       true
% 2.44/0.93  --brand_transform                       false
% 2.44/0.93  --non_eq_to_eq                          false
% 2.44/0.93  --prep_def_merge                        true
% 2.44/0.93  --prep_def_merge_prop_impl              false
% 2.44/0.93  --prep_def_merge_mbd                    true
% 2.44/0.93  --prep_def_merge_tr_red                 false
% 2.44/0.93  --prep_def_merge_tr_cl                  false
% 2.44/0.93  --smt_preprocessing                     true
% 2.44/0.93  --smt_ac_axioms                         fast
% 2.44/0.93  --preprocessed_out                      false
% 2.44/0.93  --preprocessed_stats                    false
% 2.44/0.93  
% 2.44/0.93  ------ Abstraction refinement Options
% 2.44/0.93  
% 2.44/0.93  --abstr_ref                             []
% 2.44/0.93  --abstr_ref_prep                        false
% 2.44/0.93  --abstr_ref_until_sat                   false
% 2.44/0.93  --abstr_ref_sig_restrict                funpre
% 2.44/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.93  --abstr_ref_under                       []
% 2.44/0.93  
% 2.44/0.93  ------ SAT Options
% 2.44/0.93  
% 2.44/0.93  --sat_mode                              false
% 2.44/0.93  --sat_fm_restart_options                ""
% 2.44/0.93  --sat_gr_def                            false
% 2.44/0.93  --sat_epr_types                         true
% 2.44/0.93  --sat_non_cyclic_types                  false
% 2.44/0.93  --sat_finite_models                     false
% 2.44/0.93  --sat_fm_lemmas                         false
% 2.44/0.93  --sat_fm_prep                           false
% 2.44/0.93  --sat_fm_uc_incr                        true
% 2.44/0.93  --sat_out_model                         small
% 2.44/0.93  --sat_out_clauses                       false
% 2.44/0.93  
% 2.44/0.93  ------ QBF Options
% 2.44/0.93  
% 2.44/0.93  --qbf_mode                              false
% 2.44/0.93  --qbf_elim_univ                         false
% 2.44/0.93  --qbf_dom_inst                          none
% 2.44/0.93  --qbf_dom_pre_inst                      false
% 2.44/0.93  --qbf_sk_in                             false
% 2.44/0.93  --qbf_pred_elim                         true
% 2.44/0.93  --qbf_split                             512
% 2.44/0.93  
% 2.44/0.93  ------ BMC1 Options
% 2.44/0.93  
% 2.44/0.93  --bmc1_incremental                      false
% 2.44/0.93  --bmc1_axioms                           reachable_all
% 2.44/0.93  --bmc1_min_bound                        0
% 2.44/0.93  --bmc1_max_bound                        -1
% 2.44/0.93  --bmc1_max_bound_default                -1
% 2.44/0.93  --bmc1_symbol_reachability              true
% 2.44/0.93  --bmc1_property_lemmas                  false
% 2.44/0.93  --bmc1_k_induction                      false
% 2.44/0.93  --bmc1_non_equiv_states                 false
% 2.44/0.93  --bmc1_deadlock                         false
% 2.44/0.93  --bmc1_ucm                              false
% 2.44/0.93  --bmc1_add_unsat_core                   none
% 2.44/0.93  --bmc1_unsat_core_children              false
% 2.44/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.93  --bmc1_out_stat                         full
% 2.44/0.93  --bmc1_ground_init                      false
% 2.44/0.93  --bmc1_pre_inst_next_state              false
% 2.44/0.93  --bmc1_pre_inst_state                   false
% 2.44/0.93  --bmc1_pre_inst_reach_state             false
% 2.44/0.93  --bmc1_out_unsat_core                   false
% 2.44/0.93  --bmc1_aig_witness_out                  false
% 2.44/0.93  --bmc1_verbose                          false
% 2.44/0.93  --bmc1_dump_clauses_tptp                false
% 2.44/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.93  --bmc1_dump_file                        -
% 2.44/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.93  --bmc1_ucm_extend_mode                  1
% 2.44/0.93  --bmc1_ucm_init_mode                    2
% 2.44/0.93  --bmc1_ucm_cone_mode                    none
% 2.44/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.93  --bmc1_ucm_relax_model                  4
% 2.44/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.93  --bmc1_ucm_layered_model                none
% 2.44/0.93  --bmc1_ucm_max_lemma_size               10
% 2.44/0.93  
% 2.44/0.93  ------ AIG Options
% 2.44/0.93  
% 2.44/0.93  --aig_mode                              false
% 2.44/0.93  
% 2.44/0.93  ------ Instantiation Options
% 2.44/0.93  
% 2.44/0.93  --instantiation_flag                    true
% 2.44/0.93  --inst_sos_flag                         false
% 2.44/0.93  --inst_sos_phase                        true
% 2.44/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.93  --inst_lit_sel_side                     num_symb
% 2.44/0.93  --inst_solver_per_active                1400
% 2.44/0.93  --inst_solver_calls_frac                1.
% 2.44/0.93  --inst_passive_queue_type               priority_queues
% 2.44/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.93  --inst_passive_queues_freq              [25;2]
% 2.44/0.93  --inst_dismatching                      true
% 2.44/0.93  --inst_eager_unprocessed_to_passive     true
% 2.44/0.93  --inst_prop_sim_given                   true
% 2.44/0.93  --inst_prop_sim_new                     false
% 2.44/0.93  --inst_subs_new                         false
% 2.44/0.93  --inst_eq_res_simp                      false
% 2.44/0.93  --inst_subs_given                       false
% 2.44/0.93  --inst_orphan_elimination               true
% 2.44/0.93  --inst_learning_loop_flag               true
% 2.44/0.93  --inst_learning_start                   3000
% 2.44/0.93  --inst_learning_factor                  2
% 2.44/0.93  --inst_start_prop_sim_after_learn       3
% 2.44/0.93  --inst_sel_renew                        solver
% 2.44/0.93  --inst_lit_activity_flag                true
% 2.44/0.93  --inst_restr_to_given                   false
% 2.44/0.93  --inst_activity_threshold               500
% 2.44/0.93  --inst_out_proof                        true
% 2.44/0.93  
% 2.44/0.93  ------ Resolution Options
% 2.44/0.93  
% 2.44/0.93  --resolution_flag                       true
% 2.44/0.93  --res_lit_sel                           adaptive
% 2.44/0.93  --res_lit_sel_side                      none
% 2.44/0.93  --res_ordering                          kbo
% 2.44/0.93  --res_to_prop_solver                    active
% 2.44/0.93  --res_prop_simpl_new                    false
% 2.44/0.93  --res_prop_simpl_given                  true
% 2.44/0.93  --res_passive_queue_type                priority_queues
% 2.44/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.93  --res_passive_queues_freq               [15;5]
% 2.44/0.93  --res_forward_subs                      full
% 2.44/0.93  --res_backward_subs                     full
% 2.44/0.93  --res_forward_subs_resolution           true
% 2.44/0.93  --res_backward_subs_resolution          true
% 2.44/0.93  --res_orphan_elimination                true
% 2.44/0.93  --res_time_limit                        2.
% 2.44/0.93  --res_out_proof                         true
% 2.44/0.93  
% 2.44/0.93  ------ Superposition Options
% 2.44/0.93  
% 2.44/0.93  --superposition_flag                    true
% 2.44/0.93  --sup_passive_queue_type                priority_queues
% 2.44/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.93  --demod_completeness_check              fast
% 2.44/0.93  --demod_use_ground                      true
% 2.44/0.93  --sup_to_prop_solver                    passive
% 2.44/0.93  --sup_prop_simpl_new                    true
% 2.44/0.93  --sup_prop_simpl_given                  true
% 2.44/0.93  --sup_fun_splitting                     false
% 2.44/0.93  --sup_smt_interval                      50000
% 2.44/0.93  
% 2.44/0.93  ------ Superposition Simplification Setup
% 2.44/0.93  
% 2.44/0.93  --sup_indices_passive                   []
% 2.44/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.93  --sup_full_bw                           [BwDemod]
% 2.44/0.93  --sup_immed_triv                        [TrivRules]
% 2.44/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.93  --sup_immed_bw_main                     []
% 2.44/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.93  
% 2.44/0.93  ------ Combination Options
% 2.44/0.93  
% 2.44/0.93  --comb_res_mult                         3
% 2.44/0.93  --comb_sup_mult                         2
% 2.44/0.93  --comb_inst_mult                        10
% 2.44/0.93  
% 2.44/0.93  ------ Debug Options
% 2.44/0.93  
% 2.44/0.93  --dbg_backtrace                         false
% 2.44/0.93  --dbg_dump_prop_clauses                 false
% 2.44/0.93  --dbg_dump_prop_clauses_file            -
% 2.44/0.93  --dbg_out_stat                          false
% 2.44/0.93  ------ Parsing...
% 2.44/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/0.93  
% 2.44/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.44/0.93  
% 2.44/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/0.93  
% 2.44/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/0.93  ------ Proving...
% 2.44/0.93  ------ Problem Properties 
% 2.44/0.93  
% 2.44/0.93  
% 2.44/0.93  clauses                                 20
% 2.44/0.93  conjectures                             5
% 2.44/0.93  EPR                                     5
% 2.44/0.93  Horn                                    15
% 2.44/0.93  unary                                   5
% 2.44/0.93  binary                                  8
% 2.44/0.93  lits                                    44
% 2.44/0.93  lits eq                                 4
% 2.44/0.93  fd_pure                                 0
% 2.44/0.93  fd_pseudo                               0
% 2.44/0.93  fd_cond                                 0
% 2.44/0.93  fd_pseudo_cond                          0
% 2.44/0.93  AC symbols                              0
% 2.44/0.93  
% 2.44/0.93  ------ Schedule dynamic 5 is on 
% 2.44/0.93  
% 2.44/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/0.93  
% 2.44/0.93  
% 2.44/0.93  ------ 
% 2.44/0.93  Current options:
% 2.44/0.93  ------ 
% 2.44/0.93  
% 2.44/0.93  ------ Input Options
% 2.44/0.93  
% 2.44/0.93  --out_options                           all
% 2.44/0.93  --tptp_safe_out                         true
% 2.44/0.93  --problem_path                          ""
% 2.44/0.93  --include_path                          ""
% 2.44/0.93  --clausifier                            res/vclausify_rel
% 2.44/0.93  --clausifier_options                    --mode clausify
% 2.44/0.93  --stdin                                 false
% 2.44/0.93  --stats_out                             all
% 2.44/0.93  
% 2.44/0.93  ------ General Options
% 2.44/0.93  
% 2.44/0.93  --fof                                   false
% 2.44/0.93  --time_out_real                         305.
% 2.44/0.93  --time_out_virtual                      -1.
% 2.44/0.93  --symbol_type_check                     false
% 2.44/0.93  --clausify_out                          false
% 2.44/0.93  --sig_cnt_out                           false
% 2.44/0.93  --trig_cnt_out                          false
% 2.44/0.93  --trig_cnt_out_tolerance                1.
% 2.44/0.93  --trig_cnt_out_sk_spl                   false
% 2.44/0.93  --abstr_cl_out                          false
% 2.44/0.93  
% 2.44/0.93  ------ Global Options
% 2.44/0.93  
% 2.44/0.93  --schedule                              default
% 2.44/0.93  --add_important_lit                     false
% 2.44/0.93  --prop_solver_per_cl                    1000
% 2.44/0.93  --min_unsat_core                        false
% 2.44/0.93  --soft_assumptions                      false
% 2.44/0.93  --soft_lemma_size                       3
% 2.44/0.93  --prop_impl_unit_size                   0
% 2.44/0.93  --prop_impl_unit                        []
% 2.44/0.93  --share_sel_clauses                     true
% 2.44/0.93  --reset_solvers                         false
% 2.44/0.93  --bc_imp_inh                            [conj_cone]
% 2.44/0.93  --conj_cone_tolerance                   3.
% 2.44/0.93  --extra_neg_conj                        none
% 2.44/0.93  --large_theory_mode                     true
% 2.44/0.93  --prolific_symb_bound                   200
% 2.44/0.93  --lt_threshold                          2000
% 2.44/0.93  --clause_weak_htbl                      true
% 2.44/0.93  --gc_record_bc_elim                     false
% 2.44/0.93  
% 2.44/0.93  ------ Preprocessing Options
% 2.44/0.93  
% 2.44/0.93  --preprocessing_flag                    true
% 2.44/0.93  --time_out_prep_mult                    0.1
% 2.44/0.93  --splitting_mode                        input
% 2.44/0.93  --splitting_grd                         true
% 2.44/0.93  --splitting_cvd                         false
% 2.44/0.93  --splitting_cvd_svl                     false
% 2.44/0.93  --splitting_nvd                         32
% 2.44/0.93  --sub_typing                            true
% 2.44/0.93  --prep_gs_sim                           true
% 2.44/0.93  --prep_unflatten                        true
% 2.44/0.93  --prep_res_sim                          true
% 2.44/0.93  --prep_upred                            true
% 2.44/0.93  --prep_sem_filter                       exhaustive
% 2.44/0.93  --prep_sem_filter_out                   false
% 2.44/0.93  --pred_elim                             true
% 2.44/0.93  --res_sim_input                         true
% 2.44/0.93  --eq_ax_congr_red                       true
% 2.44/0.93  --pure_diseq_elim                       true
% 2.44/0.93  --brand_transform                       false
% 2.44/0.93  --non_eq_to_eq                          false
% 2.44/0.93  --prep_def_merge                        true
% 2.44/0.93  --prep_def_merge_prop_impl              false
% 2.44/0.93  --prep_def_merge_mbd                    true
% 2.44/0.93  --prep_def_merge_tr_red                 false
% 2.44/0.93  --prep_def_merge_tr_cl                  false
% 2.44/0.93  --smt_preprocessing                     true
% 2.44/0.93  --smt_ac_axioms                         fast
% 2.44/0.93  --preprocessed_out                      false
% 2.44/0.93  --preprocessed_stats                    false
% 2.44/0.93  
% 2.44/0.93  ------ Abstraction refinement Options
% 2.44/0.93  
% 2.44/0.93  --abstr_ref                             []
% 2.44/0.93  --abstr_ref_prep                        false
% 2.44/0.93  --abstr_ref_until_sat                   false
% 2.44/0.93  --abstr_ref_sig_restrict                funpre
% 2.44/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.93  --abstr_ref_under                       []
% 2.44/0.93  
% 2.44/0.93  ------ SAT Options
% 2.44/0.93  
% 2.44/0.93  --sat_mode                              false
% 2.44/0.93  --sat_fm_restart_options                ""
% 2.44/0.93  --sat_gr_def                            false
% 2.44/0.93  --sat_epr_types                         true
% 2.44/0.93  --sat_non_cyclic_types                  false
% 2.44/0.93  --sat_finite_models                     false
% 2.44/0.93  --sat_fm_lemmas                         false
% 2.44/0.93  --sat_fm_prep                           false
% 2.44/0.93  --sat_fm_uc_incr                        true
% 2.44/0.93  --sat_out_model                         small
% 2.44/0.93  --sat_out_clauses                       false
% 2.44/0.93  
% 2.44/0.93  ------ QBF Options
% 2.44/0.93  
% 2.44/0.93  --qbf_mode                              false
% 2.44/0.93  --qbf_elim_univ                         false
% 2.44/0.93  --qbf_dom_inst                          none
% 2.44/0.93  --qbf_dom_pre_inst                      false
% 2.44/0.93  --qbf_sk_in                             false
% 2.44/0.93  --qbf_pred_elim                         true
% 2.44/0.93  --qbf_split                             512
% 2.44/0.93  
% 2.44/0.93  ------ BMC1 Options
% 2.44/0.93  
% 2.44/0.93  --bmc1_incremental                      false
% 2.44/0.93  --bmc1_axioms                           reachable_all
% 2.44/0.93  --bmc1_min_bound                        0
% 2.44/0.93  --bmc1_max_bound                        -1
% 2.44/0.93  --bmc1_max_bound_default                -1
% 2.44/0.93  --bmc1_symbol_reachability              true
% 2.44/0.93  --bmc1_property_lemmas                  false
% 2.44/0.93  --bmc1_k_induction                      false
% 2.44/0.93  --bmc1_non_equiv_states                 false
% 2.44/0.93  --bmc1_deadlock                         false
% 2.44/0.93  --bmc1_ucm                              false
% 2.44/0.93  --bmc1_add_unsat_core                   none
% 2.44/0.93  --bmc1_unsat_core_children              false
% 2.44/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/0.93  --bmc1_out_stat                         full
% 2.44/0.93  --bmc1_ground_init                      false
% 2.44/0.93  --bmc1_pre_inst_next_state              false
% 2.44/0.93  --bmc1_pre_inst_state                   false
% 2.44/0.93  --bmc1_pre_inst_reach_state             false
% 2.44/0.93  --bmc1_out_unsat_core                   false
% 2.44/0.93  --bmc1_aig_witness_out                  false
% 2.44/0.93  --bmc1_verbose                          false
% 2.44/0.93  --bmc1_dump_clauses_tptp                false
% 2.44/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.44/0.93  --bmc1_dump_file                        -
% 2.44/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.44/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.44/0.93  --bmc1_ucm_extend_mode                  1
% 2.44/0.93  --bmc1_ucm_init_mode                    2
% 2.44/0.93  --bmc1_ucm_cone_mode                    none
% 2.44/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.44/0.93  --bmc1_ucm_relax_model                  4
% 2.44/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.44/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/0.93  --bmc1_ucm_layered_model                none
% 2.44/0.93  --bmc1_ucm_max_lemma_size               10
% 2.44/0.93  
% 2.44/0.93  ------ AIG Options
% 2.44/0.93  
% 2.44/0.93  --aig_mode                              false
% 2.44/0.93  
% 2.44/0.93  ------ Instantiation Options
% 2.44/0.93  
% 2.44/0.93  --instantiation_flag                    true
% 2.44/0.93  --inst_sos_flag                         false
% 2.44/0.93  --inst_sos_phase                        true
% 2.44/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/0.93  --inst_lit_sel_side                     none
% 2.44/0.93  --inst_solver_per_active                1400
% 2.44/0.93  --inst_solver_calls_frac                1.
% 2.44/0.93  --inst_passive_queue_type               priority_queues
% 2.44/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/0.94  --inst_passive_queues_freq              [25;2]
% 2.44/0.94  --inst_dismatching                      true
% 2.44/0.94  --inst_eager_unprocessed_to_passive     true
% 2.44/0.94  --inst_prop_sim_given                   true
% 2.44/0.94  --inst_prop_sim_new                     false
% 2.44/0.94  --inst_subs_new                         false
% 2.44/0.94  --inst_eq_res_simp                      false
% 2.44/0.94  --inst_subs_given                       false
% 2.44/0.94  --inst_orphan_elimination               true
% 2.44/0.94  --inst_learning_loop_flag               true
% 2.44/0.94  --inst_learning_start                   3000
% 2.44/0.94  --inst_learning_factor                  2
% 2.44/0.94  --inst_start_prop_sim_after_learn       3
% 2.44/0.94  --inst_sel_renew                        solver
% 2.44/0.94  --inst_lit_activity_flag                true
% 2.44/0.94  --inst_restr_to_given                   false
% 2.44/0.94  --inst_activity_threshold               500
% 2.44/0.94  --inst_out_proof                        true
% 2.44/0.94  
% 2.44/0.94  ------ Resolution Options
% 2.44/0.94  
% 2.44/0.94  --resolution_flag                       false
% 2.44/0.94  --res_lit_sel                           adaptive
% 2.44/0.94  --res_lit_sel_side                      none
% 2.44/0.94  --res_ordering                          kbo
% 2.44/0.94  --res_to_prop_solver                    active
% 2.44/0.94  --res_prop_simpl_new                    false
% 2.44/0.94  --res_prop_simpl_given                  true
% 2.44/0.94  --res_passive_queue_type                priority_queues
% 2.44/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/0.94  --res_passive_queues_freq               [15;5]
% 2.44/0.94  --res_forward_subs                      full
% 2.44/0.94  --res_backward_subs                     full
% 2.44/0.94  --res_forward_subs_resolution           true
% 2.44/0.94  --res_backward_subs_resolution          true
% 2.44/0.94  --res_orphan_elimination                true
% 2.44/0.94  --res_time_limit                        2.
% 2.44/0.94  --res_out_proof                         true
% 2.44/0.94  
% 2.44/0.94  ------ Superposition Options
% 2.44/0.94  
% 2.44/0.94  --superposition_flag                    true
% 2.44/0.94  --sup_passive_queue_type                priority_queues
% 2.44/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.44/0.94  --demod_completeness_check              fast
% 2.44/0.94  --demod_use_ground                      true
% 2.44/0.94  --sup_to_prop_solver                    passive
% 2.44/0.94  --sup_prop_simpl_new                    true
% 2.44/0.94  --sup_prop_simpl_given                  true
% 2.44/0.94  --sup_fun_splitting                     false
% 2.44/0.94  --sup_smt_interval                      50000
% 2.44/0.94  
% 2.44/0.94  ------ Superposition Simplification Setup
% 2.44/0.94  
% 2.44/0.94  --sup_indices_passive                   []
% 2.44/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.94  --sup_full_bw                           [BwDemod]
% 2.44/0.94  --sup_immed_triv                        [TrivRules]
% 2.44/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.94  --sup_immed_bw_main                     []
% 2.44/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/0.94  
% 2.44/0.94  ------ Combination Options
% 2.44/0.94  
% 2.44/0.94  --comb_res_mult                         3
% 2.44/0.94  --comb_sup_mult                         2
% 2.44/0.94  --comb_inst_mult                        10
% 2.44/0.94  
% 2.44/0.94  ------ Debug Options
% 2.44/0.94  
% 2.44/0.94  --dbg_backtrace                         false
% 2.44/0.94  --dbg_dump_prop_clauses                 false
% 2.44/0.94  --dbg_dump_prop_clauses_file            -
% 2.44/0.94  --dbg_out_stat                          false
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  ------ Proving...
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  % SZS status Theorem for theBenchmark.p
% 2.44/0.94  
% 2.44/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/0.94  
% 2.44/0.94  fof(f10,conjecture,(
% 2.44/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f11,negated_conjecture,(
% 2.44/0.94    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.44/0.94    inference(negated_conjecture,[],[f10])).
% 2.44/0.94  
% 2.44/0.94  fof(f18,plain,(
% 2.44/0.94    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/0.94    inference(ennf_transformation,[],[f11])).
% 2.44/0.94  
% 2.44/0.94  fof(f19,plain,(
% 2.44/0.94    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/0.94    inference(flattening,[],[f18])).
% 2.44/0.94  
% 2.44/0.94  fof(f36,plain,(
% 2.44/0.94    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f35,plain,(
% 2.44/0.94    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f34,plain,(
% 2.44/0.94    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f37,plain,(
% 2.44/0.94    ((k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f36,f35,f34])).
% 2.44/0.94  
% 2.44/0.94  fof(f61,plain,(
% 2.44/0.94    r2_hidden(sK5,sK4)),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f5,axiom,(
% 2.44/0.94    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f28,plain,(
% 2.44/0.94    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.44/0.94    inference(nnf_transformation,[],[f5])).
% 2.44/0.94  
% 2.44/0.94  fof(f46,plain,(
% 2.44/0.94    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f28])).
% 2.44/0.94  
% 2.44/0.94  fof(f3,axiom,(
% 2.44/0.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f43,plain,(
% 2.44/0.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f3])).
% 2.44/0.94  
% 2.44/0.94  fof(f4,axiom,(
% 2.44/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f44,plain,(
% 2.44/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f4])).
% 2.44/0.94  
% 2.44/0.94  fof(f63,plain,(
% 2.44/0.94    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.44/0.94    inference(definition_unfolding,[],[f43,f44])).
% 2.44/0.94  
% 2.44/0.94  fof(f64,plain,(
% 2.44/0.94    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.94    inference(definition_unfolding,[],[f46,f63])).
% 2.44/0.94  
% 2.44/0.94  fof(f58,plain,(
% 2.44/0.94    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f7,axiom,(
% 2.44/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f29,plain,(
% 2.44/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.44/0.94    inference(nnf_transformation,[],[f7])).
% 2.44/0.94  
% 2.44/0.94  fof(f49,plain,(
% 2.44/0.94    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f29])).
% 2.44/0.94  
% 2.44/0.94  fof(f9,axiom,(
% 2.44/0.94    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f16,plain,(
% 2.44/0.94    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/0.94    inference(ennf_transformation,[],[f9])).
% 2.44/0.94  
% 2.44/0.94  fof(f17,plain,(
% 2.44/0.94    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.94    inference(flattening,[],[f16])).
% 2.44/0.94  
% 2.44/0.94  fof(f30,plain,(
% 2.44/0.94    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.94    inference(nnf_transformation,[],[f17])).
% 2.44/0.94  
% 2.44/0.94  fof(f31,plain,(
% 2.44/0.94    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.94    inference(rectify,[],[f30])).
% 2.44/0.94  
% 2.44/0.94  fof(f32,plain,(
% 2.44/0.94    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f33,plain,(
% 2.44/0.94    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f32])).
% 2.44/0.94  
% 2.44/0.94  fof(f51,plain,(
% 2.44/0.94    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f33])).
% 2.44/0.94  
% 2.44/0.94  fof(f57,plain,(
% 2.44/0.94    l1_pre_topc(sK3)),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f55,plain,(
% 2.44/0.94    ~v2_struct_0(sK3)),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f56,plain,(
% 2.44/0.94    v2_pre_topc(sK3)),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f59,plain,(
% 2.44/0.94    v2_tex_2(sK4,sK3)),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f48,plain,(
% 2.44/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/0.94    inference(cnf_transformation,[],[f29])).
% 2.44/0.94  
% 2.44/0.94  fof(f2,axiom,(
% 2.44/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f12,plain,(
% 2.44/0.94    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/0.94    inference(ennf_transformation,[],[f2])).
% 2.44/0.94  
% 2.44/0.94  fof(f24,plain,(
% 2.44/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.94    inference(nnf_transformation,[],[f12])).
% 2.44/0.94  
% 2.44/0.94  fof(f25,plain,(
% 2.44/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.94    inference(rectify,[],[f24])).
% 2.44/0.94  
% 2.44/0.94  fof(f26,plain,(
% 2.44/0.94    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f27,plain,(
% 2.44/0.94    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f25,f26])).
% 2.44/0.94  
% 2.44/0.94  fof(f40,plain,(
% 2.44/0.94    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f27])).
% 2.44/0.94  
% 2.44/0.94  fof(f60,plain,(
% 2.44/0.94    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  fof(f8,axiom,(
% 2.44/0.94    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f14,plain,(
% 2.44/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.44/0.94    inference(ennf_transformation,[],[f8])).
% 2.44/0.94  
% 2.44/0.94  fof(f15,plain,(
% 2.44/0.94    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.44/0.94    inference(flattening,[],[f14])).
% 2.44/0.94  
% 2.44/0.94  fof(f50,plain,(
% 2.44/0.94    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f15])).
% 2.44/0.94  
% 2.44/0.94  fof(f66,plain,(
% 2.44/0.94    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/0.94    inference(definition_unfolding,[],[f50,f63])).
% 2.44/0.94  
% 2.44/0.94  fof(f1,axiom,(
% 2.44/0.94    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.44/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/0.94  
% 2.44/0.94  fof(f20,plain,(
% 2.44/0.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.44/0.94    inference(nnf_transformation,[],[f1])).
% 2.44/0.94  
% 2.44/0.94  fof(f21,plain,(
% 2.44/0.94    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.44/0.94    inference(rectify,[],[f20])).
% 2.44/0.94  
% 2.44/0.94  fof(f22,plain,(
% 2.44/0.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.44/0.94    introduced(choice_axiom,[])).
% 2.44/0.94  
% 2.44/0.94  fof(f23,plain,(
% 2.44/0.94    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.44/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.44/0.94  
% 2.44/0.94  fof(f38,plain,(
% 2.44/0.94    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.44/0.94    inference(cnf_transformation,[],[f23])).
% 2.44/0.94  
% 2.44/0.94  fof(f62,plain,(
% 2.44/0.94    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 2.44/0.94    inference(cnf_transformation,[],[f37])).
% 2.44/0.94  
% 2.44/0.94  cnf(c_16,negated_conjecture,
% 2.44/0.94      ( r2_hidden(sK5,sK4) ),
% 2.44/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1978,plain,
% 2.44/0.94      ( r2_hidden(sK5,sK4) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_5,plain,
% 2.44/0.94      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~ r2_hidden(X0,X1) ),
% 2.44/0.94      inference(cnf_transformation,[],[f64]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1983,plain,
% 2.44/0.94      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) = iProver_top
% 2.44/0.94      | r2_hidden(X0,X1) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_19,negated_conjecture,
% 2.44/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/0.94      inference(cnf_transformation,[],[f58]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1975,plain,
% 2.44/0.94      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_8,plain,
% 2.44/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.44/0.94      inference(cnf_transformation,[],[f49]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1981,plain,
% 2.44/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.44/0.94      | r1_tarski(X0,X1) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_14,plain,
% 2.44/0.94      ( ~ v2_tex_2(X0,X1)
% 2.44/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.94      | ~ r1_tarski(X2,X0)
% 2.44/0.94      | v2_struct_0(X1)
% 2.44/0.94      | ~ v2_pre_topc(X1)
% 2.44/0.94      | ~ l1_pre_topc(X1)
% 2.44/0.94      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.44/0.94      inference(cnf_transformation,[],[f51]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_20,negated_conjecture,
% 2.44/0.94      ( l1_pre_topc(sK3) ),
% 2.44/0.94      inference(cnf_transformation,[],[f57]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_299,plain,
% 2.44/0.94      ( ~ v2_tex_2(X0,X1)
% 2.44/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.94      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/0.94      | ~ r1_tarski(X2,X0)
% 2.44/0.94      | v2_struct_0(X1)
% 2.44/0.94      | ~ v2_pre_topc(X1)
% 2.44/0.94      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.44/0.94      | sK3 != X1 ),
% 2.44/0.94      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_300,plain,
% 2.44/0.94      ( ~ v2_tex_2(X0,sK3)
% 2.44/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ r1_tarski(X1,X0)
% 2.44/0.94      | v2_struct_0(sK3)
% 2.44/0.94      | ~ v2_pre_topc(sK3)
% 2.44/0.94      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/0.94      inference(unflattening,[status(thm)],[c_299]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_22,negated_conjecture,
% 2.44/0.94      ( ~ v2_struct_0(sK3) ),
% 2.44/0.94      inference(cnf_transformation,[],[f55]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_21,negated_conjecture,
% 2.44/0.94      ( v2_pre_topc(sK3) ),
% 2.44/0.94      inference(cnf_transformation,[],[f56]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_304,plain,
% 2.44/0.94      ( ~ v2_tex_2(X0,sK3)
% 2.44/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ r1_tarski(X1,X0)
% 2.44/0.94      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/0.94      inference(global_propositional_subsumption,
% 2.44/0.94                [status(thm)],
% 2.44/0.94                [c_300,c_22,c_21]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_305,plain,
% 2.44/0.94      ( ~ v2_tex_2(X0,sK3)
% 2.44/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/0.94      | ~ r1_tarski(X1,X0)
% 2.44/0.94      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/0.94      inference(renaming,[status(thm)],[c_304]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1973,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.44/0.94      | v2_tex_2(X0,sK3) != iProver_top
% 2.44/0.94      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/0.94      | r1_tarski(X1,X0) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_305]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2488,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.44/0.94      | v2_tex_2(X0,sK3) != iProver_top
% 2.44/0.94      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/0.94      | r1_tarski(X1,X0) != iProver_top
% 2.44/0.94      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1981,c_1973]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2910,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 2.44/0.94      | v2_tex_2(sK4,sK3) != iProver_top
% 2.44/0.94      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/0.94      | r1_tarski(X0,sK4) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1975,c_2488]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_18,negated_conjecture,
% 2.44/0.94      ( v2_tex_2(sK4,sK3) ),
% 2.44/0.94      inference(cnf_transformation,[],[f59]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_27,plain,
% 2.44/0.94      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2952,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 2.44/0.94      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/0.94      | r1_tarski(X0,sK4) != iProver_top ),
% 2.44/0.94      inference(global_propositional_subsumption,
% 2.44/0.94                [status(thm)],
% 2.44/0.94                [c_2910,c_27]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3142,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 2.44/0.94      | r1_tarski(k2_enumset1(X0,X0,X0,X0),sK4) != iProver_top
% 2.44/0.94      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1983,c_2952]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3206,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 2.44/0.94      | r2_hidden(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/0.94      | r2_hidden(X0,sK4) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1983,c_3142]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_9,plain,
% 2.44/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.44/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1980,plain,
% 2.44/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.44/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2423,plain,
% 2.44/0.94      ( r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1975,c_1980]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4,plain,
% 2.44/0.94      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.44/0.94      inference(cnf_transformation,[],[f40]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1984,plain,
% 2.44/0.94      ( r1_tarski(X0,X1) != iProver_top
% 2.44/0.94      | r2_hidden(X2,X0) != iProver_top
% 2.44/0.94      | r2_hidden(X2,X1) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3391,plain,
% 2.44/0.94      ( r2_hidden(X0,u1_struct_0(sK3)) = iProver_top
% 2.44/0.94      | r2_hidden(X0,sK4) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_2423,c_1984]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_5440,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(X0,X0,X0,X0))) = k2_enumset1(X0,X0,X0,X0)
% 2.44/0.94      | r2_hidden(X0,sK4) != iProver_top ),
% 2.44/0.94      inference(global_propositional_subsumption,
% 2.44/0.94                [status(thm)],
% 2.44/0.94                [c_3206,c_3391]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_5450,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k2_enumset1(sK5,sK5,sK5,sK5))) = k2_enumset1(sK5,sK5,sK5,sK5) ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1978,c_5440]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_17,negated_conjecture,
% 2.44/0.94      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.44/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1977,plain,
% 2.44/0.94      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_10,plain,
% 2.44/0.94      ( ~ m1_subset_1(X0,X1)
% 2.44/0.94      | v1_xboole_0(X1)
% 2.44/0.94      | k2_enumset1(X0,X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.44/0.94      inference(cnf_transformation,[],[f66]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1979,plain,
% 2.44/0.94      ( k2_enumset1(X0,X0,X0,X0) = k6_domain_1(X1,X0)
% 2.44/0.94      | m1_subset_1(X0,X1) != iProver_top
% 2.44/0.94      | v1_xboole_0(X1) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3017,plain,
% 2.44/0.94      ( k2_enumset1(sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5)
% 2.44/0.94      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_1977,c_1979]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1,plain,
% 2.44/0.94      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.44/0.94      inference(cnf_transformation,[],[f38]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1987,plain,
% 2.44/0.94      ( r2_hidden(X0,X1) != iProver_top
% 2.44/0.94      | v1_xboole_0(X1) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3743,plain,
% 2.44/0.94      ( r2_hidden(X0,sK4) != iProver_top
% 2.44/0.94      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_3391,c_1987]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_29,plain,
% 2.44/0.94      ( r2_hidden(sK5,sK4) = iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_3553,plain,
% 2.44/0.94      ( ~ r1_tarski(sK4,X0) | r2_hidden(sK5,X0) | ~ r2_hidden(sK5,sK4) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_4]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4238,plain,
% 2.44/0.94      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.44/0.94      | r2_hidden(sK5,u1_struct_0(sK3))
% 2.44/0.94      | ~ r2_hidden(sK5,sK4) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_3553]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4241,plain,
% 2.44/0.94      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 2.44/0.94      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 2.44/0.94      | r2_hidden(sK5,sK4) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_4238]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2171,plain,
% 2.44/0.94      ( ~ r2_hidden(X0,u1_struct_0(sK3))
% 2.44/0.94      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_1]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4240,plain,
% 2.44/0.94      ( ~ r2_hidden(sK5,u1_struct_0(sK3))
% 2.44/0.94      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_2171]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4243,plain,
% 2.44/0.94      ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 2.44/0.94      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.44/0.94      inference(predicate_to_equality,[status(thm)],[c_4240]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4279,plain,
% 2.44/0.94      ( v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 2.44/0.94      inference(global_propositional_subsumption,
% 2.44/0.94                [status(thm)],
% 2.44/0.94                [c_3743,c_29,c_2423,c_4241,c_4243]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_4284,plain,
% 2.44/0.94      ( k2_enumset1(sK5,sK5,sK5,sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/0.94      inference(superposition,[status(thm)],[c_3017,c_4279]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_5457,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/0.94      inference(light_normalisation,[status(thm)],[c_5450,c_4284]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1485,plain,( X0 = X0 ),theory(equality) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2181,plain,
% 2.44/0.94      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_1485]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_1486,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2133,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
% 2.44/0.94      | k6_domain_1(u1_struct_0(sK3),sK5) != X0
% 2.44/0.94      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_1486]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_2180,plain,
% 2.44/0.94      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
% 2.44/0.94      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
% 2.44/0.94      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/0.94      inference(instantiation,[status(thm)],[c_2133]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(c_15,negated_conjecture,
% 2.44/0.94      ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.44/0.94      inference(cnf_transformation,[],[f62]) ).
% 2.44/0.94  
% 2.44/0.94  cnf(contradiction,plain,
% 2.44/0.94      ( $false ),
% 2.44/0.94      inference(minisat,[status(thm)],[c_5457,c_2181,c_2180,c_15]) ).
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/0.94  
% 2.44/0.94  ------                               Statistics
% 2.44/0.94  
% 2.44/0.94  ------ General
% 2.44/0.94  
% 2.44/0.94  abstr_ref_over_cycles:                  0
% 2.44/0.94  abstr_ref_under_cycles:                 0
% 2.44/0.94  gc_basic_clause_elim:                   0
% 2.44/0.94  forced_gc_time:                         0
% 2.44/0.94  parsing_time:                           0.008
% 2.44/0.94  unif_index_cands_time:                  0.
% 2.44/0.94  unif_index_add_time:                    0.
% 2.44/0.94  orderings_time:                         0.
% 2.44/0.94  out_proof_time:                         0.014
% 2.44/0.94  total_time:                             0.205
% 2.44/0.94  num_of_symbols:                         51
% 2.44/0.94  num_of_terms:                           3163
% 2.44/0.94  
% 2.44/0.94  ------ Preprocessing
% 2.44/0.94  
% 2.44/0.94  num_of_splits:                          0
% 2.44/0.94  num_of_split_atoms:                     0
% 2.44/0.94  num_of_reused_defs:                     0
% 2.44/0.94  num_eq_ax_congr_red:                    31
% 2.44/0.94  num_of_sem_filtered_clauses:            1
% 2.44/0.94  num_of_subtypes:                        0
% 2.44/0.94  monotx_restored_types:                  0
% 2.44/0.94  sat_num_of_epr_types:                   0
% 2.44/0.94  sat_num_of_non_cyclic_types:            0
% 2.44/0.94  sat_guarded_non_collapsed_types:        0
% 2.44/0.94  num_pure_diseq_elim:                    0
% 2.44/0.94  simp_replaced_by:                       0
% 2.44/0.94  res_preprocessed:                       108
% 2.44/0.94  prep_upred:                             0
% 2.44/0.94  prep_unflattend:                        64
% 2.44/0.94  smt_new_axioms:                         0
% 2.44/0.94  pred_elim_cands:                        5
% 2.44/0.94  pred_elim:                              3
% 2.44/0.94  pred_elim_cl:                           3
% 2.44/0.94  pred_elim_cycles:                       7
% 2.44/0.94  merged_defs:                            16
% 2.44/0.94  merged_defs_ncl:                        0
% 2.44/0.94  bin_hyper_res:                          17
% 2.44/0.94  prep_cycles:                            4
% 2.44/0.94  pred_elim_time:                         0.019
% 2.44/0.94  splitting_time:                         0.
% 2.44/0.94  sem_filter_time:                        0.
% 2.44/0.94  monotx_time:                            0.001
% 2.44/0.94  subtype_inf_time:                       0.
% 2.44/0.94  
% 2.44/0.94  ------ Problem properties
% 2.44/0.94  
% 2.44/0.94  clauses:                                20
% 2.44/0.94  conjectures:                            5
% 2.44/0.94  epr:                                    5
% 2.44/0.94  horn:                                   15
% 2.44/0.94  ground:                                 5
% 2.44/0.94  unary:                                  5
% 2.44/0.94  binary:                                 8
% 2.44/0.94  lits:                                   44
% 2.44/0.94  lits_eq:                                4
% 2.44/0.94  fd_pure:                                0
% 2.44/0.94  fd_pseudo:                              0
% 2.44/0.94  fd_cond:                                0
% 2.44/0.94  fd_pseudo_cond:                         0
% 2.44/0.94  ac_symbols:                             0
% 2.44/0.94  
% 2.44/0.94  ------ Propositional Solver
% 2.44/0.94  
% 2.44/0.94  prop_solver_calls:                      29
% 2.44/0.94  prop_fast_solver_calls:                 953
% 2.44/0.94  smt_solver_calls:                       0
% 2.44/0.94  smt_fast_solver_calls:                  0
% 2.44/0.94  prop_num_of_clauses:                    1520
% 2.44/0.94  prop_preprocess_simplified:             4785
% 2.44/0.94  prop_fo_subsumed:                       20
% 2.44/0.94  prop_solver_time:                       0.
% 2.44/0.94  smt_solver_time:                        0.
% 2.44/0.94  smt_fast_solver_time:                   0.
% 2.44/0.94  prop_fast_solver_time:                  0.
% 2.44/0.94  prop_unsat_core_time:                   0.
% 2.44/0.94  
% 2.44/0.94  ------ QBF
% 2.44/0.94  
% 2.44/0.94  qbf_q_res:                              0
% 2.44/0.94  qbf_num_tautologies:                    0
% 2.44/0.94  qbf_prep_cycles:                        0
% 2.44/0.94  
% 2.44/0.94  ------ BMC1
% 2.44/0.94  
% 2.44/0.94  bmc1_current_bound:                     -1
% 2.44/0.94  bmc1_last_solved_bound:                 -1
% 2.44/0.94  bmc1_unsat_core_size:                   -1
% 2.44/0.94  bmc1_unsat_core_parents_size:           -1
% 2.44/0.94  bmc1_merge_next_fun:                    0
% 2.44/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.44/0.94  
% 2.44/0.94  ------ Instantiation
% 2.44/0.94  
% 2.44/0.94  inst_num_of_clauses:                    408
% 2.44/0.94  inst_num_in_passive:                    27
% 2.44/0.94  inst_num_in_active:                     256
% 2.44/0.94  inst_num_in_unprocessed:                125
% 2.44/0.94  inst_num_of_loops:                      340
% 2.44/0.94  inst_num_of_learning_restarts:          0
% 2.44/0.94  inst_num_moves_active_passive:          80
% 2.44/0.94  inst_lit_activity:                      0
% 2.44/0.94  inst_lit_activity_moves:                0
% 2.44/0.94  inst_num_tautologies:                   0
% 2.44/0.94  inst_num_prop_implied:                  0
% 2.44/0.94  inst_num_existing_simplified:           0
% 2.44/0.94  inst_num_eq_res_simplified:             0
% 2.44/0.94  inst_num_child_elim:                    0
% 2.44/0.94  inst_num_of_dismatching_blockings:      184
% 2.44/0.94  inst_num_of_non_proper_insts:           525
% 2.44/0.94  inst_num_of_duplicates:                 0
% 2.44/0.94  inst_inst_num_from_inst_to_res:         0
% 2.44/0.94  inst_dismatching_checking_time:         0.
% 2.44/0.94  
% 2.44/0.94  ------ Resolution
% 2.44/0.94  
% 2.44/0.94  res_num_of_clauses:                     0
% 2.44/0.94  res_num_in_passive:                     0
% 2.44/0.94  res_num_in_active:                      0
% 2.44/0.94  res_num_of_loops:                       112
% 2.44/0.94  res_forward_subset_subsumed:            43
% 2.44/0.94  res_backward_subset_subsumed:           0
% 2.44/0.94  res_forward_subsumed:                   2
% 2.44/0.94  res_backward_subsumed:                  0
% 2.44/0.94  res_forward_subsumption_resolution:     0
% 2.44/0.94  res_backward_subsumption_resolution:    0
% 2.44/0.94  res_clause_to_clause_subsumption:       482
% 2.44/0.94  res_orphan_elimination:                 0
% 2.44/0.94  res_tautology_del:                      82
% 2.44/0.94  res_num_eq_res_simplified:              0
% 2.44/0.94  res_num_sel_changes:                    0
% 2.44/0.94  res_moves_from_active_to_pass:          0
% 2.44/0.94  
% 2.44/0.94  ------ Superposition
% 2.44/0.94  
% 2.44/0.94  sup_time_total:                         0.
% 2.44/0.94  sup_time_generating:                    0.
% 2.44/0.94  sup_time_sim_full:                      0.
% 2.44/0.94  sup_time_sim_immed:                     0.
% 2.44/0.94  
% 2.44/0.94  sup_num_of_clauses:                     102
% 2.44/0.94  sup_num_in_active:                      66
% 2.44/0.94  sup_num_in_passive:                     36
% 2.44/0.94  sup_num_of_loops:                       67
% 2.44/0.94  sup_fw_superposition:                   81
% 2.44/0.94  sup_bw_superposition:                   47
% 2.44/0.94  sup_immediate_simplified:               20
% 2.44/0.94  sup_given_eliminated:                   0
% 2.44/0.94  comparisons_done:                       0
% 2.44/0.94  comparisons_avoided:                    0
% 2.44/0.94  
% 2.44/0.94  ------ Simplifications
% 2.44/0.94  
% 2.44/0.94  
% 2.44/0.94  sim_fw_subset_subsumed:                 13
% 2.44/0.94  sim_bw_subset_subsumed:                 3
% 2.44/0.94  sim_fw_subsumed:                        3
% 2.44/0.94  sim_bw_subsumed:                        1
% 2.44/0.94  sim_fw_subsumption_res:                 1
% 2.44/0.94  sim_bw_subsumption_res:                 0
% 2.44/0.94  sim_tautology_del:                      11
% 2.44/0.94  sim_eq_tautology_del:                   0
% 2.44/0.94  sim_eq_res_simp:                        0
% 2.44/0.94  sim_fw_demodulated:                     0
% 2.44/0.94  sim_bw_demodulated:                     0
% 2.44/0.94  sim_light_normalised:                   2
% 2.44/0.94  sim_joinable_taut:                      0
% 2.44/0.94  sim_joinable_simp:                      0
% 2.44/0.94  sim_ac_normalised:                      0
% 2.44/0.94  sim_smt_subsumption:                    0
% 2.44/0.94  
%------------------------------------------------------------------------------
