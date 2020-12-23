%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:27 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 314 expanded)
%              Number of clauses        :   68 (  99 expanded)
%              Number of leaves         :   18 (  88 expanded)
%              Depth                    :   17
%              Number of atoms          :  403 (1515 expanded)
%              Number of equality atoms :  123 ( 303 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)))
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
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

fof(f42,plain,
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

fof(f45,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f44,f43,f42])).

fof(f72,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f75])).

fof(f70,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

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

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f75])).

fof(f13,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f69,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f68,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f74,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2062,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2064,plain,
    ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3055,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_enumset1(sK5,sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2062,c_2064])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_30,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_727,plain,
    ( ~ v1_xboole_0(X0)
    | sK4 != X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_20])).

cnf(c_728,plain,
    ( ~ v1_xboole_0(sK4) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_729,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2254,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r1_tarski(sK4,u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2255,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2254])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_207,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_11])).

cnf(c_208,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_207])).

cnf(c_256,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_208])).

cnf(c_2315,plain,
    ( ~ r1_tarski(sK4,X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_256])).

cnf(c_2556,plain,
    ( ~ r1_tarski(sK4,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2315])).

cnf(c_2557,plain,
    ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2556])).

cnf(c_3355,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_enumset1(sK5,sK5,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3055,c_30,c_729,c_2255,c_2557])).

cnf(c_8,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2069,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3894,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(X0)) = iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_2069])).

cnf(c_2066,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4479,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),X0) = iProver_top
    | r2_hidden(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3894,c_2066])).

cnf(c_2060,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2067,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_18,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_353,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_354,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_25,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_358,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_26,c_25])).

cnf(c_359,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_358])).

cnf(c_2058,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_359])).

cnf(c_3170,plain,
    ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
    | v2_tex_2(X0,sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2067,c_2058])).

cnf(c_3476,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | v2_tex_2(sK4,sK3) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2060,c_3170])).

cnf(c_22,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_31,plain,
    ( v2_tex_2(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3589,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
    | r1_tarski(X0,sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3476,c_31])).

cnf(c_4928,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3589])).

cnf(c_1486,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2496,plain,
    ( r1_tarski(X0,X1)
    | ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
    | X0 != k1_enumset1(sK5,sK5,sK5)
    | X1 != sK4 ),
    inference(instantiation,[status(thm)],[c_1486])).

cnf(c_3382,plain,
    ( r1_tarski(X0,sK4)
    | ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
    | X0 != k1_enumset1(sK5,sK5,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2496])).

cnf(c_4658,plain,
    ( ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k1_enumset1(sK5,sK5,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_3382])).

cnf(c_4659,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k1_enumset1(sK5,sK5,sK5)
    | sK4 != sK4
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4658])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3019,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3020,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3019])).

cnf(c_1481,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2384,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_2377,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1481])).

cnf(c_1482,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2277,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(instantiation,[status(thm)],[c_1482])).

cnf(c_2376,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_2277])).

cnf(c_2367,plain,
    ( ~ m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4))
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2368,plain,
    ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) != iProver_top
    | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2367])).

cnf(c_720,plain,
    ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
    | sK4 != X1
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_20])).

cnf(c_721,plain,
    ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_720])).

cnf(c_722,plain,
    ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_19,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_32,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4928,c_4659,c_3055,c_3020,c_2557,c_2384,c_2377,c_2376,c_2368,c_2255,c_729,c_722,c_19,c_32,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 14:07:57 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 2.44/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.44/0.99  
% 2.44/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.44/0.99  
% 2.44/0.99  ------  iProver source info
% 2.44/0.99  
% 2.44/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.44/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.44/0.99  git: non_committed_changes: false
% 2.44/0.99  git: last_make_outside_of_git: false
% 2.44/0.99  
% 2.44/0.99  ------ 
% 2.44/0.99  
% 2.44/0.99  ------ Input Options
% 2.44/0.99  
% 2.44/0.99  --out_options                           all
% 2.44/0.99  --tptp_safe_out                         true
% 2.44/0.99  --problem_path                          ""
% 2.44/0.99  --include_path                          ""
% 2.44/0.99  --clausifier                            res/vclausify_rel
% 2.44/0.99  --clausifier_options                    --mode clausify
% 2.44/0.99  --stdin                                 false
% 2.44/0.99  --stats_out                             all
% 2.44/0.99  
% 2.44/0.99  ------ General Options
% 2.44/0.99  
% 2.44/0.99  --fof                                   false
% 2.44/0.99  --time_out_real                         305.
% 2.44/0.99  --time_out_virtual                      -1.
% 2.44/0.99  --symbol_type_check                     false
% 2.44/0.99  --clausify_out                          false
% 2.44/0.99  --sig_cnt_out                           false
% 2.44/0.99  --trig_cnt_out                          false
% 2.44/0.99  --trig_cnt_out_tolerance                1.
% 2.44/0.99  --trig_cnt_out_sk_spl                   false
% 2.44/0.99  --abstr_cl_out                          false
% 2.44/0.99  
% 2.44/0.99  ------ Global Options
% 2.44/0.99  
% 2.44/0.99  --schedule                              default
% 2.44/0.99  --add_important_lit                     false
% 2.44/0.99  --prop_solver_per_cl                    1000
% 2.44/0.99  --min_unsat_core                        false
% 2.44/0.99  --soft_assumptions                      false
% 2.44/0.99  --soft_lemma_size                       3
% 2.44/0.99  --prop_impl_unit_size                   0
% 2.44/0.99  --prop_impl_unit                        []
% 2.44/0.99  --share_sel_clauses                     true
% 2.44/0.99  --reset_solvers                         false
% 2.44/0.99  --bc_imp_inh                            [conj_cone]
% 2.44/0.99  --conj_cone_tolerance                   3.
% 2.44/0.99  --extra_neg_conj                        none
% 2.44/0.99  --large_theory_mode                     true
% 2.44/0.99  --prolific_symb_bound                   200
% 2.44/0.99  --lt_threshold                          2000
% 2.44/0.99  --clause_weak_htbl                      true
% 2.44/0.99  --gc_record_bc_elim                     false
% 2.44/0.99  
% 2.44/0.99  ------ Preprocessing Options
% 2.44/0.99  
% 2.44/0.99  --preprocessing_flag                    true
% 2.44/0.99  --time_out_prep_mult                    0.1
% 2.44/0.99  --splitting_mode                        input
% 2.44/0.99  --splitting_grd                         true
% 2.44/0.99  --splitting_cvd                         false
% 2.44/0.99  --splitting_cvd_svl                     false
% 2.44/0.99  --splitting_nvd                         32
% 2.44/0.99  --sub_typing                            true
% 2.44/0.99  --prep_gs_sim                           true
% 2.44/0.99  --prep_unflatten                        true
% 2.44/0.99  --prep_res_sim                          true
% 2.44/0.99  --prep_upred                            true
% 2.44/0.99  --prep_sem_filter                       exhaustive
% 2.44/0.99  --prep_sem_filter_out                   false
% 2.44/0.99  --pred_elim                             true
% 2.44/0.99  --res_sim_input                         true
% 2.44/0.99  --eq_ax_congr_red                       true
% 2.44/0.99  --pure_diseq_elim                       true
% 2.44/0.99  --brand_transform                       false
% 2.44/0.99  --non_eq_to_eq                          false
% 2.44/0.99  --prep_def_merge                        true
% 2.44/0.99  --prep_def_merge_prop_impl              false
% 2.44/0.99  --prep_def_merge_mbd                    true
% 2.44/0.99  --prep_def_merge_tr_red                 false
% 2.44/0.99  --prep_def_merge_tr_cl                  false
% 2.44/0.99  --smt_preprocessing                     true
% 2.44/0.99  --smt_ac_axioms                         fast
% 2.44/0.99  --preprocessed_out                      false
% 2.44/0.99  --preprocessed_stats                    false
% 2.44/0.99  
% 2.44/0.99  ------ Abstraction refinement Options
% 2.44/0.99  
% 2.44/0.99  --abstr_ref                             []
% 2.44/0.99  --abstr_ref_prep                        false
% 2.44/0.99  --abstr_ref_until_sat                   false
% 2.44/0.99  --abstr_ref_sig_restrict                funpre
% 2.44/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/0.99  --abstr_ref_under                       []
% 2.44/0.99  
% 2.44/0.99  ------ SAT Options
% 2.44/0.99  
% 2.44/0.99  --sat_mode                              false
% 2.44/0.99  --sat_fm_restart_options                ""
% 2.44/0.99  --sat_gr_def                            false
% 2.44/0.99  --sat_epr_types                         true
% 2.44/0.99  --sat_non_cyclic_types                  false
% 2.44/0.99  --sat_finite_models                     false
% 2.44/0.99  --sat_fm_lemmas                         false
% 2.44/0.99  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     num_symb
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       true
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  ------ Parsing...
% 2.44/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.44/1.00  ------ Proving...
% 2.44/1.00  ------ Problem Properties 
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  clauses                                 24
% 2.44/1.00  conjectures                             5
% 2.44/1.00  EPR                                     5
% 2.44/1.00  Horn                                    18
% 2.44/1.00  unary                                   6
% 2.44/1.00  binary                                  8
% 2.44/1.00  lits                                    54
% 2.44/1.00  lits eq                                 6
% 2.44/1.00  fd_pure                                 0
% 2.44/1.00  fd_pseudo                               0
% 2.44/1.00  fd_cond                                 0
% 2.44/1.00  fd_pseudo_cond                          2
% 2.44/1.00  AC symbols                              0
% 2.44/1.00  
% 2.44/1.00  ------ Schedule dynamic 5 is on 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ 
% 2.44/1.00  Current options:
% 2.44/1.00  ------ 
% 2.44/1.00  
% 2.44/1.00  ------ Input Options
% 2.44/1.00  
% 2.44/1.00  --out_options                           all
% 2.44/1.00  --tptp_safe_out                         true
% 2.44/1.00  --problem_path                          ""
% 2.44/1.00  --include_path                          ""
% 2.44/1.00  --clausifier                            res/vclausify_rel
% 2.44/1.00  --clausifier_options                    --mode clausify
% 2.44/1.00  --stdin                                 false
% 2.44/1.00  --stats_out                             all
% 2.44/1.00  
% 2.44/1.00  ------ General Options
% 2.44/1.00  
% 2.44/1.00  --fof                                   false
% 2.44/1.00  --time_out_real                         305.
% 2.44/1.00  --time_out_virtual                      -1.
% 2.44/1.00  --symbol_type_check                     false
% 2.44/1.00  --clausify_out                          false
% 2.44/1.00  --sig_cnt_out                           false
% 2.44/1.00  --trig_cnt_out                          false
% 2.44/1.00  --trig_cnt_out_tolerance                1.
% 2.44/1.00  --trig_cnt_out_sk_spl                   false
% 2.44/1.00  --abstr_cl_out                          false
% 2.44/1.00  
% 2.44/1.00  ------ Global Options
% 2.44/1.00  
% 2.44/1.00  --schedule                              default
% 2.44/1.00  --add_important_lit                     false
% 2.44/1.00  --prop_solver_per_cl                    1000
% 2.44/1.00  --min_unsat_core                        false
% 2.44/1.00  --soft_assumptions                      false
% 2.44/1.00  --soft_lemma_size                       3
% 2.44/1.00  --prop_impl_unit_size                   0
% 2.44/1.00  --prop_impl_unit                        []
% 2.44/1.00  --share_sel_clauses                     true
% 2.44/1.00  --reset_solvers                         false
% 2.44/1.00  --bc_imp_inh                            [conj_cone]
% 2.44/1.00  --conj_cone_tolerance                   3.
% 2.44/1.00  --extra_neg_conj                        none
% 2.44/1.00  --large_theory_mode                     true
% 2.44/1.00  --prolific_symb_bound                   200
% 2.44/1.00  --lt_threshold                          2000
% 2.44/1.00  --clause_weak_htbl                      true
% 2.44/1.00  --gc_record_bc_elim                     false
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing Options
% 2.44/1.00  
% 2.44/1.00  --preprocessing_flag                    true
% 2.44/1.00  --time_out_prep_mult                    0.1
% 2.44/1.00  --splitting_mode                        input
% 2.44/1.00  --splitting_grd                         true
% 2.44/1.00  --splitting_cvd                         false
% 2.44/1.00  --splitting_cvd_svl                     false
% 2.44/1.00  --splitting_nvd                         32
% 2.44/1.00  --sub_typing                            true
% 2.44/1.00  --prep_gs_sim                           true
% 2.44/1.00  --prep_unflatten                        true
% 2.44/1.00  --prep_res_sim                          true
% 2.44/1.00  --prep_upred                            true
% 2.44/1.00  --prep_sem_filter                       exhaustive
% 2.44/1.00  --prep_sem_filter_out                   false
% 2.44/1.00  --pred_elim                             true
% 2.44/1.00  --res_sim_input                         true
% 2.44/1.00  --eq_ax_congr_red                       true
% 2.44/1.00  --pure_diseq_elim                       true
% 2.44/1.00  --brand_transform                       false
% 2.44/1.00  --non_eq_to_eq                          false
% 2.44/1.00  --prep_def_merge                        true
% 2.44/1.00  --prep_def_merge_prop_impl              false
% 2.44/1.00  --prep_def_merge_mbd                    true
% 2.44/1.00  --prep_def_merge_tr_red                 false
% 2.44/1.00  --prep_def_merge_tr_cl                  false
% 2.44/1.00  --smt_preprocessing                     true
% 2.44/1.00  --smt_ac_axioms                         fast
% 2.44/1.00  --preprocessed_out                      false
% 2.44/1.00  --preprocessed_stats                    false
% 2.44/1.00  
% 2.44/1.00  ------ Abstraction refinement Options
% 2.44/1.00  
% 2.44/1.00  --abstr_ref                             []
% 2.44/1.00  --abstr_ref_prep                        false
% 2.44/1.00  --abstr_ref_until_sat                   false
% 2.44/1.00  --abstr_ref_sig_restrict                funpre
% 2.44/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.44/1.00  --abstr_ref_under                       []
% 2.44/1.00  
% 2.44/1.00  ------ SAT Options
% 2.44/1.00  
% 2.44/1.00  --sat_mode                              false
% 2.44/1.00  --sat_fm_restart_options                ""
% 2.44/1.00  --sat_gr_def                            false
% 2.44/1.00  --sat_epr_types                         true
% 2.44/1.00  --sat_non_cyclic_types                  false
% 2.44/1.00  --sat_finite_models                     false
% 2.44/1.00  --sat_fm_lemmas                         false
% 2.44/1.00  --sat_fm_prep                           false
% 2.44/1.00  --sat_fm_uc_incr                        true
% 2.44/1.00  --sat_out_model                         small
% 2.44/1.00  --sat_out_clauses                       false
% 2.44/1.00  
% 2.44/1.00  ------ QBF Options
% 2.44/1.00  
% 2.44/1.00  --qbf_mode                              false
% 2.44/1.00  --qbf_elim_univ                         false
% 2.44/1.00  --qbf_dom_inst                          none
% 2.44/1.00  --qbf_dom_pre_inst                      false
% 2.44/1.00  --qbf_sk_in                             false
% 2.44/1.00  --qbf_pred_elim                         true
% 2.44/1.00  --qbf_split                             512
% 2.44/1.00  
% 2.44/1.00  ------ BMC1 Options
% 2.44/1.00  
% 2.44/1.00  --bmc1_incremental                      false
% 2.44/1.00  --bmc1_axioms                           reachable_all
% 2.44/1.00  --bmc1_min_bound                        0
% 2.44/1.00  --bmc1_max_bound                        -1
% 2.44/1.00  --bmc1_max_bound_default                -1
% 2.44/1.00  --bmc1_symbol_reachability              true
% 2.44/1.00  --bmc1_property_lemmas                  false
% 2.44/1.00  --bmc1_k_induction                      false
% 2.44/1.00  --bmc1_non_equiv_states                 false
% 2.44/1.00  --bmc1_deadlock                         false
% 2.44/1.00  --bmc1_ucm                              false
% 2.44/1.00  --bmc1_add_unsat_core                   none
% 2.44/1.00  --bmc1_unsat_core_children              false
% 2.44/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.44/1.00  --bmc1_out_stat                         full
% 2.44/1.00  --bmc1_ground_init                      false
% 2.44/1.00  --bmc1_pre_inst_next_state              false
% 2.44/1.00  --bmc1_pre_inst_state                   false
% 2.44/1.00  --bmc1_pre_inst_reach_state             false
% 2.44/1.00  --bmc1_out_unsat_core                   false
% 2.44/1.00  --bmc1_aig_witness_out                  false
% 2.44/1.00  --bmc1_verbose                          false
% 2.44/1.00  --bmc1_dump_clauses_tptp                false
% 2.44/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.44/1.00  --bmc1_dump_file                        -
% 2.44/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.44/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.44/1.00  --bmc1_ucm_extend_mode                  1
% 2.44/1.00  --bmc1_ucm_init_mode                    2
% 2.44/1.00  --bmc1_ucm_cone_mode                    none
% 2.44/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.44/1.00  --bmc1_ucm_relax_model                  4
% 2.44/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.44/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.44/1.00  --bmc1_ucm_layered_model                none
% 2.44/1.00  --bmc1_ucm_max_lemma_size               10
% 2.44/1.00  
% 2.44/1.00  ------ AIG Options
% 2.44/1.00  
% 2.44/1.00  --aig_mode                              false
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation Options
% 2.44/1.00  
% 2.44/1.00  --instantiation_flag                    true
% 2.44/1.00  --inst_sos_flag                         false
% 2.44/1.00  --inst_sos_phase                        true
% 2.44/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.44/1.00  --inst_lit_sel_side                     none
% 2.44/1.00  --inst_solver_per_active                1400
% 2.44/1.00  --inst_solver_calls_frac                1.
% 2.44/1.00  --inst_passive_queue_type               priority_queues
% 2.44/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.44/1.00  --inst_passive_queues_freq              [25;2]
% 2.44/1.00  --inst_dismatching                      true
% 2.44/1.00  --inst_eager_unprocessed_to_passive     true
% 2.44/1.00  --inst_prop_sim_given                   true
% 2.44/1.00  --inst_prop_sim_new                     false
% 2.44/1.00  --inst_subs_new                         false
% 2.44/1.00  --inst_eq_res_simp                      false
% 2.44/1.00  --inst_subs_given                       false
% 2.44/1.00  --inst_orphan_elimination               true
% 2.44/1.00  --inst_learning_loop_flag               true
% 2.44/1.00  --inst_learning_start                   3000
% 2.44/1.00  --inst_learning_factor                  2
% 2.44/1.00  --inst_start_prop_sim_after_learn       3
% 2.44/1.00  --inst_sel_renew                        solver
% 2.44/1.00  --inst_lit_activity_flag                true
% 2.44/1.00  --inst_restr_to_given                   false
% 2.44/1.00  --inst_activity_threshold               500
% 2.44/1.00  --inst_out_proof                        true
% 2.44/1.00  
% 2.44/1.00  ------ Resolution Options
% 2.44/1.00  
% 2.44/1.00  --resolution_flag                       false
% 2.44/1.00  --res_lit_sel                           adaptive
% 2.44/1.00  --res_lit_sel_side                      none
% 2.44/1.00  --res_ordering                          kbo
% 2.44/1.00  --res_to_prop_solver                    active
% 2.44/1.00  --res_prop_simpl_new                    false
% 2.44/1.00  --res_prop_simpl_given                  true
% 2.44/1.00  --res_passive_queue_type                priority_queues
% 2.44/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.44/1.00  --res_passive_queues_freq               [15;5]
% 2.44/1.00  --res_forward_subs                      full
% 2.44/1.00  --res_backward_subs                     full
% 2.44/1.00  --res_forward_subs_resolution           true
% 2.44/1.00  --res_backward_subs_resolution          true
% 2.44/1.00  --res_orphan_elimination                true
% 2.44/1.00  --res_time_limit                        2.
% 2.44/1.00  --res_out_proof                         true
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Options
% 2.44/1.00  
% 2.44/1.00  --superposition_flag                    true
% 2.44/1.00  --sup_passive_queue_type                priority_queues
% 2.44/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.44/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.44/1.00  --demod_completeness_check              fast
% 2.44/1.00  --demod_use_ground                      true
% 2.44/1.00  --sup_to_prop_solver                    passive
% 2.44/1.00  --sup_prop_simpl_new                    true
% 2.44/1.00  --sup_prop_simpl_given                  true
% 2.44/1.00  --sup_fun_splitting                     false
% 2.44/1.00  --sup_smt_interval                      50000
% 2.44/1.00  
% 2.44/1.00  ------ Superposition Simplification Setup
% 2.44/1.00  
% 2.44/1.00  --sup_indices_passive                   []
% 2.44/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.44/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.44/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_full_bw                           [BwDemod]
% 2.44/1.00  --sup_immed_triv                        [TrivRules]
% 2.44/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.44/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_immed_bw_main                     []
% 2.44/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.44/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.44/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.44/1.00  
% 2.44/1.00  ------ Combination Options
% 2.44/1.00  
% 2.44/1.00  --comb_res_mult                         3
% 2.44/1.00  --comb_sup_mult                         2
% 2.44/1.00  --comb_inst_mult                        10
% 2.44/1.00  
% 2.44/1.00  ------ Debug Options
% 2.44/1.00  
% 2.44/1.00  --dbg_backtrace                         false
% 2.44/1.00  --dbg_dump_prop_clauses                 false
% 2.44/1.00  --dbg_dump_prop_clauses_file            -
% 2.44/1.00  --dbg_out_stat                          false
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  ------ Proving...
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS status Theorem for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  fof(f14,conjecture,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f15,negated_conjecture,(
% 2.44/1.00    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.44/1.00    inference(negated_conjecture,[],[f14])).
% 2.44/1.00  
% 2.44/1.00  fof(f27,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f15])).
% 2.44/1.00  
% 2.44/1.00  fof(f28,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f27])).
% 2.44/1.00  
% 2.44/1.00  fof(f44,plain,(
% 2.44/1.00    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f43,plain,(
% 2.44/1.00    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f42,plain,(
% 2.44/1.00    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f45,plain,(
% 2.44/1.00    ((k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f28,f44,f43,f42])).
% 2.44/1.00  
% 2.44/1.00  fof(f72,plain,(
% 2.44/1.00    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f12,axiom,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f23,plain,(
% 2.44/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f12])).
% 2.44/1.00  
% 2.44/1.00  fof(f24,plain,(
% 2.44/1.00    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.44/1.00    inference(flattening,[],[f23])).
% 2.44/1.00  
% 2.44/1.00  fof(f62,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f24])).
% 2.44/1.00  
% 2.44/1.00  fof(f2,axiom,(
% 2.44/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f48,plain,(
% 2.44/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f2])).
% 2.44/1.00  
% 2.44/1.00  fof(f3,axiom,(
% 2.44/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f49,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f3])).
% 2.44/1.00  
% 2.44/1.00  fof(f75,plain,(
% 2.44/1.00    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f48,f49])).
% 2.44/1.00  
% 2.44/1.00  fof(f77,plain,(
% 2.44/1.00    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f62,f75])).
% 2.44/1.00  
% 2.44/1.00  fof(f70,plain,(
% 2.44/1.00    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f1,axiom,(
% 2.44/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f29,plain,(
% 2.44/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.44/1.00    inference(nnf_transformation,[],[f1])).
% 2.44/1.00  
% 2.44/1.00  fof(f30,plain,(
% 2.44/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.44/1.00    inference(rectify,[],[f29])).
% 2.44/1.00  
% 2.44/1.00  fof(f31,plain,(
% 2.44/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f32,plain,(
% 2.44/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 2.44/1.00  
% 2.44/1.00  fof(f46,plain,(
% 2.44/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f32])).
% 2.44/1.00  
% 2.44/1.00  fof(f73,plain,(
% 2.44/1.00    r2_hidden(sK5,sK4)),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f10,axiom,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f37,plain,(
% 2.44/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.44/1.00    inference(nnf_transformation,[],[f10])).
% 2.44/1.00  
% 2.44/1.00  fof(f59,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f8,axiom,(
% 2.44/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f18,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.44/1.00    inference(ennf_transformation,[],[f8])).
% 2.44/1.00  
% 2.44/1.00  fof(f57,plain,(
% 2.44/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f18])).
% 2.44/1.00  
% 2.44/1.00  fof(f60,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f37])).
% 2.44/1.00  
% 2.44/1.00  fof(f7,axiom,(
% 2.44/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f17,plain,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f7])).
% 2.44/1.00  
% 2.44/1.00  fof(f56,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f17])).
% 2.44/1.00  
% 2.44/1.00  fof(f76,plain,(
% 2.44/1.00    ( ! [X0,X1] : (m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 2.44/1.00    inference(definition_unfolding,[],[f56,f75])).
% 2.44/1.00  
% 2.44/1.00  fof(f13,axiom,(
% 2.44/1.00    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f25,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.44/1.00    inference(ennf_transformation,[],[f13])).
% 2.44/1.00  
% 2.44/1.00  fof(f26,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(flattening,[],[f25])).
% 2.44/1.00  
% 2.44/1.00  fof(f38,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(nnf_transformation,[],[f26])).
% 2.44/1.00  
% 2.44/1.00  fof(f39,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(rectify,[],[f38])).
% 2.44/1.00  
% 2.44/1.00  fof(f40,plain,(
% 2.44/1.00    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.44/1.00    introduced(choice_axiom,[])).
% 2.44/1.00  
% 2.44/1.00  fof(f41,plain,(
% 2.44/1.00    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.44/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f39,f40])).
% 2.44/1.00  
% 2.44/1.00  fof(f63,plain,(
% 2.44/1.00    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f41])).
% 2.44/1.00  
% 2.44/1.00  fof(f69,plain,(
% 2.44/1.00    l1_pre_topc(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f67,plain,(
% 2.44/1.00    ~v2_struct_0(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f68,plain,(
% 2.44/1.00    v2_pre_topc(sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f71,plain,(
% 2.44/1.00    v2_tex_2(sK4,sK3)),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  fof(f9,axiom,(
% 2.44/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.44/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.44/1.00  
% 2.44/1.00  fof(f19,plain,(
% 2.44/1.00    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.44/1.00    inference(ennf_transformation,[],[f9])).
% 2.44/1.00  
% 2.44/1.00  fof(f20,plain,(
% 2.44/1.00    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.44/1.00    inference(flattening,[],[f19])).
% 2.44/1.00  
% 2.44/1.00  fof(f58,plain,(
% 2.44/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 2.44/1.00    inference(cnf_transformation,[],[f20])).
% 2.44/1.00  
% 2.44/1.00  fof(f74,plain,(
% 2.44/1.00    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 2.44/1.00    inference(cnf_transformation,[],[f45])).
% 2.44/1.00  
% 2.44/1.00  cnf(c_21,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.44/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2062,plain,
% 2.44/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_14,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,X1)
% 2.44/1.00      | v1_xboole_0(X1)
% 2.44/1.00      | k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2064,plain,
% 2.44/1.00      ( k1_enumset1(X0,X0,X0) = k6_domain_1(X1,X0)
% 2.44/1.00      | m1_subset_1(X0,X1) != iProver_top
% 2.44/1.00      | v1_xboole_0(X1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3055,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_enumset1(sK5,sK5,sK5)
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2062,c_2064]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_23,negated_conjecture,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_30,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1,plain,
% 2.44/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_20,negated_conjecture,
% 2.44/1.00      ( r2_hidden(sK5,sK4) ),
% 2.44/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_727,plain,
% 2.44/1.00      ( ~ v1_xboole_0(X0) | sK4 != X0 | sK5 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_728,plain,
% 2.44/1.00      ( ~ v1_xboole_0(sK4) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_727]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_729,plain,
% 2.44/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_12,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2254,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2255,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | r1_tarski(sK4,u1_struct_0(sK3)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2254]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_9,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.44/1.00      | ~ v1_xboole_0(X1)
% 2.44/1.00      | v1_xboole_0(X0) ),
% 2.44/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_11,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_207,plain,
% 2.44/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.44/1.00      inference(prop_impl,[status(thm)],[c_11]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_208,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_207]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_256,plain,
% 2.44/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 2.44/1.00      inference(bin_hyper_res,[status(thm)],[c_9,c_208]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2315,plain,
% 2.44/1.00      ( ~ r1_tarski(sK4,X0) | ~ v1_xboole_0(X0) | v1_xboole_0(sK4) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_256]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2556,plain,
% 2.44/1.00      ( ~ r1_tarski(sK4,u1_struct_0(sK3))
% 2.44/1.00      | ~ v1_xboole_0(u1_struct_0(sK3))
% 2.44/1.00      | v1_xboole_0(sK4) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2315]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2557,plain,
% 2.44/1.00      ( r1_tarski(sK4,u1_struct_0(sK3)) != iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top
% 2.44/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2556]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3355,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK3),sK5) = k1_enumset1(sK5,sK5,sK5) ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_3055,c_30,c_729,c_2255,c_2557]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_8,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 2.44/1.00      | ~ r2_hidden(X0,X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2069,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.44/1.00      | r2_hidden(X0,X1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3894,plain,
% 2.44/1.00      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(X0)) = iProver_top
% 2.44/1.00      | r2_hidden(sK5,X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3355,c_2069]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2066,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4479,plain,
% 2.44/1.00      ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),X0) = iProver_top
% 2.44/1.00      | r2_hidden(sK5,X0) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_3894,c_2066]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2060,plain,
% 2.44/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2067,plain,
% 2.44/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.44/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_18,plain,
% 2.44/1.00      ( ~ v2_tex_2(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ r1_tarski(X2,X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | ~ l1_pre_topc(X1)
% 2.44/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.44/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_24,negated_conjecture,
% 2.44/1.00      ( l1_pre_topc(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_353,plain,
% 2.44/1.00      ( ~ v2_tex_2(X0,X1)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.44/1.00      | ~ r1_tarski(X2,X0)
% 2.44/1.00      | v2_struct_0(X1)
% 2.44/1.00      | ~ v2_pre_topc(X1)
% 2.44/1.00      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.44/1.00      | sK3 != X1 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_354,plain,
% 2.44/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ r1_tarski(X1,X0)
% 2.44/1.00      | v2_struct_0(sK3)
% 2.44/1.00      | ~ v2_pre_topc(sK3)
% 2.44/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_353]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_26,negated_conjecture,
% 2.44/1.00      ( ~ v2_struct_0(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_25,negated_conjecture,
% 2.44/1.00      ( v2_pre_topc(sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_358,plain,
% 2.44/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ r1_tarski(X1,X0)
% 2.44/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_354,c_26,c_25]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_359,plain,
% 2.44/1.00      ( ~ v2_tex_2(X0,sK3)
% 2.44/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.44/1.00      | ~ r1_tarski(X1,X0)
% 2.44/1.00      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.44/1.00      inference(renaming,[status(thm)],[c_358]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2058,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.44/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 2.44/1.00      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_359]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3170,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1
% 2.44/1.00      | v2_tex_2(X0,sK3) != iProver_top
% 2.44/1.00      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 2.44/1.00      | r1_tarski(X1,X0) != iProver_top
% 2.44/1.00      | r1_tarski(X1,u1_struct_0(sK3)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2067,c_2058]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3476,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 2.44/1.00      | v2_tex_2(sK4,sK3) != iProver_top
% 2.44/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/1.00      | r1_tarski(X0,sK4) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_2060,c_3170]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_22,negated_conjecture,
% 2.44/1.00      ( v2_tex_2(sK4,sK3) ),
% 2.44/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_31,plain,
% 2.44/1.00      ( v2_tex_2(sK4,sK3) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3589,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0
% 2.44/1.00      | r1_tarski(X0,u1_struct_0(sK3)) != iProver_top
% 2.44/1.00      | r1_tarski(X0,sK4) != iProver_top ),
% 2.44/1.00      inference(global_propositional_subsumption,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_3476,c_31]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4928,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5)
% 2.44/1.00      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) != iProver_top
% 2.44/1.00      | r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top ),
% 2.44/1.00      inference(superposition,[status(thm)],[c_4479,c_3589]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1486,plain,
% 2.44/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.44/1.00      theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2496,plain,
% 2.44/1.00      ( r1_tarski(X0,X1)
% 2.44/1.00      | ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
% 2.44/1.00      | X0 != k1_enumset1(sK5,sK5,sK5)
% 2.44/1.00      | X1 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1486]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3382,plain,
% 2.44/1.00      ( r1_tarski(X0,sK4)
% 2.44/1.00      | ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
% 2.44/1.00      | X0 != k1_enumset1(sK5,sK5,sK5)
% 2.44/1.00      | sK4 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2496]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4658,plain,
% 2.44/1.00      ( ~ r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4)
% 2.44/1.00      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK3),sK5) != k1_enumset1(sK5,sK5,sK5)
% 2.44/1.00      | sK4 != sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_3382]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_4659,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK3),sK5) != k1_enumset1(sK5,sK5,sK5)
% 2.44/1.00      | sK4 != sK4
% 2.44/1.00      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) != iProver_top
% 2.44/1.00      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_4658]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_10,plain,
% 2.44/1.00      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.44/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3019,plain,
% 2.44/1.00      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.44/1.00      | r2_hidden(sK5,u1_struct_0(sK3))
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_3020,plain,
% 2.44/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) != iProver_top
% 2.44/1.00      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 2.44/1.00      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_3019]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1481,plain,( X0 = X0 ),theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2384,plain,
% 2.44/1.00      ( sK4 = sK4 ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1481]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2377,plain,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1481]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_1482,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2277,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK3),sK5) != X0
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_1482]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2376,plain,
% 2.44/1.00      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
% 2.44/1.00      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_2277]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2367,plain,
% 2.44/1.00      ( ~ m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4))
% 2.44/1.00      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) ),
% 2.44/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_2368,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) != iProver_top
% 2.44/1.00      | r1_tarski(k1_enumset1(sK5,sK5,sK5),sK4) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_2367]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_720,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(X0,X0,X0),k1_zfmisc_1(X1))
% 2.44/1.00      | sK4 != X1
% 2.44/1.00      | sK5 != X0 ),
% 2.44/1.00      inference(resolution_lifted,[status(thm)],[c_8,c_20]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_721,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) ),
% 2.44/1.00      inference(unflattening,[status(thm)],[c_720]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_722,plain,
% 2.44/1.00      ( m1_subset_1(k1_enumset1(sK5,sK5,sK5),k1_zfmisc_1(sK4)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_19,negated_conjecture,
% 2.44/1.00      ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.44/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(c_32,plain,
% 2.44/1.00      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 2.44/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.44/1.00  
% 2.44/1.00  cnf(contradiction,plain,
% 2.44/1.00      ( $false ),
% 2.44/1.00      inference(minisat,
% 2.44/1.00                [status(thm)],
% 2.44/1.00                [c_4928,c_4659,c_3055,c_3020,c_2557,c_2384,c_2377,c_2376,
% 2.44/1.00                 c_2368,c_2255,c_729,c_722,c_19,c_32,c_30]) ).
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.44/1.00  
% 2.44/1.00  ------                               Statistics
% 2.44/1.00  
% 2.44/1.00  ------ General
% 2.44/1.00  
% 2.44/1.00  abstr_ref_over_cycles:                  0
% 2.44/1.00  abstr_ref_under_cycles:                 0
% 2.44/1.00  gc_basic_clause_elim:                   0
% 2.44/1.00  forced_gc_time:                         0
% 2.44/1.00  parsing_time:                           0.01
% 2.44/1.00  unif_index_cands_time:                  0.
% 2.44/1.00  unif_index_add_time:                    0.
% 2.44/1.00  orderings_time:                         0.
% 2.44/1.00  out_proof_time:                         0.007
% 2.44/1.00  total_time:                             0.15
% 2.44/1.00  num_of_symbols:                         51
% 2.44/1.00  num_of_terms:                           3350
% 2.44/1.00  
% 2.44/1.00  ------ Preprocessing
% 2.44/1.00  
% 2.44/1.00  num_of_splits:                          0
% 2.44/1.00  num_of_split_atoms:                     0
% 2.44/1.00  num_of_reused_defs:                     0
% 2.44/1.00  num_eq_ax_congr_red:                    22
% 2.44/1.00  num_of_sem_filtered_clauses:            1
% 2.44/1.00  num_of_subtypes:                        0
% 2.44/1.00  monotx_restored_types:                  0
% 2.44/1.00  sat_num_of_epr_types:                   0
% 2.44/1.00  sat_num_of_non_cyclic_types:            0
% 2.44/1.00  sat_guarded_non_collapsed_types:        0
% 2.44/1.00  num_pure_diseq_elim:                    0
% 2.44/1.00  simp_replaced_by:                       0
% 2.44/1.00  res_preprocessed:                       126
% 2.44/1.00  prep_upred:                             0
% 2.44/1.00  prep_unflattend:                        84
% 2.44/1.00  smt_new_axioms:                         0
% 2.44/1.00  pred_elim_cands:                        5
% 2.44/1.00  pred_elim:                              3
% 2.44/1.00  pred_elim_cl:                           3
% 2.44/1.00  pred_elim_cycles:                       7
% 2.44/1.00  merged_defs:                            16
% 2.44/1.00  merged_defs_ncl:                        0
% 2.44/1.00  bin_hyper_res:                          17
% 2.44/1.00  prep_cycles:                            4
% 2.44/1.00  pred_elim_time:                         0.016
% 2.44/1.00  splitting_time:                         0.
% 2.44/1.00  sem_filter_time:                        0.
% 2.44/1.00  monotx_time:                            0.
% 2.44/1.00  subtype_inf_time:                       0.
% 2.44/1.00  
% 2.44/1.00  ------ Problem properties
% 2.44/1.00  
% 2.44/1.00  clauses:                                24
% 2.44/1.00  conjectures:                            5
% 2.44/1.00  epr:                                    5
% 2.44/1.00  horn:                                   18
% 2.44/1.00  ground:                                 5
% 2.44/1.00  unary:                                  6
% 2.44/1.00  binary:                                 8
% 2.44/1.00  lits:                                   54
% 2.44/1.00  lits_eq:                                6
% 2.44/1.00  fd_pure:                                0
% 2.44/1.00  fd_pseudo:                              0
% 2.44/1.00  fd_cond:                                0
% 2.44/1.00  fd_pseudo_cond:                         2
% 2.44/1.00  ac_symbols:                             0
% 2.44/1.00  
% 2.44/1.00  ------ Propositional Solver
% 2.44/1.00  
% 2.44/1.00  prop_solver_calls:                      28
% 2.44/1.00  prop_fast_solver_calls:                 967
% 2.44/1.00  smt_solver_calls:                       0
% 2.44/1.00  smt_fast_solver_calls:                  0
% 2.44/1.00  prop_num_of_clauses:                    1439
% 2.44/1.00  prop_preprocess_simplified:             5039
% 2.44/1.00  prop_fo_subsumed:                       21
% 2.44/1.00  prop_solver_time:                       0.
% 2.44/1.00  smt_solver_time:                        0.
% 2.44/1.00  smt_fast_solver_time:                   0.
% 2.44/1.00  prop_fast_solver_time:                  0.
% 2.44/1.00  prop_unsat_core_time:                   0.
% 2.44/1.00  
% 2.44/1.00  ------ QBF
% 2.44/1.00  
% 2.44/1.00  qbf_q_res:                              0
% 2.44/1.00  qbf_num_tautologies:                    0
% 2.44/1.00  qbf_prep_cycles:                        0
% 2.44/1.00  
% 2.44/1.00  ------ BMC1
% 2.44/1.00  
% 2.44/1.00  bmc1_current_bound:                     -1
% 2.44/1.00  bmc1_last_solved_bound:                 -1
% 2.44/1.00  bmc1_unsat_core_size:                   -1
% 2.44/1.00  bmc1_unsat_core_parents_size:           -1
% 2.44/1.00  bmc1_merge_next_fun:                    0
% 2.44/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.44/1.00  
% 2.44/1.00  ------ Instantiation
% 2.44/1.00  
% 2.44/1.00  inst_num_of_clauses:                    394
% 2.44/1.00  inst_num_in_passive:                    92
% 2.44/1.00  inst_num_in_active:                     227
% 2.44/1.00  inst_num_in_unprocessed:                75
% 2.44/1.00  inst_num_of_loops:                      260
% 2.44/1.00  inst_num_of_learning_restarts:          0
% 2.44/1.00  inst_num_moves_active_passive:          30
% 2.44/1.00  inst_lit_activity:                      0
% 2.44/1.00  inst_lit_activity_moves:                0
% 2.44/1.00  inst_num_tautologies:                   0
% 2.44/1.00  inst_num_prop_implied:                  0
% 2.44/1.00  inst_num_existing_simplified:           0
% 2.44/1.00  inst_num_eq_res_simplified:             0
% 2.44/1.00  inst_num_child_elim:                    0
% 2.44/1.00  inst_num_of_dismatching_blockings:      103
% 2.44/1.00  inst_num_of_non_proper_insts:           328
% 2.44/1.00  inst_num_of_duplicates:                 0
% 2.44/1.00  inst_inst_num_from_inst_to_res:         0
% 2.44/1.00  inst_dismatching_checking_time:         0.
% 2.44/1.00  
% 2.44/1.00  ------ Resolution
% 2.44/1.00  
% 2.44/1.00  res_num_of_clauses:                     0
% 2.44/1.00  res_num_in_passive:                     0
% 2.44/1.00  res_num_in_active:                      0
% 2.44/1.00  res_num_of_loops:                       130
% 2.44/1.00  res_forward_subset_subsumed:            46
% 2.44/1.00  res_backward_subset_subsumed:           0
% 2.44/1.00  res_forward_subsumed:                   2
% 2.44/1.00  res_backward_subsumed:                  0
% 2.44/1.00  res_forward_subsumption_resolution:     0
% 2.44/1.00  res_backward_subsumption_resolution:    0
% 2.44/1.00  res_clause_to_clause_subsumption:       321
% 2.44/1.00  res_orphan_elimination:                 0
% 2.44/1.00  res_tautology_del:                      73
% 2.44/1.00  res_num_eq_res_simplified:              0
% 2.44/1.00  res_num_sel_changes:                    0
% 2.44/1.00  res_moves_from_active_to_pass:          0
% 2.44/1.00  
% 2.44/1.00  ------ Superposition
% 2.44/1.00  
% 2.44/1.00  sup_time_total:                         0.
% 2.44/1.00  sup_time_generating:                    0.
% 2.44/1.00  sup_time_sim_full:                      0.
% 2.44/1.00  sup_time_sim_immed:                     0.
% 2.44/1.00  
% 2.44/1.00  sup_num_of_clauses:                     95
% 2.44/1.00  sup_num_in_active:                      51
% 2.44/1.00  sup_num_in_passive:                     44
% 2.44/1.00  sup_num_of_loops:                       50
% 2.44/1.00  sup_fw_superposition:                   41
% 2.44/1.00  sup_bw_superposition:                   51
% 2.44/1.00  sup_immediate_simplified:               9
% 2.44/1.00  sup_given_eliminated:                   0
% 2.44/1.00  comparisons_done:                       0
% 2.44/1.00  comparisons_avoided:                    0
% 2.44/1.00  
% 2.44/1.00  ------ Simplifications
% 2.44/1.00  
% 2.44/1.00  
% 2.44/1.00  sim_fw_subset_subsumed:                 5
% 2.44/1.00  sim_bw_subset_subsumed:                 0
% 2.44/1.00  sim_fw_subsumed:                        2
% 2.44/1.00  sim_bw_subsumed:                        0
% 2.44/1.00  sim_fw_subsumption_res:                 0
% 2.44/1.00  sim_bw_subsumption_res:                 0
% 2.44/1.00  sim_tautology_del:                      5
% 2.44/1.00  sim_eq_tautology_del:                   0
% 2.44/1.00  sim_eq_res_simp:                        0
% 2.44/1.00  sim_fw_demodulated:                     0
% 2.44/1.00  sim_bw_demodulated:                     0
% 2.44/1.00  sim_light_normalised:                   2
% 2.44/1.00  sim_joinable_taut:                      0
% 2.44/1.00  sim_joinable_simp:                      0
% 2.44/1.00  sim_ac_normalised:                      0
% 2.44/1.00  sim_smt_subsumption:                    0
% 2.44/1.00  
%------------------------------------------------------------------------------
