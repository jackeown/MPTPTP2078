%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:36 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 445 expanded)
%              Number of clauses        :   63 ( 137 expanded)
%              Number of leaves         :   13 ( 119 expanded)
%              Depth                    :   14
%              Number of atoms          :  384 (2253 expanded)
%              Number of equality atoms :   85 ( 365 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & v2_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
            & r2_hidden(X2,sK3)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & v2_tex_2(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
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
              ( k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2)))
              & r2_hidden(X2,X1)
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & v2_tex_2(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35,f34,f33])).

fof(f57,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

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
    inference(nnf_transformation,[],[f11])).

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
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f8,axiom,(
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

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
                & r1_tarski(sK1(X0,X1),X1)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
                  | ~ r1_tarski(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f36])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f36])).

fof(f55,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_2101,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3))
    | r1_tarski(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4186,plain,
    ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3))
    | r1_tarski(k1_tarski(sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_2101])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1840,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1846,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2225,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_1846])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1841,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2914,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2225,c_1841])).

cnf(c_28,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1987,plain,
    ( m1_subset_1(sK4,sK3)
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1988,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1987])).

cnf(c_2061,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2066,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2061])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1848,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1849,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2789,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1848,c_1849])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_5,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_160,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_161,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_160])).

cnf(c_201,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_7,c_161])).

cnf(c_1836,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_201])).

cnf(c_2725,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_1836])).

cnf(c_3552,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2789,c_2725])).

cnf(c_3569,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2914,c_28,c_1988,c_2066,c_3552])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1842,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3572,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3569,c_1842])).

cnf(c_3573,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3572])).

cnf(c_3567,plain,
    ( ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3552])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_346,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_347,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_351,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_347,c_21,c_20])).

cnf(c_352,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_351])).

cnf(c_1981,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_352])).

cnf(c_3488,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(k1_tarski(sK4),sK3)
    | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_1981])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1839,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2911,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1839,c_1841])).

cnf(c_2027,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1837,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1843,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2261,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1837,c_1843])).

cnf(c_2262,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2261])).

cnf(c_2072,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_201])).

cnf(c_2477,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ r1_tarski(sK3,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2072])).

cnf(c_3194,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2911,c_16,c_15,c_2027,c_2262,c_2477])).

cnf(c_3372,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3194,c_1842])).

cnf(c_3450,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3372])).

cnf(c_14,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3197,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
    inference(demodulation,[status(thm)],[c_3194,c_14])).

cnf(c_17,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4186,c_3573,c_3567,c_3488,c_3450,c_3197,c_2477,c_2262,c_1987,c_15,c_16,c_17,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.18/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.18/1.00  
% 2.18/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.00  
% 2.18/1.00  ------  iProver source info
% 2.18/1.00  
% 2.18/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.00  git: non_committed_changes: false
% 2.18/1.00  git: last_make_outside_of_git: false
% 2.18/1.00  
% 2.18/1.00  ------ 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options
% 2.18/1.00  
% 2.18/1.00  --out_options                           all
% 2.18/1.00  --tptp_safe_out                         true
% 2.18/1.00  --problem_path                          ""
% 2.18/1.00  --include_path                          ""
% 2.18/1.00  --clausifier                            res/vclausify_rel
% 2.18/1.00  --clausifier_options                    --mode clausify
% 2.18/1.00  --stdin                                 false
% 2.18/1.00  --stats_out                             all
% 2.18/1.00  
% 2.18/1.00  ------ General Options
% 2.18/1.00  
% 2.18/1.00  --fof                                   false
% 2.18/1.00  --time_out_real                         305.
% 2.18/1.00  --time_out_virtual                      -1.
% 2.18/1.00  --symbol_type_check                     false
% 2.18/1.00  --clausify_out                          false
% 2.18/1.00  --sig_cnt_out                           false
% 2.18/1.00  --trig_cnt_out                          false
% 2.18/1.00  --trig_cnt_out_tolerance                1.
% 2.18/1.00  --trig_cnt_out_sk_spl                   false
% 2.18/1.00  --abstr_cl_out                          false
% 2.18/1.00  
% 2.18/1.00  ------ Global Options
% 2.18/1.00  
% 2.18/1.00  --schedule                              default
% 2.18/1.00  --add_important_lit                     false
% 2.18/1.00  --prop_solver_per_cl                    1000
% 2.18/1.00  --min_unsat_core                        false
% 2.18/1.00  --soft_assumptions                      false
% 2.18/1.00  --soft_lemma_size                       3
% 2.18/1.00  --prop_impl_unit_size                   0
% 2.18/1.00  --prop_impl_unit                        []
% 2.18/1.00  --share_sel_clauses                     true
% 2.18/1.00  --reset_solvers                         false
% 2.18/1.00  --bc_imp_inh                            [conj_cone]
% 2.18/1.00  --conj_cone_tolerance                   3.
% 2.18/1.00  --extra_neg_conj                        none
% 2.18/1.00  --large_theory_mode                     true
% 2.18/1.00  --prolific_symb_bound                   200
% 2.18/1.00  --lt_threshold                          2000
% 2.18/1.00  --clause_weak_htbl                      true
% 2.18/1.00  --gc_record_bc_elim                     false
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing Options
% 2.18/1.00  
% 2.18/1.00  --preprocessing_flag                    true
% 2.18/1.00  --time_out_prep_mult                    0.1
% 2.18/1.00  --splitting_mode                        input
% 2.18/1.00  --splitting_grd                         true
% 2.18/1.00  --splitting_cvd                         false
% 2.18/1.00  --splitting_cvd_svl                     false
% 2.18/1.00  --splitting_nvd                         32
% 2.18/1.00  --sub_typing                            true
% 2.18/1.00  --prep_gs_sim                           true
% 2.18/1.00  --prep_unflatten                        true
% 2.18/1.00  --prep_res_sim                          true
% 2.18/1.00  --prep_upred                            true
% 2.18/1.00  --prep_sem_filter                       exhaustive
% 2.18/1.00  --prep_sem_filter_out                   false
% 2.18/1.00  --pred_elim                             true
% 2.18/1.00  --res_sim_input                         true
% 2.18/1.00  --eq_ax_congr_red                       true
% 2.18/1.00  --pure_diseq_elim                       true
% 2.18/1.00  --brand_transform                       false
% 2.18/1.00  --non_eq_to_eq                          false
% 2.18/1.00  --prep_def_merge                        true
% 2.18/1.00  --prep_def_merge_prop_impl              false
% 2.18/1.00  --prep_def_merge_mbd                    true
% 2.18/1.00  --prep_def_merge_tr_red                 false
% 2.18/1.00  --prep_def_merge_tr_cl                  false
% 2.18/1.00  --smt_preprocessing                     true
% 2.18/1.00  --smt_ac_axioms                         fast
% 2.18/1.00  --preprocessed_out                      false
% 2.18/1.00  --preprocessed_stats                    false
% 2.18/1.00  
% 2.18/1.00  ------ Abstraction refinement Options
% 2.18/1.00  
% 2.18/1.00  --abstr_ref                             []
% 2.18/1.00  --abstr_ref_prep                        false
% 2.18/1.00  --abstr_ref_until_sat                   false
% 2.18/1.00  --abstr_ref_sig_restrict                funpre
% 2.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.00  --abstr_ref_under                       []
% 2.18/1.00  
% 2.18/1.00  ------ SAT Options
% 2.18/1.00  
% 2.18/1.00  --sat_mode                              false
% 2.18/1.00  --sat_fm_restart_options                ""
% 2.18/1.00  --sat_gr_def                            false
% 2.18/1.00  --sat_epr_types                         true
% 2.18/1.00  --sat_non_cyclic_types                  false
% 2.18/1.00  --sat_finite_models                     false
% 2.18/1.00  --sat_fm_lemmas                         false
% 2.18/1.00  --sat_fm_prep                           false
% 2.18/1.00  --sat_fm_uc_incr                        true
% 2.18/1.00  --sat_out_model                         small
% 2.18/1.00  --sat_out_clauses                       false
% 2.18/1.00  
% 2.18/1.00  ------ QBF Options
% 2.18/1.00  
% 2.18/1.00  --qbf_mode                              false
% 2.18/1.00  --qbf_elim_univ                         false
% 2.18/1.00  --qbf_dom_inst                          none
% 2.18/1.00  --qbf_dom_pre_inst                      false
% 2.18/1.00  --qbf_sk_in                             false
% 2.18/1.00  --qbf_pred_elim                         true
% 2.18/1.00  --qbf_split                             512
% 2.18/1.00  
% 2.18/1.00  ------ BMC1 Options
% 2.18/1.00  
% 2.18/1.00  --bmc1_incremental                      false
% 2.18/1.00  --bmc1_axioms                           reachable_all
% 2.18/1.00  --bmc1_min_bound                        0
% 2.18/1.00  --bmc1_max_bound                        -1
% 2.18/1.00  --bmc1_max_bound_default                -1
% 2.18/1.00  --bmc1_symbol_reachability              true
% 2.18/1.00  --bmc1_property_lemmas                  false
% 2.18/1.00  --bmc1_k_induction                      false
% 2.18/1.00  --bmc1_non_equiv_states                 false
% 2.18/1.00  --bmc1_deadlock                         false
% 2.18/1.00  --bmc1_ucm                              false
% 2.18/1.00  --bmc1_add_unsat_core                   none
% 2.18/1.00  --bmc1_unsat_core_children              false
% 2.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.00  --bmc1_out_stat                         full
% 2.18/1.00  --bmc1_ground_init                      false
% 2.18/1.00  --bmc1_pre_inst_next_state              false
% 2.18/1.00  --bmc1_pre_inst_state                   false
% 2.18/1.00  --bmc1_pre_inst_reach_state             false
% 2.18/1.00  --bmc1_out_unsat_core                   false
% 2.18/1.00  --bmc1_aig_witness_out                  false
% 2.18/1.00  --bmc1_verbose                          false
% 2.18/1.00  --bmc1_dump_clauses_tptp                false
% 2.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.00  --bmc1_dump_file                        -
% 2.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.00  --bmc1_ucm_extend_mode                  1
% 2.18/1.00  --bmc1_ucm_init_mode                    2
% 2.18/1.00  --bmc1_ucm_cone_mode                    none
% 2.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.00  --bmc1_ucm_relax_model                  4
% 2.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.00  --bmc1_ucm_layered_model                none
% 2.18/1.00  --bmc1_ucm_max_lemma_size               10
% 2.18/1.00  
% 2.18/1.00  ------ AIG Options
% 2.18/1.00  
% 2.18/1.00  --aig_mode                              false
% 2.18/1.00  
% 2.18/1.00  ------ Instantiation Options
% 2.18/1.00  
% 2.18/1.00  --instantiation_flag                    true
% 2.18/1.00  --inst_sos_flag                         false
% 2.18/1.00  --inst_sos_phase                        true
% 2.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel_side                     num_symb
% 2.18/1.00  --inst_solver_per_active                1400
% 2.18/1.00  --inst_solver_calls_frac                1.
% 2.18/1.00  --inst_passive_queue_type               priority_queues
% 2.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.00  --inst_passive_queues_freq              [25;2]
% 2.18/1.00  --inst_dismatching                      true
% 2.18/1.00  --inst_eager_unprocessed_to_passive     true
% 2.18/1.00  --inst_prop_sim_given                   true
% 2.18/1.00  --inst_prop_sim_new                     false
% 2.18/1.00  --inst_subs_new                         false
% 2.18/1.00  --inst_eq_res_simp                      false
% 2.18/1.00  --inst_subs_given                       false
% 2.18/1.00  --inst_orphan_elimination               true
% 2.18/1.00  --inst_learning_loop_flag               true
% 2.18/1.00  --inst_learning_start                   3000
% 2.18/1.00  --inst_learning_factor                  2
% 2.18/1.00  --inst_start_prop_sim_after_learn       3
% 2.18/1.00  --inst_sel_renew                        solver
% 2.18/1.00  --inst_lit_activity_flag                true
% 2.18/1.00  --inst_restr_to_given                   false
% 2.18/1.00  --inst_activity_threshold               500
% 2.18/1.00  --inst_out_proof                        true
% 2.18/1.00  
% 2.18/1.00  ------ Resolution Options
% 2.18/1.00  
% 2.18/1.00  --resolution_flag                       true
% 2.18/1.00  --res_lit_sel                           adaptive
% 2.18/1.00  --res_lit_sel_side                      none
% 2.18/1.00  --res_ordering                          kbo
% 2.18/1.00  --res_to_prop_solver                    active
% 2.18/1.00  --res_prop_simpl_new                    false
% 2.18/1.00  --res_prop_simpl_given                  true
% 2.18/1.00  --res_passive_queue_type                priority_queues
% 2.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.00  --res_passive_queues_freq               [15;5]
% 2.18/1.00  --res_forward_subs                      full
% 2.18/1.00  --res_backward_subs                     full
% 2.18/1.00  --res_forward_subs_resolution           true
% 2.18/1.00  --res_backward_subs_resolution          true
% 2.18/1.00  --res_orphan_elimination                true
% 2.18/1.00  --res_time_limit                        2.
% 2.18/1.00  --res_out_proof                         true
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Options
% 2.18/1.00  
% 2.18/1.00  --superposition_flag                    true
% 2.18/1.00  --sup_passive_queue_type                priority_queues
% 2.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.00  --demod_completeness_check              fast
% 2.18/1.00  --demod_use_ground                      true
% 2.18/1.00  --sup_to_prop_solver                    passive
% 2.18/1.00  --sup_prop_simpl_new                    true
% 2.18/1.00  --sup_prop_simpl_given                  true
% 2.18/1.00  --sup_fun_splitting                     false
% 2.18/1.00  --sup_smt_interval                      50000
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Simplification Setup
% 2.18/1.00  
% 2.18/1.00  --sup_indices_passive                   []
% 2.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_full_bw                           [BwDemod]
% 2.18/1.00  --sup_immed_triv                        [TrivRules]
% 2.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_immed_bw_main                     []
% 2.18/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.00  
% 2.18/1.00  ------ Combination Options
% 2.18/1.00  
% 2.18/1.00  --comb_res_mult                         3
% 2.18/1.00  --comb_sup_mult                         2
% 2.18/1.00  --comb_inst_mult                        10
% 2.18/1.00  
% 2.18/1.00  ------ Debug Options
% 2.18/1.00  
% 2.18/1.00  --dbg_backtrace                         false
% 2.18/1.00  --dbg_dump_prop_clauses                 false
% 2.18/1.00  --dbg_dump_prop_clauses_file            -
% 2.18/1.00  --dbg_out_stat                          false
% 2.18/1.00  ------ Parsing...
% 2.18/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.00  ------ Proving...
% 2.18/1.00  ------ Problem Properties 
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  clauses                                 19
% 2.18/1.00  conjectures                             5
% 2.18/1.00  EPR                                     6
% 2.18/1.00  Horn                                    13
% 2.18/1.00  unary                                   5
% 2.18/1.00  binary                                  5
% 2.18/1.00  lits                                    44
% 2.18/1.00  lits eq                                 4
% 2.18/1.00  fd_pure                                 0
% 2.18/1.00  fd_pseudo                               0
% 2.18/1.00  fd_cond                                 0
% 2.18/1.00  fd_pseudo_cond                          0
% 2.18/1.00  AC symbols                              0
% 2.18/1.00  
% 2.18/1.00  ------ Schedule dynamic 5 is on 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.00  
% 2.18/1.00  
% 2.18/1.00  ------ 
% 2.18/1.00  Current options:
% 2.18/1.00  ------ 
% 2.18/1.00  
% 2.18/1.00  ------ Input Options
% 2.18/1.00  
% 2.18/1.00  --out_options                           all
% 2.18/1.00  --tptp_safe_out                         true
% 2.18/1.00  --problem_path                          ""
% 2.18/1.00  --include_path                          ""
% 2.18/1.00  --clausifier                            res/vclausify_rel
% 2.18/1.00  --clausifier_options                    --mode clausify
% 2.18/1.00  --stdin                                 false
% 2.18/1.00  --stats_out                             all
% 2.18/1.00  
% 2.18/1.00  ------ General Options
% 2.18/1.00  
% 2.18/1.00  --fof                                   false
% 2.18/1.00  --time_out_real                         305.
% 2.18/1.00  --time_out_virtual                      -1.
% 2.18/1.00  --symbol_type_check                     false
% 2.18/1.00  --clausify_out                          false
% 2.18/1.00  --sig_cnt_out                           false
% 2.18/1.00  --trig_cnt_out                          false
% 2.18/1.00  --trig_cnt_out_tolerance                1.
% 2.18/1.00  --trig_cnt_out_sk_spl                   false
% 2.18/1.00  --abstr_cl_out                          false
% 2.18/1.00  
% 2.18/1.00  ------ Global Options
% 2.18/1.00  
% 2.18/1.00  --schedule                              default
% 2.18/1.00  --add_important_lit                     false
% 2.18/1.00  --prop_solver_per_cl                    1000
% 2.18/1.00  --min_unsat_core                        false
% 2.18/1.00  --soft_assumptions                      false
% 2.18/1.00  --soft_lemma_size                       3
% 2.18/1.00  --prop_impl_unit_size                   0
% 2.18/1.00  --prop_impl_unit                        []
% 2.18/1.00  --share_sel_clauses                     true
% 2.18/1.00  --reset_solvers                         false
% 2.18/1.00  --bc_imp_inh                            [conj_cone]
% 2.18/1.00  --conj_cone_tolerance                   3.
% 2.18/1.00  --extra_neg_conj                        none
% 2.18/1.00  --large_theory_mode                     true
% 2.18/1.00  --prolific_symb_bound                   200
% 2.18/1.00  --lt_threshold                          2000
% 2.18/1.00  --clause_weak_htbl                      true
% 2.18/1.00  --gc_record_bc_elim                     false
% 2.18/1.00  
% 2.18/1.00  ------ Preprocessing Options
% 2.18/1.00  
% 2.18/1.00  --preprocessing_flag                    true
% 2.18/1.00  --time_out_prep_mult                    0.1
% 2.18/1.00  --splitting_mode                        input
% 2.18/1.00  --splitting_grd                         true
% 2.18/1.00  --splitting_cvd                         false
% 2.18/1.00  --splitting_cvd_svl                     false
% 2.18/1.00  --splitting_nvd                         32
% 2.18/1.00  --sub_typing                            true
% 2.18/1.00  --prep_gs_sim                           true
% 2.18/1.00  --prep_unflatten                        true
% 2.18/1.00  --prep_res_sim                          true
% 2.18/1.00  --prep_upred                            true
% 2.18/1.00  --prep_sem_filter                       exhaustive
% 2.18/1.00  --prep_sem_filter_out                   false
% 2.18/1.00  --pred_elim                             true
% 2.18/1.00  --res_sim_input                         true
% 2.18/1.00  --eq_ax_congr_red                       true
% 2.18/1.00  --pure_diseq_elim                       true
% 2.18/1.00  --brand_transform                       false
% 2.18/1.00  --non_eq_to_eq                          false
% 2.18/1.00  --prep_def_merge                        true
% 2.18/1.00  --prep_def_merge_prop_impl              false
% 2.18/1.00  --prep_def_merge_mbd                    true
% 2.18/1.00  --prep_def_merge_tr_red                 false
% 2.18/1.00  --prep_def_merge_tr_cl                  false
% 2.18/1.00  --smt_preprocessing                     true
% 2.18/1.00  --smt_ac_axioms                         fast
% 2.18/1.00  --preprocessed_out                      false
% 2.18/1.00  --preprocessed_stats                    false
% 2.18/1.00  
% 2.18/1.00  ------ Abstraction refinement Options
% 2.18/1.00  
% 2.18/1.00  --abstr_ref                             []
% 2.18/1.00  --abstr_ref_prep                        false
% 2.18/1.00  --abstr_ref_until_sat                   false
% 2.18/1.00  --abstr_ref_sig_restrict                funpre
% 2.18/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.00  --abstr_ref_under                       []
% 2.18/1.00  
% 2.18/1.00  ------ SAT Options
% 2.18/1.00  
% 2.18/1.00  --sat_mode                              false
% 2.18/1.00  --sat_fm_restart_options                ""
% 2.18/1.00  --sat_gr_def                            false
% 2.18/1.00  --sat_epr_types                         true
% 2.18/1.00  --sat_non_cyclic_types                  false
% 2.18/1.00  --sat_finite_models                     false
% 2.18/1.00  --sat_fm_lemmas                         false
% 2.18/1.00  --sat_fm_prep                           false
% 2.18/1.00  --sat_fm_uc_incr                        true
% 2.18/1.00  --sat_out_model                         small
% 2.18/1.00  --sat_out_clauses                       false
% 2.18/1.00  
% 2.18/1.00  ------ QBF Options
% 2.18/1.00  
% 2.18/1.00  --qbf_mode                              false
% 2.18/1.00  --qbf_elim_univ                         false
% 2.18/1.00  --qbf_dom_inst                          none
% 2.18/1.00  --qbf_dom_pre_inst                      false
% 2.18/1.00  --qbf_sk_in                             false
% 2.18/1.00  --qbf_pred_elim                         true
% 2.18/1.00  --qbf_split                             512
% 2.18/1.00  
% 2.18/1.00  ------ BMC1 Options
% 2.18/1.00  
% 2.18/1.00  --bmc1_incremental                      false
% 2.18/1.00  --bmc1_axioms                           reachable_all
% 2.18/1.00  --bmc1_min_bound                        0
% 2.18/1.00  --bmc1_max_bound                        -1
% 2.18/1.00  --bmc1_max_bound_default                -1
% 2.18/1.00  --bmc1_symbol_reachability              true
% 2.18/1.00  --bmc1_property_lemmas                  false
% 2.18/1.00  --bmc1_k_induction                      false
% 2.18/1.00  --bmc1_non_equiv_states                 false
% 2.18/1.00  --bmc1_deadlock                         false
% 2.18/1.00  --bmc1_ucm                              false
% 2.18/1.00  --bmc1_add_unsat_core                   none
% 2.18/1.00  --bmc1_unsat_core_children              false
% 2.18/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.00  --bmc1_out_stat                         full
% 2.18/1.00  --bmc1_ground_init                      false
% 2.18/1.00  --bmc1_pre_inst_next_state              false
% 2.18/1.00  --bmc1_pre_inst_state                   false
% 2.18/1.00  --bmc1_pre_inst_reach_state             false
% 2.18/1.00  --bmc1_out_unsat_core                   false
% 2.18/1.00  --bmc1_aig_witness_out                  false
% 2.18/1.00  --bmc1_verbose                          false
% 2.18/1.00  --bmc1_dump_clauses_tptp                false
% 2.18/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.00  --bmc1_dump_file                        -
% 2.18/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.00  --bmc1_ucm_extend_mode                  1
% 2.18/1.00  --bmc1_ucm_init_mode                    2
% 2.18/1.00  --bmc1_ucm_cone_mode                    none
% 2.18/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.00  --bmc1_ucm_relax_model                  4
% 2.18/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.00  --bmc1_ucm_layered_model                none
% 2.18/1.00  --bmc1_ucm_max_lemma_size               10
% 2.18/1.00  
% 2.18/1.00  ------ AIG Options
% 2.18/1.00  
% 2.18/1.00  --aig_mode                              false
% 2.18/1.00  
% 2.18/1.00  ------ Instantiation Options
% 2.18/1.00  
% 2.18/1.00  --instantiation_flag                    true
% 2.18/1.00  --inst_sos_flag                         false
% 2.18/1.00  --inst_sos_phase                        true
% 2.18/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.00  --inst_lit_sel_side                     none
% 2.18/1.00  --inst_solver_per_active                1400
% 2.18/1.00  --inst_solver_calls_frac                1.
% 2.18/1.00  --inst_passive_queue_type               priority_queues
% 2.18/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.00  --inst_passive_queues_freq              [25;2]
% 2.18/1.00  --inst_dismatching                      true
% 2.18/1.00  --inst_eager_unprocessed_to_passive     true
% 2.18/1.00  --inst_prop_sim_given                   true
% 2.18/1.00  --inst_prop_sim_new                     false
% 2.18/1.00  --inst_subs_new                         false
% 2.18/1.00  --inst_eq_res_simp                      false
% 2.18/1.00  --inst_subs_given                       false
% 2.18/1.00  --inst_orphan_elimination               true
% 2.18/1.00  --inst_learning_loop_flag               true
% 2.18/1.00  --inst_learning_start                   3000
% 2.18/1.00  --inst_learning_factor                  2
% 2.18/1.00  --inst_start_prop_sim_after_learn       3
% 2.18/1.00  --inst_sel_renew                        solver
% 2.18/1.00  --inst_lit_activity_flag                true
% 2.18/1.00  --inst_restr_to_given                   false
% 2.18/1.00  --inst_activity_threshold               500
% 2.18/1.00  --inst_out_proof                        true
% 2.18/1.00  
% 2.18/1.00  ------ Resolution Options
% 2.18/1.00  
% 2.18/1.00  --resolution_flag                       false
% 2.18/1.00  --res_lit_sel                           adaptive
% 2.18/1.00  --res_lit_sel_side                      none
% 2.18/1.00  --res_ordering                          kbo
% 2.18/1.00  --res_to_prop_solver                    active
% 2.18/1.00  --res_prop_simpl_new                    false
% 2.18/1.00  --res_prop_simpl_given                  true
% 2.18/1.00  --res_passive_queue_type                priority_queues
% 2.18/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.00  --res_passive_queues_freq               [15;5]
% 2.18/1.00  --res_forward_subs                      full
% 2.18/1.00  --res_backward_subs                     full
% 2.18/1.00  --res_forward_subs_resolution           true
% 2.18/1.00  --res_backward_subs_resolution          true
% 2.18/1.00  --res_orphan_elimination                true
% 2.18/1.00  --res_time_limit                        2.
% 2.18/1.00  --res_out_proof                         true
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Options
% 2.18/1.00  
% 2.18/1.00  --superposition_flag                    true
% 2.18/1.00  --sup_passive_queue_type                priority_queues
% 2.18/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.00  --demod_completeness_check              fast
% 2.18/1.00  --demod_use_ground                      true
% 2.18/1.00  --sup_to_prop_solver                    passive
% 2.18/1.00  --sup_prop_simpl_new                    true
% 2.18/1.00  --sup_prop_simpl_given                  true
% 2.18/1.00  --sup_fun_splitting                     false
% 2.18/1.00  --sup_smt_interval                      50000
% 2.18/1.00  
% 2.18/1.00  ------ Superposition Simplification Setup
% 2.18/1.00  
% 2.18/1.00  --sup_indices_passive                   []
% 2.18/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.00  --sup_full_bw                           [BwDemod]
% 2.18/1.00  --sup_immed_triv                        [TrivRules]
% 2.18/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ Proving...
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS status Theorem for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  fof(f4,axiom,(
% 2.18/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f28,plain,(
% 2.18/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/1.01    inference(nnf_transformation,[],[f4])).
% 2.18/1.01  
% 2.18/1.01  fof(f42,plain,(
% 2.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f28])).
% 2.18/1.01  
% 2.18/1.01  fof(f9,conjecture,(
% 2.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f10,negated_conjecture,(
% 2.18/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.18/1.01    inference(negated_conjecture,[],[f9])).
% 2.18/1.01  
% 2.18/1.01  fof(f22,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f10])).
% 2.18/1.01  
% 2.18/1.01  fof(f23,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.18/1.01    inference(flattening,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f35,plain,(
% 2.18/1.01    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f34,plain,(
% 2.18/1.01    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f33,plain,(
% 2.18/1.01    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f36,plain,(
% 2.18/1.01    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f23,f35,f34,f33])).
% 2.18/1.01  
% 2.18/1.01  fof(f57,plain,(
% 2.18/1.01    r2_hidden(sK4,sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f2,axiom,(
% 2.18/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f12,plain,(
% 2.18/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.18/1.01    inference(ennf_transformation,[],[f2])).
% 2.18/1.01  
% 2.18/1.01  fof(f40,plain,(
% 2.18/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f12])).
% 2.18/1.01  
% 2.18/1.01  fof(f7,axiom,(
% 2.18/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f18,plain,(
% 2.18/1.01    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f7])).
% 2.18/1.01  
% 2.18/1.01  fof(f19,plain,(
% 2.18/1.01    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.18/1.01    inference(flattening,[],[f18])).
% 2.18/1.01  
% 2.18/1.01  fof(f46,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f19])).
% 2.18/1.01  
% 2.18/1.01  fof(f1,axiom,(
% 2.18/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f11,plain,(
% 2.18/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f1])).
% 2.18/1.01  
% 2.18/1.01  fof(f24,plain,(
% 2.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.18/1.01    inference(nnf_transformation,[],[f11])).
% 2.18/1.01  
% 2.18/1.01  fof(f25,plain,(
% 2.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.18/1.01    inference(rectify,[],[f24])).
% 2.18/1.01  
% 2.18/1.01  fof(f26,plain,(
% 2.18/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f27,plain,(
% 2.18/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 2.18/1.01  
% 2.18/1.01  fof(f38,plain,(
% 2.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f27])).
% 2.18/1.01  
% 2.18/1.01  fof(f39,plain,(
% 2.18/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f27])).
% 2.18/1.01  
% 2.18/1.01  fof(f5,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f15,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.18/1.01    inference(ennf_transformation,[],[f5])).
% 2.18/1.01  
% 2.18/1.01  fof(f44,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f15])).
% 2.18/1.01  
% 2.18/1.01  fof(f43,plain,(
% 2.18/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f28])).
% 2.18/1.01  
% 2.18/1.01  fof(f6,axiom,(
% 2.18/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f16,plain,(
% 2.18/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f6])).
% 2.18/1.01  
% 2.18/1.01  fof(f17,plain,(
% 2.18/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.18/1.01    inference(flattening,[],[f16])).
% 2.18/1.01  
% 2.18/1.01  fof(f45,plain,(
% 2.18/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f17])).
% 2.18/1.01  
% 2.18/1.01  fof(f8,axiom,(
% 2.18/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.18/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f20,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.18/1.01    inference(ennf_transformation,[],[f8])).
% 2.18/1.01  
% 2.18/1.01  fof(f21,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.01    inference(flattening,[],[f20])).
% 2.18/1.01  
% 2.18/1.01  fof(f29,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.01    inference(nnf_transformation,[],[f21])).
% 2.18/1.01  
% 2.18/1.01  fof(f30,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.01    inference(rectify,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f31,plain,(
% 2.18/1.01    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f32,plain,(
% 2.18/1.01    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 2.18/1.01  
% 2.18/1.01  fof(f47,plain,(
% 2.18/1.01    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f32])).
% 2.18/1.01  
% 2.18/1.01  fof(f53,plain,(
% 2.18/1.01    l1_pre_topc(sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f51,plain,(
% 2.18/1.01    ~v2_struct_0(sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f52,plain,(
% 2.18/1.01    v2_pre_topc(sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f56,plain,(
% 2.18/1.01    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f54,plain,(
% 2.18/1.01    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f58,plain,(
% 2.18/1.01    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f55,plain,(
% 2.18/1.01    v2_tex_2(sK3,sK2)),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f42]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2101,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) | r1_tarski(X0,sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_6]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_4186,plain,
% 2.18/1.01      ( ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3))
% 2.18/1.01      | r1_tarski(k1_tarski(sK4),sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2101]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_15,negated_conjecture,
% 2.18/1.01      ( r2_hidden(sK4,sK3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1840,plain,
% 2.18/1.01      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3,plain,
% 2.18/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f40]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1846,plain,
% 2.18/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.18/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2225,plain,
% 2.18/1.01      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1840,c_1846]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_9,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,X1)
% 2.18/1.01      | v1_xboole_0(X1)
% 2.18/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1841,plain,
% 2.18/1.01      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.18/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.18/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2914,plain,
% 2.18/1.01      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
% 2.18/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2225,c_1841]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_28,plain,
% 2.18/1.01      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1987,plain,
% 2.18/1.01      ( m1_subset_1(sK4,sK3) | ~ r2_hidden(sK4,sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1988,plain,
% 2.18/1.01      ( m1_subset_1(sK4,sK3) = iProver_top
% 2.18/1.01      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1987]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2061,plain,
% 2.18/1.01      ( ~ m1_subset_1(sK4,sK3)
% 2.18/1.01      | v1_xboole_0(sK3)
% 2.18/1.01      | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2066,plain,
% 2.18/1.01      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
% 2.18/1.01      | m1_subset_1(sK4,sK3) != iProver_top
% 2.18/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_2061]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1,plain,
% 2.18/1.01      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f38]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1848,plain,
% 2.18/1.01      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 2.18/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_0,plain,
% 2.18/1.01      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f39]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1849,plain,
% 2.18/1.01      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 2.18/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2789,plain,
% 2.18/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1848,c_1849]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_7,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.18/1.01      | ~ r2_hidden(X2,X0)
% 2.18/1.01      | ~ v1_xboole_0(X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_5,plain,
% 2.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_160,plain,
% 2.18/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.18/1.01      inference(prop_impl,[status(thm)],[c_5]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_161,plain,
% 2.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_160]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_201,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 2.18/1.01      inference(bin_hyper_res,[status(thm)],[c_7,c_161]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1836,plain,
% 2.18/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.18/1.01      | r1_tarski(X1,X2) != iProver_top
% 2.18/1.01      | v1_xboole_0(X2) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_201]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2725,plain,
% 2.18/1.01      ( r1_tarski(sK3,X0) != iProver_top
% 2.18/1.01      | v1_xboole_0(X0) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1840,c_1836]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3552,plain,
% 2.18/1.01      ( v1_xboole_0(sK3) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2789,c_2725]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3569,plain,
% 2.18/1.01      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2914,c_28,c_1988,c_2066,c_3552]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_8,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,X1)
% 2.18/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.18/1.01      | v1_xboole_0(X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1842,plain,
% 2.18/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.18/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.18/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3572,plain,
% 2.18/1.01      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.18/1.01      | m1_subset_1(sK4,sK3) != iProver_top
% 2.18/1.01      | v1_xboole_0(sK3) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_3569,c_1842]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3573,plain,
% 2.18/1.01      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3))
% 2.18/1.01      | ~ m1_subset_1(sK4,sK3)
% 2.18/1.01      | v1_xboole_0(sK3) ),
% 2.18/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3572]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3567,plain,
% 2.18/1.01      ( ~ v1_xboole_0(sK3) ),
% 2.18/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3552]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_13,plain,
% 2.18/1.01      ( ~ v2_tex_2(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.01      | ~ r1_tarski(X2,X0)
% 2.18/1.01      | v2_struct_0(X1)
% 2.18/1.01      | ~ v2_pre_topc(X1)
% 2.18/1.01      | ~ l1_pre_topc(X1)
% 2.18/1.01      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.18/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_19,negated_conjecture,
% 2.18/1.01      ( l1_pre_topc(sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_346,plain,
% 2.18/1.01      ( ~ v2_tex_2(X0,X1)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.18/1.01      | ~ r1_tarski(X2,X0)
% 2.18/1.01      | v2_struct_0(X1)
% 2.18/1.01      | ~ v2_pre_topc(X1)
% 2.18/1.01      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.18/1.01      | sK2 != X1 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_347,plain,
% 2.18/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.18/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ r1_tarski(X1,X0)
% 2.18/1.01      | v2_struct_0(sK2)
% 2.18/1.01      | ~ v2_pre_topc(sK2)
% 2.18/1.01      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_346]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_21,negated_conjecture,
% 2.18/1.01      ( ~ v2_struct_0(sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_20,negated_conjecture,
% 2.18/1.01      ( v2_pre_topc(sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_351,plain,
% 2.18/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.18/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ r1_tarski(X1,X0)
% 2.18/1.01      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_347,c_21,c_20]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_352,plain,
% 2.18/1.01      ( ~ v2_tex_2(X0,sK2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ r1_tarski(X1,X0)
% 2.18/1.01      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_351]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1981,plain,
% 2.18/1.01      ( ~ v2_tex_2(sK3,sK2)
% 2.18/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ r1_tarski(X0,sK3)
% 2.18/1.01      | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_352]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3488,plain,
% 2.18/1.01      ( ~ v2_tex_2(sK3,sK2)
% 2.18/1.01      | ~ m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ r1_tarski(k1_tarski(sK4),sK3)
% 2.18/1.01      | k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1981]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_16,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1839,plain,
% 2.18/1.01      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2911,plain,
% 2.18/1.01      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
% 2.18/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1839,c_1841]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2027,plain,
% 2.18/1.01      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.18/1.01      | v1_xboole_0(u1_struct_0(sK2))
% 2.18/1.01      | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_18,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1837,plain,
% 2.18/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1843,plain,
% 2.18/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.18/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2261,plain,
% 2.18/1.01      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1837,c_1843]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2262,plain,
% 2.18/1.01      ( r1_tarski(sK3,u1_struct_0(sK2)) ),
% 2.18/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2261]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2072,plain,
% 2.18/1.01      ( ~ r2_hidden(X0,X1)
% 2.18/1.01      | ~ r1_tarski(X1,u1_struct_0(sK2))
% 2.18/1.01      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_201]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2477,plain,
% 2.18/1.01      ( ~ r2_hidden(sK4,sK3)
% 2.18/1.01      | ~ r1_tarski(sK3,u1_struct_0(sK2))
% 2.18/1.01      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_2072]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3194,plain,
% 2.18/1.01      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2911,c_16,c_15,c_2027,c_2262,c_2477]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3372,plain,
% 2.18/1.01      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.18/1.01      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.18/1.01      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_3194,c_1842]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3450,plain,
% 2.18/1.01      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 2.18/1.01      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.18/1.01      | v1_xboole_0(u1_struct_0(sK2)) ),
% 2.18/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3372]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_14,negated_conjecture,
% 2.18/1.01      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3197,plain,
% 2.18/1.01      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_3194,c_14]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_17,negated_conjecture,
% 2.18/1.01      ( v2_tex_2(sK3,sK2) ),
% 2.18/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(contradiction,plain,
% 2.18/1.01      ( $false ),
% 2.18/1.01      inference(minisat,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_4186,c_3573,c_3567,c_3488,c_3450,c_3197,c_2477,c_2262,
% 2.18/1.01                 c_1987,c_15,c_16,c_17,c_18]) ).
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  ------                               Statistics
% 2.18/1.01  
% 2.18/1.01  ------ General
% 2.18/1.01  
% 2.18/1.01  abstr_ref_over_cycles:                  0
% 2.18/1.01  abstr_ref_under_cycles:                 0
% 2.18/1.01  gc_basic_clause_elim:                   0
% 2.18/1.01  forced_gc_time:                         0
% 2.18/1.01  parsing_time:                           0.011
% 2.18/1.01  unif_index_cands_time:                  0.
% 2.18/1.01  unif_index_add_time:                    0.
% 2.18/1.01  orderings_time:                         0.
% 2.18/1.01  out_proof_time:                         0.008
% 2.18/1.01  total_time:                             0.133
% 2.18/1.01  num_of_symbols:                         50
% 2.18/1.01  num_of_terms:                           2646
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing
% 2.18/1.01  
% 2.18/1.01  num_of_splits:                          0
% 2.18/1.01  num_of_split_atoms:                     0
% 2.18/1.01  num_of_reused_defs:                     0
% 2.18/1.01  num_eq_ax_congr_red:                    19
% 2.18/1.01  num_of_sem_filtered_clauses:            1
% 2.18/1.01  num_of_subtypes:                        0
% 2.18/1.01  monotx_restored_types:                  0
% 2.18/1.01  sat_num_of_epr_types:                   0
% 2.18/1.01  sat_num_of_non_cyclic_types:            0
% 2.18/1.01  sat_guarded_non_collapsed_types:        0
% 2.18/1.01  num_pure_diseq_elim:                    0
% 2.18/1.01  simp_replaced_by:                       0
% 2.18/1.01  res_preprocessed:                       104
% 2.18/1.01  prep_upred:                             0
% 2.18/1.01  prep_unflattend:                        64
% 2.18/1.01  smt_new_axioms:                         0
% 2.18/1.01  pred_elim_cands:                        5
% 2.18/1.01  pred_elim:                              3
% 2.18/1.01  pred_elim_cl:                           3
% 2.18/1.01  pred_elim_cycles:                       9
% 2.18/1.01  merged_defs:                            8
% 2.18/1.01  merged_defs_ncl:                        0
% 2.18/1.01  bin_hyper_res:                          9
% 2.18/1.01  prep_cycles:                            4
% 2.18/1.01  pred_elim_time:                         0.015
% 2.18/1.01  splitting_time:                         0.
% 2.18/1.01  sem_filter_time:                        0.
% 2.18/1.01  monotx_time:                            0.001
% 2.18/1.01  subtype_inf_time:                       0.
% 2.18/1.01  
% 2.18/1.01  ------ Problem properties
% 2.18/1.01  
% 2.18/1.01  clauses:                                19
% 2.18/1.01  conjectures:                            5
% 2.18/1.01  epr:                                    6
% 2.18/1.01  horn:                                   13
% 2.18/1.01  ground:                                 5
% 2.18/1.01  unary:                                  5
% 2.18/1.01  binary:                                 5
% 2.18/1.01  lits:                                   44
% 2.18/1.01  lits_eq:                                4
% 2.18/1.01  fd_pure:                                0
% 2.18/1.01  fd_pseudo:                              0
% 2.18/1.01  fd_cond:                                0
% 2.18/1.01  fd_pseudo_cond:                         0
% 2.18/1.01  ac_symbols:                             0
% 2.18/1.01  
% 2.18/1.01  ------ Propositional Solver
% 2.18/1.01  
% 2.18/1.01  prop_solver_calls:                      29
% 2.18/1.01  prop_fast_solver_calls:                 832
% 2.18/1.01  smt_solver_calls:                       0
% 2.18/1.01  smt_fast_solver_calls:                  0
% 2.18/1.01  prop_num_of_clauses:                    1165
% 2.18/1.01  prop_preprocess_simplified:             4132
% 2.18/1.01  prop_fo_subsumed:                       17
% 2.18/1.01  prop_solver_time:                       0.
% 2.18/1.01  smt_solver_time:                        0.
% 2.18/1.01  smt_fast_solver_time:                   0.
% 2.18/1.01  prop_fast_solver_time:                  0.
% 2.18/1.01  prop_unsat_core_time:                   0.
% 2.18/1.01  
% 2.18/1.01  ------ QBF
% 2.18/1.01  
% 2.18/1.01  qbf_q_res:                              0
% 2.18/1.01  qbf_num_tautologies:                    0
% 2.18/1.01  qbf_prep_cycles:                        0
% 2.18/1.01  
% 2.18/1.01  ------ BMC1
% 2.18/1.01  
% 2.18/1.01  bmc1_current_bound:                     -1
% 2.18/1.01  bmc1_last_solved_bound:                 -1
% 2.18/1.01  bmc1_unsat_core_size:                   -1
% 2.18/1.01  bmc1_unsat_core_parents_size:           -1
% 2.18/1.01  bmc1_merge_next_fun:                    0
% 2.18/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation
% 2.18/1.01  
% 2.18/1.01  inst_num_of_clauses:                    294
% 2.18/1.01  inst_num_in_passive:                    106
% 2.18/1.01  inst_num_in_active:                     163
% 2.18/1.01  inst_num_in_unprocessed:                24
% 2.18/1.01  inst_num_of_loops:                      221
% 2.18/1.01  inst_num_of_learning_restarts:          0
% 2.18/1.01  inst_num_moves_active_passive:          53
% 2.18/1.01  inst_lit_activity:                      0
% 2.18/1.01  inst_lit_activity_moves:                0
% 2.18/1.01  inst_num_tautologies:                   0
% 2.18/1.01  inst_num_prop_implied:                  0
% 2.18/1.01  inst_num_existing_simplified:           0
% 2.18/1.01  inst_num_eq_res_simplified:             0
% 2.18/1.01  inst_num_child_elim:                    0
% 2.18/1.01  inst_num_of_dismatching_blockings:      98
% 2.18/1.01  inst_num_of_non_proper_insts:           287
% 2.18/1.01  inst_num_of_duplicates:                 0
% 2.18/1.01  inst_inst_num_from_inst_to_res:         0
% 2.18/1.01  inst_dismatching_checking_time:         0.
% 2.18/1.01  
% 2.18/1.01  ------ Resolution
% 2.18/1.01  
% 2.18/1.01  res_num_of_clauses:                     0
% 2.18/1.01  res_num_in_passive:                     0
% 2.18/1.01  res_num_in_active:                      0
% 2.18/1.01  res_num_of_loops:                       108
% 2.18/1.01  res_forward_subset_subsumed:            29
% 2.18/1.01  res_backward_subset_subsumed:           0
% 2.18/1.01  res_forward_subsumed:                   0
% 2.18/1.01  res_backward_subsumed:                  0
% 2.18/1.01  res_forward_subsumption_resolution:     0
% 2.18/1.01  res_backward_subsumption_resolution:    0
% 2.18/1.01  res_clause_to_clause_subsumption:       278
% 2.18/1.01  res_orphan_elimination:                 0
% 2.18/1.01  res_tautology_del:                      41
% 2.18/1.01  res_num_eq_res_simplified:              0
% 2.18/1.01  res_num_sel_changes:                    0
% 2.18/1.01  res_moves_from_active_to_pass:          0
% 2.18/1.01  
% 2.18/1.01  ------ Superposition
% 2.18/1.01  
% 2.18/1.01  sup_time_total:                         0.
% 2.18/1.01  sup_time_generating:                    0.
% 2.18/1.01  sup_time_sim_full:                      0.
% 2.18/1.01  sup_time_sim_immed:                     0.
% 2.18/1.01  
% 2.18/1.01  sup_num_of_clauses:                     82
% 2.18/1.01  sup_num_in_active:                      43
% 2.18/1.01  sup_num_in_passive:                     39
% 2.18/1.01  sup_num_of_loops:                       44
% 2.18/1.01  sup_fw_superposition:                   30
% 2.18/1.01  sup_bw_superposition:                   45
% 2.18/1.01  sup_immediate_simplified:               5
% 2.18/1.01  sup_given_eliminated:                   0
% 2.18/1.01  comparisons_done:                       0
% 2.18/1.01  comparisons_avoided:                    0
% 2.18/1.01  
% 2.18/1.01  ------ Simplifications
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  sim_fw_subset_subsumed:                 5
% 2.18/1.01  sim_bw_subset_subsumed:                 1
% 2.18/1.01  sim_fw_subsumed:                        0
% 2.18/1.01  sim_bw_subsumed:                        0
% 2.18/1.01  sim_fw_subsumption_res:                 0
% 2.18/1.01  sim_bw_subsumption_res:                 0
% 2.18/1.01  sim_tautology_del:                      1
% 2.18/1.01  sim_eq_tautology_del:                   0
% 2.18/1.01  sim_eq_res_simp:                        0
% 2.18/1.01  sim_fw_demodulated:                     0
% 2.18/1.01  sim_bw_demodulated:                     1
% 2.18/1.01  sim_light_normalised:                   0
% 2.18/1.01  sim_joinable_taut:                      0
% 2.18/1.01  sim_joinable_simp:                      0
% 2.18/1.01  sim_ac_normalised:                      0
% 2.18/1.01  sim_smt_subsumption:                    0
% 2.18/1.01  
%------------------------------------------------------------------------------
