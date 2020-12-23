%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:33 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 524 expanded)
%              Number of clauses        :   73 ( 164 expanded)
%              Number of leaves         :   14 ( 135 expanded)
%              Depth                    :   17
%              Number of atoms          :  415 (2437 expanded)
%              Number of equality atoms :  110 ( 400 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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

fof(f31,plain,
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

fof(f34,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f33,f32,f31])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f37])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).

fof(f35,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

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
    inference(cnf_transformation,[],[f30])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f51,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1396,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1398,plain,
    ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2766,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1396,c_1398])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1565,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1566,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1565])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_172,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_211,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_172])).

cnf(c_1626,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | r2_hidden(X0,u1_struct_0(sK2))
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_211])).

cnf(c_1791,plain,
    ( ~ r1_tarski(sK3,u1_struct_0(sK2))
    | r2_hidden(sK4,u1_struct_0(sK2))
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1626])).

cnf(c_1792,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
    | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1970,plain,
    ( ~ r2_hidden(sK4,u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1971,plain,
    ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1970])).

cnf(c_3035,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2766,c_26,c_29,c_1566,c_1792,c_1971])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1399,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3210,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3035,c_1399])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3686,plain,
    ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3210,c_26,c_28,c_29,c_1566,c_1792,c_1971])).

cnf(c_1397,plain,
    ( r2_hidden(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_133,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_1])).

cnf(c_134,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_133])).

cnf(c_1393,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_134])).

cnf(c_3185,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1397,c_1393])).

cnf(c_3393,plain,
    ( k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3185,c_1398])).

cnf(c_1552,plain,
    ( ~ r2_hidden(sK4,sK3)
    | ~ v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1770,plain,
    ( m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_134])).

cnf(c_2279,plain,
    ( m1_subset_1(sK4,sK3)
    | ~ r2_hidden(sK4,sK3) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_1610,plain,
    ( ~ m1_subset_1(X0,sK3)
    | v1_xboole_0(sK3)
    | k2_tarski(X0,X0) = k6_domain_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2355,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1610])).

cnf(c_3515,plain,
    ( k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3393,c_16,c_1552,c_2279,c_2355])).

cnf(c_3690,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3686,c_3515])).

cnf(c_1400,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3696,plain,
    ( r1_tarski(k6_domain_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3690,c_1400])).

cnf(c_1394,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1401,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_295,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_20])).

cnf(c_296,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_300,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_22,c_21])).

cnf(c_301,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_300])).

cnf(c_1391,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_301])).

cnf(c_1886,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X1,u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1401,c_1391])).

cnf(c_2222,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1394,c_1886])).

cnf(c_18,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_27,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2264,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
    | r1_tarski(X0,sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2222,c_27])).

cnf(c_3920,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(sK3,sK4))) = k6_domain_1(sK3,sK4)
    | r1_tarski(k6_domain_1(sK3,sK4),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3696,c_2264])).

cnf(c_15,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3038,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != k2_tarski(sK4,sK4) ),
    inference(demodulation,[status(thm)],[c_3035,c_15])).

cnf(c_3518,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(sK3,sK4))) != k6_domain_1(sK3,sK4) ),
    inference(demodulation,[status(thm)],[c_3515,c_3038])).

cnf(c_1828,plain,
    ( r1_tarski(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_3031,plain,
    ( r1_tarski(k6_domain_1(sK3,sK4),sK3)
    | ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1828])).

cnf(c_3032,plain,
    ( r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top
    | m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3031])).

cnf(c_1611,plain,
    ( ~ m1_subset_1(X0,sK3)
    | m1_subset_1(k6_domain_1(sK3,X0),k1_zfmisc_1(sK3))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2357,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
    | ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1611])).

cnf(c_2358,plain,
    ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2357])).

cnf(c_2280,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top
    | r2_hidden(sK4,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2279])).

cnf(c_1553,plain,
    ( r2_hidden(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1552])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3920,c_3518,c_3032,c_2358,c_2280,c_1553,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.40/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.05  
% 2.40/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.40/1.05  
% 2.40/1.05  ------  iProver source info
% 2.40/1.05  
% 2.40/1.05  git: date: 2020-06-30 10:37:57 +0100
% 2.40/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.40/1.05  git: non_committed_changes: false
% 2.40/1.05  git: last_make_outside_of_git: false
% 2.40/1.05  
% 2.40/1.05  ------ 
% 2.40/1.05  
% 2.40/1.05  ------ Input Options
% 2.40/1.05  
% 2.40/1.05  --out_options                           all
% 2.40/1.05  --tptp_safe_out                         true
% 2.40/1.05  --problem_path                          ""
% 2.40/1.05  --include_path                          ""
% 2.40/1.05  --clausifier                            res/vclausify_rel
% 2.40/1.05  --clausifier_options                    --mode clausify
% 2.40/1.05  --stdin                                 false
% 2.40/1.05  --stats_out                             all
% 2.40/1.05  
% 2.40/1.05  ------ General Options
% 2.40/1.05  
% 2.40/1.05  --fof                                   false
% 2.40/1.05  --time_out_real                         305.
% 2.40/1.05  --time_out_virtual                      -1.
% 2.40/1.05  --symbol_type_check                     false
% 2.40/1.05  --clausify_out                          false
% 2.40/1.05  --sig_cnt_out                           false
% 2.40/1.05  --trig_cnt_out                          false
% 2.40/1.05  --trig_cnt_out_tolerance                1.
% 2.40/1.05  --trig_cnt_out_sk_spl                   false
% 2.40/1.05  --abstr_cl_out                          false
% 2.40/1.05  
% 2.40/1.05  ------ Global Options
% 2.40/1.05  
% 2.40/1.05  --schedule                              default
% 2.40/1.05  --add_important_lit                     false
% 2.40/1.05  --prop_solver_per_cl                    1000
% 2.40/1.05  --min_unsat_core                        false
% 2.40/1.05  --soft_assumptions                      false
% 2.40/1.05  --soft_lemma_size                       3
% 2.40/1.05  --prop_impl_unit_size                   0
% 2.40/1.05  --prop_impl_unit                        []
% 2.40/1.05  --share_sel_clauses                     true
% 2.40/1.05  --reset_solvers                         false
% 2.40/1.05  --bc_imp_inh                            [conj_cone]
% 2.40/1.05  --conj_cone_tolerance                   3.
% 2.40/1.05  --extra_neg_conj                        none
% 2.40/1.05  --large_theory_mode                     true
% 2.40/1.05  --prolific_symb_bound                   200
% 2.40/1.05  --lt_threshold                          2000
% 2.40/1.05  --clause_weak_htbl                      true
% 2.40/1.05  --gc_record_bc_elim                     false
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing Options
% 2.40/1.05  
% 2.40/1.05  --preprocessing_flag                    true
% 2.40/1.05  --time_out_prep_mult                    0.1
% 2.40/1.05  --splitting_mode                        input
% 2.40/1.05  --splitting_grd                         true
% 2.40/1.05  --splitting_cvd                         false
% 2.40/1.05  --splitting_cvd_svl                     false
% 2.40/1.05  --splitting_nvd                         32
% 2.40/1.05  --sub_typing                            true
% 2.40/1.05  --prep_gs_sim                           true
% 2.40/1.05  --prep_unflatten                        true
% 2.40/1.05  --prep_res_sim                          true
% 2.40/1.05  --prep_upred                            true
% 2.40/1.05  --prep_sem_filter                       exhaustive
% 2.40/1.05  --prep_sem_filter_out                   false
% 2.40/1.05  --pred_elim                             true
% 2.40/1.05  --res_sim_input                         true
% 2.40/1.05  --eq_ax_congr_red                       true
% 2.40/1.05  --pure_diseq_elim                       true
% 2.40/1.05  --brand_transform                       false
% 2.40/1.05  --non_eq_to_eq                          false
% 2.40/1.05  --prep_def_merge                        true
% 2.40/1.05  --prep_def_merge_prop_impl              false
% 2.40/1.05  --prep_def_merge_mbd                    true
% 2.40/1.05  --prep_def_merge_tr_red                 false
% 2.40/1.05  --prep_def_merge_tr_cl                  false
% 2.40/1.05  --smt_preprocessing                     true
% 2.40/1.05  --smt_ac_axioms                         fast
% 2.40/1.05  --preprocessed_out                      false
% 2.40/1.05  --preprocessed_stats                    false
% 2.40/1.05  
% 2.40/1.05  ------ Abstraction refinement Options
% 2.40/1.05  
% 2.40/1.05  --abstr_ref                             []
% 2.40/1.05  --abstr_ref_prep                        false
% 2.40/1.05  --abstr_ref_until_sat                   false
% 2.40/1.05  --abstr_ref_sig_restrict                funpre
% 2.40/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.05  --abstr_ref_under                       []
% 2.40/1.05  
% 2.40/1.05  ------ SAT Options
% 2.40/1.05  
% 2.40/1.05  --sat_mode                              false
% 2.40/1.05  --sat_fm_restart_options                ""
% 2.40/1.05  --sat_gr_def                            false
% 2.40/1.05  --sat_epr_types                         true
% 2.40/1.05  --sat_non_cyclic_types                  false
% 2.40/1.05  --sat_finite_models                     false
% 2.40/1.05  --sat_fm_lemmas                         false
% 2.40/1.05  --sat_fm_prep                           false
% 2.40/1.05  --sat_fm_uc_incr                        true
% 2.40/1.05  --sat_out_model                         small
% 2.40/1.05  --sat_out_clauses                       false
% 2.40/1.05  
% 2.40/1.05  ------ QBF Options
% 2.40/1.05  
% 2.40/1.05  --qbf_mode                              false
% 2.40/1.05  --qbf_elim_univ                         false
% 2.40/1.05  --qbf_dom_inst                          none
% 2.40/1.05  --qbf_dom_pre_inst                      false
% 2.40/1.05  --qbf_sk_in                             false
% 2.40/1.05  --qbf_pred_elim                         true
% 2.40/1.05  --qbf_split                             512
% 2.40/1.05  
% 2.40/1.05  ------ BMC1 Options
% 2.40/1.05  
% 2.40/1.05  --bmc1_incremental                      false
% 2.40/1.05  --bmc1_axioms                           reachable_all
% 2.40/1.05  --bmc1_min_bound                        0
% 2.40/1.05  --bmc1_max_bound                        -1
% 2.40/1.05  --bmc1_max_bound_default                -1
% 2.40/1.05  --bmc1_symbol_reachability              true
% 2.40/1.05  --bmc1_property_lemmas                  false
% 2.40/1.05  --bmc1_k_induction                      false
% 2.40/1.05  --bmc1_non_equiv_states                 false
% 2.40/1.05  --bmc1_deadlock                         false
% 2.40/1.05  --bmc1_ucm                              false
% 2.40/1.05  --bmc1_add_unsat_core                   none
% 2.40/1.05  --bmc1_unsat_core_children              false
% 2.40/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.05  --bmc1_out_stat                         full
% 2.40/1.05  --bmc1_ground_init                      false
% 2.40/1.05  --bmc1_pre_inst_next_state              false
% 2.40/1.05  --bmc1_pre_inst_state                   false
% 2.40/1.05  --bmc1_pre_inst_reach_state             false
% 2.40/1.05  --bmc1_out_unsat_core                   false
% 2.40/1.05  --bmc1_aig_witness_out                  false
% 2.40/1.05  --bmc1_verbose                          false
% 2.40/1.05  --bmc1_dump_clauses_tptp                false
% 2.40/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.05  --bmc1_dump_file                        -
% 2.40/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.05  --bmc1_ucm_extend_mode                  1
% 2.40/1.05  --bmc1_ucm_init_mode                    2
% 2.40/1.05  --bmc1_ucm_cone_mode                    none
% 2.40/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.05  --bmc1_ucm_relax_model                  4
% 2.40/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.05  --bmc1_ucm_layered_model                none
% 2.40/1.05  --bmc1_ucm_max_lemma_size               10
% 2.40/1.05  
% 2.40/1.05  ------ AIG Options
% 2.40/1.05  
% 2.40/1.05  --aig_mode                              false
% 2.40/1.05  
% 2.40/1.05  ------ Instantiation Options
% 2.40/1.05  
% 2.40/1.05  --instantiation_flag                    true
% 2.40/1.05  --inst_sos_flag                         false
% 2.40/1.05  --inst_sos_phase                        true
% 2.40/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.05  --inst_lit_sel_side                     num_symb
% 2.40/1.05  --inst_solver_per_active                1400
% 2.40/1.05  --inst_solver_calls_frac                1.
% 2.40/1.05  --inst_passive_queue_type               priority_queues
% 2.40/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.05  --inst_passive_queues_freq              [25;2]
% 2.40/1.05  --inst_dismatching                      true
% 2.40/1.05  --inst_eager_unprocessed_to_passive     true
% 2.40/1.05  --inst_prop_sim_given                   true
% 2.40/1.05  --inst_prop_sim_new                     false
% 2.40/1.05  --inst_subs_new                         false
% 2.40/1.05  --inst_eq_res_simp                      false
% 2.40/1.05  --inst_subs_given                       false
% 2.40/1.05  --inst_orphan_elimination               true
% 2.40/1.05  --inst_learning_loop_flag               true
% 2.40/1.05  --inst_learning_start                   3000
% 2.40/1.05  --inst_learning_factor                  2
% 2.40/1.05  --inst_start_prop_sim_after_learn       3
% 2.40/1.05  --inst_sel_renew                        solver
% 2.40/1.05  --inst_lit_activity_flag                true
% 2.40/1.05  --inst_restr_to_given                   false
% 2.40/1.05  --inst_activity_threshold               500
% 2.40/1.05  --inst_out_proof                        true
% 2.40/1.05  
% 2.40/1.05  ------ Resolution Options
% 2.40/1.05  
% 2.40/1.05  --resolution_flag                       true
% 2.40/1.05  --res_lit_sel                           adaptive
% 2.40/1.05  --res_lit_sel_side                      none
% 2.40/1.05  --res_ordering                          kbo
% 2.40/1.05  --res_to_prop_solver                    active
% 2.40/1.05  --res_prop_simpl_new                    false
% 2.40/1.05  --res_prop_simpl_given                  true
% 2.40/1.05  --res_passive_queue_type                priority_queues
% 2.40/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.05  --res_passive_queues_freq               [15;5]
% 2.40/1.05  --res_forward_subs                      full
% 2.40/1.05  --res_backward_subs                     full
% 2.40/1.05  --res_forward_subs_resolution           true
% 2.40/1.05  --res_backward_subs_resolution          true
% 2.40/1.05  --res_orphan_elimination                true
% 2.40/1.05  --res_time_limit                        2.
% 2.40/1.05  --res_out_proof                         true
% 2.40/1.05  
% 2.40/1.05  ------ Superposition Options
% 2.40/1.05  
% 2.40/1.05  --superposition_flag                    true
% 2.40/1.05  --sup_passive_queue_type                priority_queues
% 2.40/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.05  --demod_completeness_check              fast
% 2.40/1.05  --demod_use_ground                      true
% 2.40/1.05  --sup_to_prop_solver                    passive
% 2.40/1.05  --sup_prop_simpl_new                    true
% 2.40/1.05  --sup_prop_simpl_given                  true
% 2.40/1.05  --sup_fun_splitting                     false
% 2.40/1.05  --sup_smt_interval                      50000
% 2.40/1.05  
% 2.40/1.05  ------ Superposition Simplification Setup
% 2.40/1.05  
% 2.40/1.05  --sup_indices_passive                   []
% 2.40/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_full_bw                           [BwDemod]
% 2.40/1.05  --sup_immed_triv                        [TrivRules]
% 2.40/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_immed_bw_main                     []
% 2.40/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.05  
% 2.40/1.05  ------ Combination Options
% 2.40/1.05  
% 2.40/1.05  --comb_res_mult                         3
% 2.40/1.05  --comb_sup_mult                         2
% 2.40/1.05  --comb_inst_mult                        10
% 2.40/1.05  
% 2.40/1.05  ------ Debug Options
% 2.40/1.05  
% 2.40/1.05  --dbg_backtrace                         false
% 2.40/1.05  --dbg_dump_prop_clauses                 false
% 2.40/1.05  --dbg_dump_prop_clauses_file            -
% 2.40/1.05  --dbg_out_stat                          false
% 2.40/1.05  ------ Parsing...
% 2.40/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.40/1.05  ------ Proving...
% 2.40/1.05  ------ Problem Properties 
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  clauses                                 20
% 2.40/1.05  conjectures                             5
% 2.40/1.05  EPR                                     8
% 2.40/1.05  Horn                                    14
% 2.40/1.05  unary                                   5
% 2.40/1.05  binary                                  5
% 2.40/1.05  lits                                    47
% 2.40/1.05  lits eq                                 4
% 2.40/1.05  fd_pure                                 0
% 2.40/1.05  fd_pseudo                               0
% 2.40/1.05  fd_cond                                 0
% 2.40/1.05  fd_pseudo_cond                          0
% 2.40/1.05  AC symbols                              0
% 2.40/1.05  
% 2.40/1.05  ------ Schedule dynamic 5 is on 
% 2.40/1.05  
% 2.40/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  ------ 
% 2.40/1.05  Current options:
% 2.40/1.05  ------ 
% 2.40/1.05  
% 2.40/1.05  ------ Input Options
% 2.40/1.05  
% 2.40/1.05  --out_options                           all
% 2.40/1.05  --tptp_safe_out                         true
% 2.40/1.05  --problem_path                          ""
% 2.40/1.05  --include_path                          ""
% 2.40/1.05  --clausifier                            res/vclausify_rel
% 2.40/1.05  --clausifier_options                    --mode clausify
% 2.40/1.05  --stdin                                 false
% 2.40/1.05  --stats_out                             all
% 2.40/1.05  
% 2.40/1.05  ------ General Options
% 2.40/1.05  
% 2.40/1.05  --fof                                   false
% 2.40/1.05  --time_out_real                         305.
% 2.40/1.05  --time_out_virtual                      -1.
% 2.40/1.05  --symbol_type_check                     false
% 2.40/1.05  --clausify_out                          false
% 2.40/1.05  --sig_cnt_out                           false
% 2.40/1.05  --trig_cnt_out                          false
% 2.40/1.05  --trig_cnt_out_tolerance                1.
% 2.40/1.05  --trig_cnt_out_sk_spl                   false
% 2.40/1.05  --abstr_cl_out                          false
% 2.40/1.05  
% 2.40/1.05  ------ Global Options
% 2.40/1.05  
% 2.40/1.05  --schedule                              default
% 2.40/1.05  --add_important_lit                     false
% 2.40/1.05  --prop_solver_per_cl                    1000
% 2.40/1.05  --min_unsat_core                        false
% 2.40/1.05  --soft_assumptions                      false
% 2.40/1.05  --soft_lemma_size                       3
% 2.40/1.05  --prop_impl_unit_size                   0
% 2.40/1.05  --prop_impl_unit                        []
% 2.40/1.05  --share_sel_clauses                     true
% 2.40/1.05  --reset_solvers                         false
% 2.40/1.05  --bc_imp_inh                            [conj_cone]
% 2.40/1.05  --conj_cone_tolerance                   3.
% 2.40/1.05  --extra_neg_conj                        none
% 2.40/1.05  --large_theory_mode                     true
% 2.40/1.05  --prolific_symb_bound                   200
% 2.40/1.05  --lt_threshold                          2000
% 2.40/1.05  --clause_weak_htbl                      true
% 2.40/1.05  --gc_record_bc_elim                     false
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing Options
% 2.40/1.05  
% 2.40/1.05  --preprocessing_flag                    true
% 2.40/1.05  --time_out_prep_mult                    0.1
% 2.40/1.05  --splitting_mode                        input
% 2.40/1.05  --splitting_grd                         true
% 2.40/1.05  --splitting_cvd                         false
% 2.40/1.05  --splitting_cvd_svl                     false
% 2.40/1.05  --splitting_nvd                         32
% 2.40/1.05  --sub_typing                            true
% 2.40/1.05  --prep_gs_sim                           true
% 2.40/1.05  --prep_unflatten                        true
% 2.40/1.05  --prep_res_sim                          true
% 2.40/1.05  --prep_upred                            true
% 2.40/1.05  --prep_sem_filter                       exhaustive
% 2.40/1.05  --prep_sem_filter_out                   false
% 2.40/1.05  --pred_elim                             true
% 2.40/1.05  --res_sim_input                         true
% 2.40/1.05  --eq_ax_congr_red                       true
% 2.40/1.05  --pure_diseq_elim                       true
% 2.40/1.05  --brand_transform                       false
% 2.40/1.05  --non_eq_to_eq                          false
% 2.40/1.05  --prep_def_merge                        true
% 2.40/1.05  --prep_def_merge_prop_impl              false
% 2.40/1.05  --prep_def_merge_mbd                    true
% 2.40/1.05  --prep_def_merge_tr_red                 false
% 2.40/1.05  --prep_def_merge_tr_cl                  false
% 2.40/1.05  --smt_preprocessing                     true
% 2.40/1.05  --smt_ac_axioms                         fast
% 2.40/1.05  --preprocessed_out                      false
% 2.40/1.05  --preprocessed_stats                    false
% 2.40/1.05  
% 2.40/1.05  ------ Abstraction refinement Options
% 2.40/1.05  
% 2.40/1.05  --abstr_ref                             []
% 2.40/1.05  --abstr_ref_prep                        false
% 2.40/1.05  --abstr_ref_until_sat                   false
% 2.40/1.05  --abstr_ref_sig_restrict                funpre
% 2.40/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 2.40/1.05  --abstr_ref_under                       []
% 2.40/1.05  
% 2.40/1.05  ------ SAT Options
% 2.40/1.05  
% 2.40/1.05  --sat_mode                              false
% 2.40/1.05  --sat_fm_restart_options                ""
% 2.40/1.05  --sat_gr_def                            false
% 2.40/1.05  --sat_epr_types                         true
% 2.40/1.05  --sat_non_cyclic_types                  false
% 2.40/1.05  --sat_finite_models                     false
% 2.40/1.05  --sat_fm_lemmas                         false
% 2.40/1.05  --sat_fm_prep                           false
% 2.40/1.05  --sat_fm_uc_incr                        true
% 2.40/1.05  --sat_out_model                         small
% 2.40/1.05  --sat_out_clauses                       false
% 2.40/1.05  
% 2.40/1.05  ------ QBF Options
% 2.40/1.05  
% 2.40/1.05  --qbf_mode                              false
% 2.40/1.05  --qbf_elim_univ                         false
% 2.40/1.05  --qbf_dom_inst                          none
% 2.40/1.05  --qbf_dom_pre_inst                      false
% 2.40/1.05  --qbf_sk_in                             false
% 2.40/1.05  --qbf_pred_elim                         true
% 2.40/1.05  --qbf_split                             512
% 2.40/1.05  
% 2.40/1.05  ------ BMC1 Options
% 2.40/1.05  
% 2.40/1.05  --bmc1_incremental                      false
% 2.40/1.05  --bmc1_axioms                           reachable_all
% 2.40/1.05  --bmc1_min_bound                        0
% 2.40/1.05  --bmc1_max_bound                        -1
% 2.40/1.05  --bmc1_max_bound_default                -1
% 2.40/1.05  --bmc1_symbol_reachability              true
% 2.40/1.05  --bmc1_property_lemmas                  false
% 2.40/1.05  --bmc1_k_induction                      false
% 2.40/1.05  --bmc1_non_equiv_states                 false
% 2.40/1.05  --bmc1_deadlock                         false
% 2.40/1.05  --bmc1_ucm                              false
% 2.40/1.05  --bmc1_add_unsat_core                   none
% 2.40/1.05  --bmc1_unsat_core_children              false
% 2.40/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 2.40/1.05  --bmc1_out_stat                         full
% 2.40/1.05  --bmc1_ground_init                      false
% 2.40/1.05  --bmc1_pre_inst_next_state              false
% 2.40/1.05  --bmc1_pre_inst_state                   false
% 2.40/1.05  --bmc1_pre_inst_reach_state             false
% 2.40/1.05  --bmc1_out_unsat_core                   false
% 2.40/1.05  --bmc1_aig_witness_out                  false
% 2.40/1.05  --bmc1_verbose                          false
% 2.40/1.05  --bmc1_dump_clauses_tptp                false
% 2.40/1.05  --bmc1_dump_unsat_core_tptp             false
% 2.40/1.05  --bmc1_dump_file                        -
% 2.40/1.05  --bmc1_ucm_expand_uc_limit              128
% 2.40/1.05  --bmc1_ucm_n_expand_iterations          6
% 2.40/1.05  --bmc1_ucm_extend_mode                  1
% 2.40/1.05  --bmc1_ucm_init_mode                    2
% 2.40/1.05  --bmc1_ucm_cone_mode                    none
% 2.40/1.05  --bmc1_ucm_reduced_relation_type        0
% 2.40/1.05  --bmc1_ucm_relax_model                  4
% 2.40/1.05  --bmc1_ucm_full_tr_after_sat            true
% 2.40/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 2.40/1.05  --bmc1_ucm_layered_model                none
% 2.40/1.05  --bmc1_ucm_max_lemma_size               10
% 2.40/1.05  
% 2.40/1.05  ------ AIG Options
% 2.40/1.05  
% 2.40/1.05  --aig_mode                              false
% 2.40/1.05  
% 2.40/1.05  ------ Instantiation Options
% 2.40/1.05  
% 2.40/1.05  --instantiation_flag                    true
% 2.40/1.05  --inst_sos_flag                         false
% 2.40/1.05  --inst_sos_phase                        true
% 2.40/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.40/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.40/1.05  --inst_lit_sel_side                     none
% 2.40/1.05  --inst_solver_per_active                1400
% 2.40/1.05  --inst_solver_calls_frac                1.
% 2.40/1.05  --inst_passive_queue_type               priority_queues
% 2.40/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.40/1.05  --inst_passive_queues_freq              [25;2]
% 2.40/1.05  --inst_dismatching                      true
% 2.40/1.05  --inst_eager_unprocessed_to_passive     true
% 2.40/1.05  --inst_prop_sim_given                   true
% 2.40/1.05  --inst_prop_sim_new                     false
% 2.40/1.05  --inst_subs_new                         false
% 2.40/1.05  --inst_eq_res_simp                      false
% 2.40/1.05  --inst_subs_given                       false
% 2.40/1.05  --inst_orphan_elimination               true
% 2.40/1.05  --inst_learning_loop_flag               true
% 2.40/1.05  --inst_learning_start                   3000
% 2.40/1.05  --inst_learning_factor                  2
% 2.40/1.05  --inst_start_prop_sim_after_learn       3
% 2.40/1.05  --inst_sel_renew                        solver
% 2.40/1.05  --inst_lit_activity_flag                true
% 2.40/1.05  --inst_restr_to_given                   false
% 2.40/1.05  --inst_activity_threshold               500
% 2.40/1.05  --inst_out_proof                        true
% 2.40/1.05  
% 2.40/1.05  ------ Resolution Options
% 2.40/1.05  
% 2.40/1.05  --resolution_flag                       false
% 2.40/1.05  --res_lit_sel                           adaptive
% 2.40/1.05  --res_lit_sel_side                      none
% 2.40/1.05  --res_ordering                          kbo
% 2.40/1.05  --res_to_prop_solver                    active
% 2.40/1.05  --res_prop_simpl_new                    false
% 2.40/1.05  --res_prop_simpl_given                  true
% 2.40/1.05  --res_passive_queue_type                priority_queues
% 2.40/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.40/1.05  --res_passive_queues_freq               [15;5]
% 2.40/1.05  --res_forward_subs                      full
% 2.40/1.05  --res_backward_subs                     full
% 2.40/1.05  --res_forward_subs_resolution           true
% 2.40/1.05  --res_backward_subs_resolution          true
% 2.40/1.05  --res_orphan_elimination                true
% 2.40/1.05  --res_time_limit                        2.
% 2.40/1.05  --res_out_proof                         true
% 2.40/1.05  
% 2.40/1.05  ------ Superposition Options
% 2.40/1.05  
% 2.40/1.05  --superposition_flag                    true
% 2.40/1.05  --sup_passive_queue_type                priority_queues
% 2.40/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.40/1.05  --sup_passive_queues_freq               [8;1;4]
% 2.40/1.05  --demod_completeness_check              fast
% 2.40/1.05  --demod_use_ground                      true
% 2.40/1.05  --sup_to_prop_solver                    passive
% 2.40/1.05  --sup_prop_simpl_new                    true
% 2.40/1.05  --sup_prop_simpl_given                  true
% 2.40/1.05  --sup_fun_splitting                     false
% 2.40/1.05  --sup_smt_interval                      50000
% 2.40/1.05  
% 2.40/1.05  ------ Superposition Simplification Setup
% 2.40/1.05  
% 2.40/1.05  --sup_indices_passive                   []
% 2.40/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.40/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.40/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_full_bw                           [BwDemod]
% 2.40/1.05  --sup_immed_triv                        [TrivRules]
% 2.40/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.40/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_immed_bw_main                     []
% 2.40/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.40/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.40/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.40/1.05  
% 2.40/1.05  ------ Combination Options
% 2.40/1.05  
% 2.40/1.05  --comb_res_mult                         3
% 2.40/1.05  --comb_sup_mult                         2
% 2.40/1.05  --comb_inst_mult                        10
% 2.40/1.05  
% 2.40/1.05  ------ Debug Options
% 2.40/1.05  
% 2.40/1.05  --dbg_backtrace                         false
% 2.40/1.05  --dbg_dump_prop_clauses                 false
% 2.40/1.05  --dbg_dump_prop_clauses_file            -
% 2.40/1.05  --dbg_out_stat                          false
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  ------ Proving...
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  % SZS status Theorem for theBenchmark.p
% 2.40/1.05  
% 2.40/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.40/1.05  
% 2.40/1.05  fof(f9,conjecture,(
% 2.40/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f10,negated_conjecture,(
% 2.40/1.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.40/1.05    inference(negated_conjecture,[],[f9])).
% 2.40/1.05  
% 2.40/1.05  fof(f19,plain,(
% 2.40/1.05    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f10])).
% 2.40/1.05  
% 2.40/1.05  fof(f20,plain,(
% 2.40/1.05    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.40/1.05    inference(flattening,[],[f19])).
% 2.40/1.05  
% 2.40/1.05  fof(f33,plain,(
% 2.40/1.05    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.40/1.05    introduced(choice_axiom,[])).
% 2.40/1.05  
% 2.40/1.05  fof(f32,plain,(
% 2.40/1.05    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.40/1.05    introduced(choice_axiom,[])).
% 2.40/1.05  
% 2.40/1.05  fof(f31,plain,(
% 2.40/1.05    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.40/1.05    introduced(choice_axiom,[])).
% 2.40/1.05  
% 2.40/1.05  fof(f34,plain,(
% 2.40/1.05    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.40/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f20,f33,f32,f31])).
% 2.40/1.05  
% 2.40/1.05  fof(f56,plain,(
% 2.40/1.05    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f7,axiom,(
% 2.40/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f15,plain,(
% 2.40/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f7])).
% 2.40/1.05  
% 2.40/1.05  fof(f16,plain,(
% 2.40/1.05    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.40/1.05    inference(flattening,[],[f15])).
% 2.40/1.05  
% 2.40/1.05  fof(f46,plain,(
% 2.40/1.05    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f16])).
% 2.40/1.05  
% 2.40/1.05  fof(f2,axiom,(
% 2.40/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f37,plain,(
% 2.40/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f2])).
% 2.40/1.05  
% 2.40/1.05  fof(f59,plain,(
% 2.40/1.05    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.05    inference(definition_unfolding,[],[f46,f37])).
% 2.40/1.05  
% 2.40/1.05  fof(f54,plain,(
% 2.40/1.05    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f57,plain,(
% 2.40/1.05    r2_hidden(sK4,sK3)),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f5,axiom,(
% 2.40/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f26,plain,(
% 2.40/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.40/1.05    inference(nnf_transformation,[],[f5])).
% 2.40/1.05  
% 2.40/1.05  fof(f43,plain,(
% 2.40/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.40/1.05    inference(cnf_transformation,[],[f26])).
% 2.40/1.05  
% 2.40/1.05  fof(f4,axiom,(
% 2.40/1.05    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f12,plain,(
% 2.40/1.05    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f4])).
% 2.40/1.05  
% 2.40/1.05  fof(f42,plain,(
% 2.40/1.05    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.40/1.05    inference(cnf_transformation,[],[f12])).
% 2.40/1.05  
% 2.40/1.05  fof(f44,plain,(
% 2.40/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f26])).
% 2.40/1.05  
% 2.40/1.05  fof(f1,axiom,(
% 2.40/1.05    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f21,plain,(
% 2.40/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.40/1.05    inference(nnf_transformation,[],[f1])).
% 2.40/1.05  
% 2.40/1.05  fof(f22,plain,(
% 2.40/1.05    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/1.05    inference(rectify,[],[f21])).
% 2.40/1.05  
% 2.40/1.05  fof(f23,plain,(
% 2.40/1.05    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.40/1.05    introduced(choice_axiom,[])).
% 2.40/1.05  
% 2.40/1.05  fof(f24,plain,(
% 2.40/1.05    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.40/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f22,f23])).
% 2.40/1.05  
% 2.40/1.05  fof(f35,plain,(
% 2.40/1.05    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f24])).
% 2.40/1.05  
% 2.40/1.05  fof(f6,axiom,(
% 2.40/1.05    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f13,plain,(
% 2.40/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f6])).
% 2.40/1.05  
% 2.40/1.05  fof(f14,plain,(
% 2.40/1.05    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.40/1.05    inference(flattening,[],[f13])).
% 2.40/1.05  
% 2.40/1.05  fof(f45,plain,(
% 2.40/1.05    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f14])).
% 2.40/1.05  
% 2.40/1.05  fof(f3,axiom,(
% 2.40/1.05    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f11,plain,(
% 2.40/1.05    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f3])).
% 2.40/1.05  
% 2.40/1.05  fof(f25,plain,(
% 2.40/1.05    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.40/1.05    inference(nnf_transformation,[],[f11])).
% 2.40/1.05  
% 2.40/1.05  fof(f39,plain,(
% 2.40/1.05    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f25])).
% 2.40/1.05  
% 2.40/1.05  fof(f8,axiom,(
% 2.40/1.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.40/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.40/1.05  
% 2.40/1.05  fof(f17,plain,(
% 2.40/1.05    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.40/1.05    inference(ennf_transformation,[],[f8])).
% 2.40/1.05  
% 2.40/1.05  fof(f18,plain,(
% 2.40/1.05    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.05    inference(flattening,[],[f17])).
% 2.40/1.05  
% 2.40/1.05  fof(f27,plain,(
% 2.40/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.05    inference(nnf_transformation,[],[f18])).
% 2.40/1.05  
% 2.40/1.05  fof(f28,plain,(
% 2.40/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.05    inference(rectify,[],[f27])).
% 2.40/1.05  
% 2.40/1.05  fof(f29,plain,(
% 2.40/1.05    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.40/1.05    introduced(choice_axiom,[])).
% 2.40/1.05  
% 2.40/1.05  fof(f30,plain,(
% 2.40/1.05    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.40/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 2.40/1.05  
% 2.40/1.05  fof(f47,plain,(
% 2.40/1.05    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.40/1.05    inference(cnf_transformation,[],[f30])).
% 2.40/1.05  
% 2.40/1.05  fof(f53,plain,(
% 2.40/1.05    l1_pre_topc(sK2)),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f51,plain,(
% 2.40/1.05    ~v2_struct_0(sK2)),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f52,plain,(
% 2.40/1.05    v2_pre_topc(sK2)),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f55,plain,(
% 2.40/1.05    v2_tex_2(sK3,sK2)),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  fof(f58,plain,(
% 2.40/1.05    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 2.40/1.05    inference(cnf_transformation,[],[f34])).
% 2.40/1.05  
% 2.40/1.05  cnf(c_17,negated_conjecture,
% 2.40/1.05      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.40/1.05      inference(cnf_transformation,[],[f56]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1396,plain,
% 2.40/1.05      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_10,plain,
% 2.40/1.05      ( ~ m1_subset_1(X0,X1)
% 2.40/1.05      | v1_xboole_0(X1)
% 2.40/1.05      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 2.40/1.05      inference(cnf_transformation,[],[f59]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1398,plain,
% 2.40/1.05      ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
% 2.40/1.05      | m1_subset_1(X0,X1) != iProver_top
% 2.40/1.05      | v1_xboole_0(X1) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2766,plain,
% 2.40/1.05      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4)
% 2.40/1.05      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_1396,c_1398]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_19,negated_conjecture,
% 2.40/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/1.05      inference(cnf_transformation,[],[f54]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_26,plain,
% 2.40/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_16,negated_conjecture,
% 2.40/1.05      ( r2_hidden(sK4,sK3) ),
% 2.40/1.05      inference(cnf_transformation,[],[f57]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_29,plain,
% 2.40/1.05      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_8,plain,
% 2.40/1.05      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.40/1.05      inference(cnf_transformation,[],[f43]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1565,plain,
% 2.40/1.05      ( r1_tarski(sK3,u1_struct_0(sK2))
% 2.40/1.05      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1566,plain,
% 2.40/1.05      ( r1_tarski(sK3,u1_struct_0(sK2)) = iProver_top
% 2.40/1.05      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_1565]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_6,plain,
% 2.40/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.40/1.05      | ~ r2_hidden(X2,X0)
% 2.40/1.05      | r2_hidden(X2,X1) ),
% 2.40/1.05      inference(cnf_transformation,[],[f42]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_7,plain,
% 2.40/1.05      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.40/1.05      inference(cnf_transformation,[],[f44]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_172,plain,
% 2.40/1.05      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.40/1.05      inference(prop_impl,[status(thm)],[c_7]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_211,plain,
% 2.40/1.05      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.40/1.05      inference(bin_hyper_res,[status(thm)],[c_6,c_172]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1626,plain,
% 2.40/1.05      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 2.40/1.05      | r2_hidden(X0,u1_struct_0(sK2))
% 2.40/1.05      | ~ r2_hidden(X0,sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_211]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1791,plain,
% 2.40/1.05      ( ~ r1_tarski(sK3,u1_struct_0(sK2))
% 2.40/1.05      | r2_hidden(sK4,u1_struct_0(sK2))
% 2.40/1.05      | ~ r2_hidden(sK4,sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1626]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1792,plain,
% 2.40/1.05      ( r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | r2_hidden(sK4,u1_struct_0(sK2)) = iProver_top
% 2.40/1.05      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1,plain,
% 2.40/1.05      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.40/1.05      inference(cnf_transformation,[],[f35]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1970,plain,
% 2.40/1.05      ( ~ r2_hidden(sK4,u1_struct_0(sK2))
% 2.40/1.05      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1971,plain,
% 2.40/1.05      ( r2_hidden(sK4,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_1970]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3035,plain,
% 2.40/1.05      ( k6_domain_1(u1_struct_0(sK2),sK4) = k2_tarski(sK4,sK4) ),
% 2.40/1.05      inference(global_propositional_subsumption,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_2766,c_26,c_29,c_1566,c_1792,c_1971]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_9,plain,
% 2.40/1.05      ( ~ m1_subset_1(X0,X1)
% 2.40/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.40/1.05      | v1_xboole_0(X1) ),
% 2.40/1.05      inference(cnf_transformation,[],[f45]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1399,plain,
% 2.40/1.05      ( m1_subset_1(X0,X1) != iProver_top
% 2.40/1.05      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.40/1.05      | v1_xboole_0(X1) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3210,plain,
% 2.40/1.05      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.40/1.05      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_3035,c_1399]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_28,plain,
% 2.40/1.05      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3686,plain,
% 2.40/1.05      ( m1_subset_1(k2_tarski(sK4,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.05      inference(global_propositional_subsumption,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_3210,c_26,c_28,c_29,c_1566,c_1792,c_1971]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1397,plain,
% 2.40/1.05      ( r2_hidden(sK4,sK3) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_4,plain,
% 2.40/1.05      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.40/1.05      inference(cnf_transformation,[],[f39]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_133,plain,
% 2.40/1.05      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.40/1.05      inference(global_propositional_subsumption,[status(thm)],[c_4,c_1]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_134,plain,
% 2.40/1.05      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.40/1.05      inference(renaming,[status(thm)],[c_133]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1393,plain,
% 2.40/1.05      ( m1_subset_1(X0,X1) = iProver_top
% 2.40/1.05      | r2_hidden(X0,X1) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_134]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3185,plain,
% 2.40/1.05      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_1397,c_1393]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3393,plain,
% 2.40/1.05      ( k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4)
% 2.40/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_3185,c_1398]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1552,plain,
% 2.40/1.05      ( ~ r2_hidden(sK4,sK3) | ~ v1_xboole_0(sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1770,plain,
% 2.40/1.05      ( m1_subset_1(X0,sK3) | ~ r2_hidden(X0,sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_134]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2279,plain,
% 2.40/1.05      ( m1_subset_1(sK4,sK3) | ~ r2_hidden(sK4,sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1770]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1610,plain,
% 2.40/1.05      ( ~ m1_subset_1(X0,sK3)
% 2.40/1.05      | v1_xboole_0(sK3)
% 2.40/1.05      | k2_tarski(X0,X0) = k6_domain_1(sK3,X0) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2355,plain,
% 2.40/1.05      ( ~ m1_subset_1(sK4,sK3)
% 2.40/1.05      | v1_xboole_0(sK3)
% 2.40/1.05      | k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1610]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3515,plain,
% 2.40/1.05      ( k2_tarski(sK4,sK4) = k6_domain_1(sK3,sK4) ),
% 2.40/1.05      inference(global_propositional_subsumption,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_3393,c_16,c_1552,c_2279,c_2355]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3690,plain,
% 2.40/1.05      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.05      inference(light_normalisation,[status(thm)],[c_3686,c_3515]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1400,plain,
% 2.40/1.05      ( r1_tarski(X0,X1) = iProver_top
% 2.40/1.05      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3696,plain,
% 2.40/1.05      ( r1_tarski(k6_domain_1(sK3,sK4),u1_struct_0(sK2)) = iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_3690,c_1400]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1394,plain,
% 2.40/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1401,plain,
% 2.40/1.05      ( r1_tarski(X0,X1) != iProver_top
% 2.40/1.05      | m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_14,plain,
% 2.40/1.05      ( ~ v2_tex_2(X0,X1)
% 2.40/1.05      | ~ r1_tarski(X2,X0)
% 2.40/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.05      | v2_struct_0(X1)
% 2.40/1.05      | ~ v2_pre_topc(X1)
% 2.40/1.05      | ~ l1_pre_topc(X1)
% 2.40/1.05      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.40/1.05      inference(cnf_transformation,[],[f47]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_20,negated_conjecture,
% 2.40/1.05      ( l1_pre_topc(sK2) ),
% 2.40/1.05      inference(cnf_transformation,[],[f53]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_295,plain,
% 2.40/1.05      ( ~ v2_tex_2(X0,X1)
% 2.40/1.05      | ~ r1_tarski(X2,X0)
% 2.40/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.40/1.05      | v2_struct_0(X1)
% 2.40/1.05      | ~ v2_pre_topc(X1)
% 2.40/1.05      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.40/1.05      | sK2 != X1 ),
% 2.40/1.05      inference(resolution_lifted,[status(thm)],[c_14,c_20]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_296,plain,
% 2.40/1.05      ( ~ v2_tex_2(X0,sK2)
% 2.40/1.05      | ~ r1_tarski(X1,X0)
% 2.40/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | v2_struct_0(sK2)
% 2.40/1.05      | ~ v2_pre_topc(sK2)
% 2.40/1.05      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.40/1.05      inference(unflattening,[status(thm)],[c_295]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_22,negated_conjecture,
% 2.40/1.05      ( ~ v2_struct_0(sK2) ),
% 2.40/1.05      inference(cnf_transformation,[],[f51]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_21,negated_conjecture,
% 2.40/1.05      ( v2_pre_topc(sK2) ),
% 2.40/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_300,plain,
% 2.40/1.05      ( ~ v2_tex_2(X0,sK2)
% 2.40/1.05      | ~ r1_tarski(X1,X0)
% 2.40/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.40/1.05      inference(global_propositional_subsumption,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_296,c_22,c_21]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_301,plain,
% 2.40/1.05      ( ~ v2_tex_2(X0,sK2)
% 2.40/1.05      | ~ r1_tarski(X1,X0)
% 2.40/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.40/1.05      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.40/1.05      inference(renaming,[status(thm)],[c_300]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1391,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 2.40/1.05      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/1.05      | r1_tarski(X1,X0) != iProver_top
% 2.40/1.05      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.40/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_301]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1886,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 2.40/1.05      | v2_tex_2(X0,sK2) != iProver_top
% 2.40/1.05      | r1_tarski(X1,X0) != iProver_top
% 2.40/1.05      | r1_tarski(X1,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_1401,c_1391]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2222,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0
% 2.40/1.05      | v2_tex_2(sK3,sK2) != iProver_top
% 2.40/1.05      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | r1_tarski(X0,sK3) != iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_1394,c_1886]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_18,negated_conjecture,
% 2.40/1.05      ( v2_tex_2(sK3,sK2) ),
% 2.40/1.05      inference(cnf_transformation,[],[f55]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_27,plain,
% 2.40/1.05      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2264,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,X0)) = X0
% 2.40/1.05      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top
% 2.40/1.05      | r1_tarski(X0,sK3) != iProver_top ),
% 2.40/1.05      inference(global_propositional_subsumption,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_2222,c_27]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3920,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(sK3,sK4))) = k6_domain_1(sK3,sK4)
% 2.40/1.05      | r1_tarski(k6_domain_1(sK3,sK4),sK3) != iProver_top ),
% 2.40/1.05      inference(superposition,[status(thm)],[c_3696,c_2264]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_15,negated_conjecture,
% 2.40/1.05      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.40/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3038,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k2_tarski(sK4,sK4))) != k2_tarski(sK4,sK4) ),
% 2.40/1.05      inference(demodulation,[status(thm)],[c_3035,c_15]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3518,plain,
% 2.40/1.05      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(sK3,sK4))) != k6_domain_1(sK3,sK4) ),
% 2.40/1.05      inference(demodulation,[status(thm)],[c_3515,c_3038]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1828,plain,
% 2.40/1.05      ( r1_tarski(X0,sK3) | ~ m1_subset_1(X0,k1_zfmisc_1(sK3)) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_8]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3031,plain,
% 2.40/1.05      ( r1_tarski(k6_domain_1(sK3,sK4),sK3)
% 2.40/1.05      | ~ m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1828]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_3032,plain,
% 2.40/1.05      ( r1_tarski(k6_domain_1(sK3,sK4),sK3) = iProver_top
% 2.40/1.05      | m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_3031]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1611,plain,
% 2.40/1.05      ( ~ m1_subset_1(X0,sK3)
% 2.40/1.05      | m1_subset_1(k6_domain_1(sK3,X0),k1_zfmisc_1(sK3))
% 2.40/1.05      | v1_xboole_0(sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_9]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2357,plain,
% 2.40/1.05      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3))
% 2.40/1.05      | ~ m1_subset_1(sK4,sK3)
% 2.40/1.05      | v1_xboole_0(sK3) ),
% 2.40/1.05      inference(instantiation,[status(thm)],[c_1611]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2358,plain,
% 2.40/1.05      ( m1_subset_1(k6_domain_1(sK3,sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.40/1.05      | m1_subset_1(sK4,sK3) != iProver_top
% 2.40/1.05      | v1_xboole_0(sK3) = iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_2357]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_2280,plain,
% 2.40/1.05      ( m1_subset_1(sK4,sK3) = iProver_top
% 2.40/1.05      | r2_hidden(sK4,sK3) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_2279]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(c_1553,plain,
% 2.40/1.05      ( r2_hidden(sK4,sK3) != iProver_top
% 2.40/1.05      | v1_xboole_0(sK3) != iProver_top ),
% 2.40/1.05      inference(predicate_to_equality,[status(thm)],[c_1552]) ).
% 2.40/1.05  
% 2.40/1.05  cnf(contradiction,plain,
% 2.40/1.05      ( $false ),
% 2.40/1.05      inference(minisat,
% 2.40/1.05                [status(thm)],
% 2.40/1.05                [c_3920,c_3518,c_3032,c_2358,c_2280,c_1553,c_29]) ).
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.40/1.05  
% 2.40/1.05  ------                               Statistics
% 2.40/1.05  
% 2.40/1.05  ------ General
% 2.40/1.05  
% 2.40/1.05  abstr_ref_over_cycles:                  0
% 2.40/1.05  abstr_ref_under_cycles:                 0
% 2.40/1.05  gc_basic_clause_elim:                   0
% 2.40/1.05  forced_gc_time:                         0
% 2.40/1.05  parsing_time:                           0.011
% 2.40/1.05  unif_index_cands_time:                  0.
% 2.40/1.05  unif_index_add_time:                    0.
% 2.40/1.05  orderings_time:                         0.
% 2.40/1.05  out_proof_time:                         0.01
% 2.40/1.05  total_time:                             0.167
% 2.40/1.05  num_of_symbols:                         50
% 2.40/1.05  num_of_terms:                           2128
% 2.40/1.05  
% 2.40/1.05  ------ Preprocessing
% 2.40/1.05  
% 2.40/1.05  num_of_splits:                          0
% 2.40/1.05  num_of_split_atoms:                     0
% 2.40/1.05  num_of_reused_defs:                     0
% 2.40/1.05  num_eq_ax_congr_red:                    19
% 2.40/1.05  num_of_sem_filtered_clauses:            1
% 2.40/1.05  num_of_subtypes:                        0
% 2.40/1.05  monotx_restored_types:                  0
% 2.40/1.05  sat_num_of_epr_types:                   0
% 2.40/1.05  sat_num_of_non_cyclic_types:            0
% 2.40/1.05  sat_guarded_non_collapsed_types:        0
% 2.40/1.05  num_pure_diseq_elim:                    0
% 2.40/1.05  simp_replaced_by:                       0
% 2.40/1.05  res_preprocessed:                       108
% 2.40/1.05  prep_upred:                             0
% 2.40/1.05  prep_unflattend:                        22
% 2.40/1.05  smt_new_axioms:                         0
% 2.40/1.05  pred_elim_cands:                        5
% 2.40/1.05  pred_elim:                              3
% 2.40/1.05  pred_elim_cl:                           3
% 2.40/1.05  pred_elim_cycles:                       7
% 2.40/1.05  merged_defs:                            8
% 2.40/1.05  merged_defs_ncl:                        0
% 2.40/1.05  bin_hyper_res:                          9
% 2.40/1.05  prep_cycles:                            4
% 2.40/1.05  pred_elim_time:                         0.014
% 2.40/1.05  splitting_time:                         0.
% 2.40/1.05  sem_filter_time:                        0.
% 2.40/1.05  monotx_time:                            0.001
% 2.40/1.05  subtype_inf_time:                       0.
% 2.40/1.05  
% 2.40/1.05  ------ Problem properties
% 2.40/1.05  
% 2.40/1.05  clauses:                                20
% 2.40/1.05  conjectures:                            5
% 2.40/1.05  epr:                                    8
% 2.40/1.05  horn:                                   14
% 2.40/1.05  ground:                                 5
% 2.40/1.05  unary:                                  5
% 2.40/1.05  binary:                                 5
% 2.40/1.05  lits:                                   47
% 2.40/1.05  lits_eq:                                4
% 2.40/1.05  fd_pure:                                0
% 2.40/1.05  fd_pseudo:                              0
% 2.40/1.05  fd_cond:                                0
% 2.40/1.05  fd_pseudo_cond:                         0
% 2.40/1.05  ac_symbols:                             0
% 2.40/1.05  
% 2.40/1.05  ------ Propositional Solver
% 2.40/1.05  
% 2.40/1.05  prop_solver_calls:                      28
% 2.40/1.05  prop_fast_solver_calls:                 800
% 2.40/1.05  smt_solver_calls:                       0
% 2.40/1.05  smt_fast_solver_calls:                  0
% 2.40/1.05  prop_num_of_clauses:                    1112
% 2.40/1.05  prop_preprocess_simplified:             4168
% 2.40/1.05  prop_fo_subsumed:                       31
% 2.40/1.05  prop_solver_time:                       0.
% 2.40/1.05  smt_solver_time:                        0.
% 2.40/1.05  smt_fast_solver_time:                   0.
% 2.40/1.05  prop_fast_solver_time:                  0.
% 2.40/1.05  prop_unsat_core_time:                   0.
% 2.40/1.05  
% 2.40/1.05  ------ QBF
% 2.40/1.05  
% 2.40/1.05  qbf_q_res:                              0
% 2.40/1.05  qbf_num_tautologies:                    0
% 2.40/1.05  qbf_prep_cycles:                        0
% 2.40/1.05  
% 2.40/1.05  ------ BMC1
% 2.40/1.05  
% 2.40/1.05  bmc1_current_bound:                     -1
% 2.40/1.05  bmc1_last_solved_bound:                 -1
% 2.40/1.05  bmc1_unsat_core_size:                   -1
% 2.40/1.05  bmc1_unsat_core_parents_size:           -1
% 2.40/1.05  bmc1_merge_next_fun:                    0
% 2.40/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.40/1.05  
% 2.40/1.05  ------ Instantiation
% 2.40/1.05  
% 2.40/1.05  inst_num_of_clauses:                    279
% 2.40/1.05  inst_num_in_passive:                    74
% 2.40/1.05  inst_num_in_active:                     200
% 2.40/1.05  inst_num_in_unprocessed:                5
% 2.40/1.05  inst_num_of_loops:                      240
% 2.40/1.05  inst_num_of_learning_restarts:          0
% 2.40/1.05  inst_num_moves_active_passive:          37
% 2.40/1.05  inst_lit_activity:                      0
% 2.40/1.05  inst_lit_activity_moves:                0
% 2.40/1.05  inst_num_tautologies:                   0
% 2.40/1.05  inst_num_prop_implied:                  0
% 2.40/1.05  inst_num_existing_simplified:           0
% 2.40/1.05  inst_num_eq_res_simplified:             0
% 2.40/1.05  inst_num_child_elim:                    0
% 2.40/1.05  inst_num_of_dismatching_blockings:      78
% 2.40/1.05  inst_num_of_non_proper_insts:           345
% 2.40/1.05  inst_num_of_duplicates:                 0
% 2.40/1.05  inst_inst_num_from_inst_to_res:         0
% 2.40/1.05  inst_dismatching_checking_time:         0.
% 2.40/1.05  
% 2.40/1.05  ------ Resolution
% 2.40/1.05  
% 2.40/1.05  res_num_of_clauses:                     0
% 2.40/1.05  res_num_in_passive:                     0
% 2.40/1.05  res_num_in_active:                      0
% 2.40/1.05  res_num_of_loops:                       112
% 2.40/1.05  res_forward_subset_subsumed:            43
% 2.40/1.05  res_backward_subset_subsumed:           0
% 2.40/1.05  res_forward_subsumed:                   0
% 2.40/1.05  res_backward_subsumed:                  0
% 2.40/1.05  res_forward_subsumption_resolution:     0
% 2.40/1.05  res_backward_subsumption_resolution:    0
% 2.40/1.05  res_clause_to_clause_subsumption:       235
% 2.40/1.05  res_orphan_elimination:                 0
% 2.40/1.05  res_tautology_del:                      46
% 2.40/1.05  res_num_eq_res_simplified:              0
% 2.40/1.05  res_num_sel_changes:                    0
% 2.40/1.05  res_moves_from_active_to_pass:          0
% 2.40/1.05  
% 2.40/1.05  ------ Superposition
% 2.40/1.05  
% 2.40/1.05  sup_time_total:                         0.
% 2.40/1.05  sup_time_generating:                    0.
% 2.40/1.05  sup_time_sim_full:                      0.
% 2.40/1.05  sup_time_sim_immed:                     0.
% 2.40/1.05  
% 2.40/1.05  sup_num_of_clauses:                     85
% 2.40/1.05  sup_num_in_active:                      44
% 2.40/1.05  sup_num_in_passive:                     41
% 2.40/1.05  sup_num_of_loops:                       46
% 2.40/1.05  sup_fw_superposition:                   33
% 2.40/1.05  sup_bw_superposition:                   56
% 2.40/1.05  sup_immediate_simplified:               5
% 2.40/1.05  sup_given_eliminated:                   0
% 2.40/1.05  comparisons_done:                       0
% 2.40/1.05  comparisons_avoided:                    0
% 2.40/1.05  
% 2.40/1.05  ------ Simplifications
% 2.40/1.05  
% 2.40/1.05  
% 2.40/1.05  sim_fw_subset_subsumed:                 5
% 2.40/1.05  sim_bw_subset_subsumed:                 1
% 2.40/1.05  sim_fw_subsumed:                        0
% 2.40/1.05  sim_bw_subsumed:                        0
% 2.40/1.05  sim_fw_subsumption_res:                 0
% 2.40/1.05  sim_bw_subsumption_res:                 0
% 2.40/1.05  sim_tautology_del:                      6
% 2.40/1.05  sim_eq_tautology_del:                   0
% 2.40/1.05  sim_eq_res_simp:                        0
% 2.40/1.05  sim_fw_demodulated:                     0
% 2.40/1.05  sim_bw_demodulated:                     3
% 2.40/1.05  sim_light_normalised:                   1
% 2.40/1.05  sim_joinable_taut:                      0
% 2.40/1.05  sim_joinable_simp:                      0
% 2.40/1.05  sim_ac_normalised:                      0
% 2.40/1.05  sim_smt_subsumption:                    0
% 2.40/1.05  
%------------------------------------------------------------------------------
