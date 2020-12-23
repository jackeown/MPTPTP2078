%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:29 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 410 expanded)
%              Number of clauses        :   60 ( 121 expanded)
%              Number of leaves         :   13 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  373 (2199 expanded)
%              Number of equality atoms :   95 ( 384 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

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
    inference(ennf_transformation,[],[f9])).

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

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4)))
        & r2_hidden(sK4,X1)
        & m1_subset_1(sK4,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))
    & r2_hidden(sK4,sK3)
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & v2_tex_2(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f31,f30,f29])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f48,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f51,plain,(
    r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f47,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f45,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_14,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_935,negated_conjecture,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1209,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_935])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_937,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | v1_xboole_0(X1_47)
    | k6_domain_1(X1_47,X0_47) = k1_tarski(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1208,plain,
    ( k6_domain_1(X0_47,X1_47) = k1_tarski(X1_47)
    | m1_subset_1(X1_47,X0_47) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1565,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_1208])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_13,negated_conjecture,
    ( r2_hidden(sK4,sK3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_275,plain,
    ( ~ v1_xboole_0(X0)
    | sK3 != X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_13])).

cnf(c_276,plain,
    ( ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_275])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_939,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_xboole_0(X1_47)
    | v1_xboole_0(X0_47) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1396,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(X0_47)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_939])).

cnf(c_1398,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | v1_xboole_0(sK3) ),
    inference(instantiation,[status(thm)],[c_1396])).

cnf(c_1758,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1565,c_16,c_14,c_276,c_1337,c_1398])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_938,plain,
    ( ~ m1_subset_1(X0_47,X1_47)
    | m1_subset_1(k6_domain_1(X1_47,X0_47),k1_zfmisc_1(X1_47))
    | v1_xboole_0(X1_47) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1207,plain,
    ( m1_subset_1(X0_47,X1_47) != iProver_top
    | m1_subset_1(k6_domain_1(X1_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top
    | v1_xboole_0(X1_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_1762,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1758,c_1207])).

cnf(c_23,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_277,plain,
    ( v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_1397,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(X0_47) = iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1396])).

cnf(c_1399,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_2017,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1762,c_23,c_25,c_277,c_1399])).

cnf(c_5,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_142,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_5])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_17,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_289,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_290,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_289])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_18,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_294,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_290,c_19,c_18])).

cnf(c_295,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_294])).

cnf(c_509,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X3 != X1
    | X0 != X2
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X3)) = X3 ),
    inference(resolution_lifted,[status(thm)],[c_142,c_295])).

cnf(c_510,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_927,plain,
    ( ~ v2_tex_2(X0_47,sK2)
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_47))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2)))
    | k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,X1_47)) = X1_47 ),
    inference(subtyping,[status(esa)],[c_510])).

cnf(c_1217,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,X1_47)) = X1_47
    | v2_tex_2(X0_47,sK2) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(X0_47)) != iProver_top
    | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_927])).

cnf(c_2023,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4)
    | v2_tex_2(X0_47,sK2) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2017,c_1217])).

cnf(c_2046,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4)
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2023])).

cnf(c_12,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_936,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1761,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
    inference(demodulation,[status(thm)],[c_1758,c_936])).

cnf(c_3,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_268,plain,
    ( m1_subset_1(X0,X1)
    | sK3 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_269,plain,
    ( m1_subset_1(sK4,sK3) ),
    inference(unflattening,[status(thm)],[c_268])).

cnf(c_931,plain,
    ( m1_subset_1(sK4,sK3) ),
    inference(subtyping,[status(esa)],[c_269])).

cnf(c_1213,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_1567,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1213,c_1208])).

cnf(c_1343,plain,
    ( ~ m1_subset_1(sK4,sK3)
    | v1_xboole_0(sK3)
    | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_1752,plain,
    ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_269,c_276,c_1343])).

cnf(c_1755,plain,
    ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,sK3) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1752,c_1207])).

cnf(c_270,plain,
    ( m1_subset_1(sK4,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_269])).

cnf(c_15,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_24,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2046,c_1761,c_1755,c_277,c_270,c_24,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.30  % Computer   : n010.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 15:38:44 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.11/0.31  % Running in FOF mode
% 2.03/0.95  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/0.95  
% 2.03/0.95  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.03/0.95  
% 2.03/0.95  ------  iProver source info
% 2.03/0.95  
% 2.03/0.95  git: date: 2020-06-30 10:37:57 +0100
% 2.03/0.95  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.03/0.95  git: non_committed_changes: false
% 2.03/0.95  git: last_make_outside_of_git: false
% 2.03/0.95  
% 2.03/0.95  ------ 
% 2.03/0.95  
% 2.03/0.95  ------ Input Options
% 2.03/0.95  
% 2.03/0.95  --out_options                           all
% 2.03/0.95  --tptp_safe_out                         true
% 2.03/0.95  --problem_path                          ""
% 2.03/0.95  --include_path                          ""
% 2.03/0.95  --clausifier                            res/vclausify_rel
% 2.03/0.95  --clausifier_options                    --mode clausify
% 2.03/0.95  --stdin                                 false
% 2.03/0.95  --stats_out                             all
% 2.03/0.95  
% 2.03/0.95  ------ General Options
% 2.03/0.95  
% 2.03/0.95  --fof                                   false
% 2.03/0.95  --time_out_real                         305.
% 2.03/0.95  --time_out_virtual                      -1.
% 2.03/0.95  --symbol_type_check                     false
% 2.03/0.95  --clausify_out                          false
% 2.03/0.95  --sig_cnt_out                           false
% 2.03/0.95  --trig_cnt_out                          false
% 2.03/0.95  --trig_cnt_out_tolerance                1.
% 2.03/0.95  --trig_cnt_out_sk_spl                   false
% 2.03/0.95  --abstr_cl_out                          false
% 2.03/0.95  
% 2.03/0.95  ------ Global Options
% 2.03/0.95  
% 2.03/0.95  --schedule                              default
% 2.03/0.95  --add_important_lit                     false
% 2.03/0.95  --prop_solver_per_cl                    1000
% 2.03/0.95  --min_unsat_core                        false
% 2.03/0.95  --soft_assumptions                      false
% 2.03/0.95  --soft_lemma_size                       3
% 2.03/0.95  --prop_impl_unit_size                   0
% 2.03/0.95  --prop_impl_unit                        []
% 2.03/0.95  --share_sel_clauses                     true
% 2.03/0.95  --reset_solvers                         false
% 2.03/0.95  --bc_imp_inh                            [conj_cone]
% 2.03/0.95  --conj_cone_tolerance                   3.
% 2.03/0.95  --extra_neg_conj                        none
% 2.03/0.95  --large_theory_mode                     true
% 2.03/0.95  --prolific_symb_bound                   200
% 2.03/0.95  --lt_threshold                          2000
% 2.03/0.95  --clause_weak_htbl                      true
% 2.03/0.95  --gc_record_bc_elim                     false
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing Options
% 2.03/0.95  
% 2.03/0.95  --preprocessing_flag                    true
% 2.03/0.95  --time_out_prep_mult                    0.1
% 2.03/0.95  --splitting_mode                        input
% 2.03/0.95  --splitting_grd                         true
% 2.03/0.95  --splitting_cvd                         false
% 2.03/0.95  --splitting_cvd_svl                     false
% 2.03/0.95  --splitting_nvd                         32
% 2.03/0.95  --sub_typing                            true
% 2.03/0.95  --prep_gs_sim                           true
% 2.03/0.95  --prep_unflatten                        true
% 2.03/0.95  --prep_res_sim                          true
% 2.03/0.95  --prep_upred                            true
% 2.03/0.95  --prep_sem_filter                       exhaustive
% 2.03/0.95  --prep_sem_filter_out                   false
% 2.03/0.95  --pred_elim                             true
% 2.03/0.95  --res_sim_input                         true
% 2.03/0.95  --eq_ax_congr_red                       true
% 2.03/0.95  --pure_diseq_elim                       true
% 2.03/0.95  --brand_transform                       false
% 2.03/0.95  --non_eq_to_eq                          false
% 2.03/0.95  --prep_def_merge                        true
% 2.03/0.95  --prep_def_merge_prop_impl              false
% 2.03/0.95  --prep_def_merge_mbd                    true
% 2.03/0.95  --prep_def_merge_tr_red                 false
% 2.03/0.95  --prep_def_merge_tr_cl                  false
% 2.03/0.95  --smt_preprocessing                     true
% 2.03/0.95  --smt_ac_axioms                         fast
% 2.03/0.95  --preprocessed_out                      false
% 2.03/0.95  --preprocessed_stats                    false
% 2.03/0.95  
% 2.03/0.95  ------ Abstraction refinement Options
% 2.03/0.95  
% 2.03/0.95  --abstr_ref                             []
% 2.03/0.95  --abstr_ref_prep                        false
% 2.03/0.95  --abstr_ref_until_sat                   false
% 2.03/0.95  --abstr_ref_sig_restrict                funpre
% 2.03/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.95  --abstr_ref_under                       []
% 2.03/0.95  
% 2.03/0.95  ------ SAT Options
% 2.03/0.95  
% 2.03/0.95  --sat_mode                              false
% 2.03/0.95  --sat_fm_restart_options                ""
% 2.03/0.95  --sat_gr_def                            false
% 2.03/0.95  --sat_epr_types                         true
% 2.03/0.95  --sat_non_cyclic_types                  false
% 2.03/0.95  --sat_finite_models                     false
% 2.03/0.95  --sat_fm_lemmas                         false
% 2.03/0.95  --sat_fm_prep                           false
% 2.03/0.95  --sat_fm_uc_incr                        true
% 2.03/0.95  --sat_out_model                         small
% 2.03/0.95  --sat_out_clauses                       false
% 2.03/0.95  
% 2.03/0.95  ------ QBF Options
% 2.03/0.95  
% 2.03/0.95  --qbf_mode                              false
% 2.03/0.95  --qbf_elim_univ                         false
% 2.03/0.95  --qbf_dom_inst                          none
% 2.03/0.95  --qbf_dom_pre_inst                      false
% 2.03/0.95  --qbf_sk_in                             false
% 2.03/0.95  --qbf_pred_elim                         true
% 2.03/0.95  --qbf_split                             512
% 2.03/0.95  
% 2.03/0.95  ------ BMC1 Options
% 2.03/0.95  
% 2.03/0.95  --bmc1_incremental                      false
% 2.03/0.95  --bmc1_axioms                           reachable_all
% 2.03/0.95  --bmc1_min_bound                        0
% 2.03/0.95  --bmc1_max_bound                        -1
% 2.03/0.95  --bmc1_max_bound_default                -1
% 2.03/0.95  --bmc1_symbol_reachability              true
% 2.03/0.95  --bmc1_property_lemmas                  false
% 2.03/0.95  --bmc1_k_induction                      false
% 2.03/0.95  --bmc1_non_equiv_states                 false
% 2.03/0.95  --bmc1_deadlock                         false
% 2.03/0.95  --bmc1_ucm                              false
% 2.03/0.95  --bmc1_add_unsat_core                   none
% 2.03/0.95  --bmc1_unsat_core_children              false
% 2.03/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.95  --bmc1_out_stat                         full
% 2.03/0.95  --bmc1_ground_init                      false
% 2.03/0.95  --bmc1_pre_inst_next_state              false
% 2.03/0.95  --bmc1_pre_inst_state                   false
% 2.03/0.95  --bmc1_pre_inst_reach_state             false
% 2.03/0.95  --bmc1_out_unsat_core                   false
% 2.03/0.95  --bmc1_aig_witness_out                  false
% 2.03/0.95  --bmc1_verbose                          false
% 2.03/0.95  --bmc1_dump_clauses_tptp                false
% 2.03/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.95  --bmc1_dump_file                        -
% 2.03/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.95  --bmc1_ucm_extend_mode                  1
% 2.03/0.95  --bmc1_ucm_init_mode                    2
% 2.03/0.95  --bmc1_ucm_cone_mode                    none
% 2.03/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.95  --bmc1_ucm_relax_model                  4
% 2.03/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.95  --bmc1_ucm_layered_model                none
% 2.03/0.95  --bmc1_ucm_max_lemma_size               10
% 2.03/0.95  
% 2.03/0.95  ------ AIG Options
% 2.03/0.95  
% 2.03/0.95  --aig_mode                              false
% 2.03/0.95  
% 2.03/0.95  ------ Instantiation Options
% 2.03/0.95  
% 2.03/0.95  --instantiation_flag                    true
% 2.03/0.95  --inst_sos_flag                         false
% 2.03/0.95  --inst_sos_phase                        true
% 2.03/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.95  --inst_lit_sel_side                     num_symb
% 2.03/0.95  --inst_solver_per_active                1400
% 2.03/0.95  --inst_solver_calls_frac                1.
% 2.03/0.95  --inst_passive_queue_type               priority_queues
% 2.03/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.95  --inst_passive_queues_freq              [25;2]
% 2.03/0.95  --inst_dismatching                      true
% 2.03/0.95  --inst_eager_unprocessed_to_passive     true
% 2.03/0.95  --inst_prop_sim_given                   true
% 2.03/0.95  --inst_prop_sim_new                     false
% 2.03/0.95  --inst_subs_new                         false
% 2.03/0.95  --inst_eq_res_simp                      false
% 2.03/0.95  --inst_subs_given                       false
% 2.03/0.95  --inst_orphan_elimination               true
% 2.03/0.95  --inst_learning_loop_flag               true
% 2.03/0.95  --inst_learning_start                   3000
% 2.03/0.95  --inst_learning_factor                  2
% 2.03/0.95  --inst_start_prop_sim_after_learn       3
% 2.03/0.95  --inst_sel_renew                        solver
% 2.03/0.95  --inst_lit_activity_flag                true
% 2.03/0.95  --inst_restr_to_given                   false
% 2.03/0.95  --inst_activity_threshold               500
% 2.03/0.95  --inst_out_proof                        true
% 2.03/0.95  
% 2.03/0.95  ------ Resolution Options
% 2.03/0.95  
% 2.03/0.95  --resolution_flag                       true
% 2.03/0.95  --res_lit_sel                           adaptive
% 2.03/0.95  --res_lit_sel_side                      none
% 2.03/0.95  --res_ordering                          kbo
% 2.03/0.95  --res_to_prop_solver                    active
% 2.03/0.95  --res_prop_simpl_new                    false
% 2.03/0.95  --res_prop_simpl_given                  true
% 2.03/0.95  --res_passive_queue_type                priority_queues
% 2.03/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.95  --res_passive_queues_freq               [15;5]
% 2.03/0.95  --res_forward_subs                      full
% 2.03/0.95  --res_backward_subs                     full
% 2.03/0.95  --res_forward_subs_resolution           true
% 2.03/0.95  --res_backward_subs_resolution          true
% 2.03/0.95  --res_orphan_elimination                true
% 2.03/0.95  --res_time_limit                        2.
% 2.03/0.95  --res_out_proof                         true
% 2.03/0.95  
% 2.03/0.95  ------ Superposition Options
% 2.03/0.95  
% 2.03/0.95  --superposition_flag                    true
% 2.03/0.95  --sup_passive_queue_type                priority_queues
% 2.03/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.95  --demod_completeness_check              fast
% 2.03/0.95  --demod_use_ground                      true
% 2.03/0.95  --sup_to_prop_solver                    passive
% 2.03/0.95  --sup_prop_simpl_new                    true
% 2.03/0.95  --sup_prop_simpl_given                  true
% 2.03/0.95  --sup_fun_splitting                     false
% 2.03/0.95  --sup_smt_interval                      50000
% 2.03/0.95  
% 2.03/0.95  ------ Superposition Simplification Setup
% 2.03/0.95  
% 2.03/0.95  --sup_indices_passive                   []
% 2.03/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_full_bw                           [BwDemod]
% 2.03/0.95  --sup_immed_triv                        [TrivRules]
% 2.03/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_immed_bw_main                     []
% 2.03/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.95  
% 2.03/0.95  ------ Combination Options
% 2.03/0.95  
% 2.03/0.95  --comb_res_mult                         3
% 2.03/0.95  --comb_sup_mult                         2
% 2.03/0.95  --comb_inst_mult                        10
% 2.03/0.95  
% 2.03/0.95  ------ Debug Options
% 2.03/0.95  
% 2.03/0.95  --dbg_backtrace                         false
% 2.03/0.95  --dbg_dump_prop_clauses                 false
% 2.03/0.95  --dbg_dump_prop_clauses_file            -
% 2.03/0.95  --dbg_out_stat                          false
% 2.03/0.95  ------ Parsing...
% 2.03/0.95  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.03/0.95  ------ Proving...
% 2.03/0.95  ------ Problem Properties 
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  clauses                                 15
% 2.03/0.95  conjectures                             4
% 2.03/0.95  EPR                                     3
% 2.03/0.95  Horn                                    9
% 2.03/0.95  unary                                   6
% 2.03/0.95  binary                                  1
% 2.03/0.95  lits                                    35
% 2.03/0.95  lits eq                                 4
% 2.03/0.95  fd_pure                                 0
% 2.03/0.95  fd_pseudo                               0
% 2.03/0.95  fd_cond                                 0
% 2.03/0.95  fd_pseudo_cond                          0
% 2.03/0.95  AC symbols                              0
% 2.03/0.95  
% 2.03/0.95  ------ Schedule dynamic 5 is on 
% 2.03/0.95  
% 2.03/0.95  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  ------ 
% 2.03/0.95  Current options:
% 2.03/0.95  ------ 
% 2.03/0.95  
% 2.03/0.95  ------ Input Options
% 2.03/0.95  
% 2.03/0.95  --out_options                           all
% 2.03/0.95  --tptp_safe_out                         true
% 2.03/0.95  --problem_path                          ""
% 2.03/0.95  --include_path                          ""
% 2.03/0.95  --clausifier                            res/vclausify_rel
% 2.03/0.95  --clausifier_options                    --mode clausify
% 2.03/0.95  --stdin                                 false
% 2.03/0.95  --stats_out                             all
% 2.03/0.95  
% 2.03/0.95  ------ General Options
% 2.03/0.95  
% 2.03/0.95  --fof                                   false
% 2.03/0.95  --time_out_real                         305.
% 2.03/0.95  --time_out_virtual                      -1.
% 2.03/0.95  --symbol_type_check                     false
% 2.03/0.95  --clausify_out                          false
% 2.03/0.95  --sig_cnt_out                           false
% 2.03/0.95  --trig_cnt_out                          false
% 2.03/0.95  --trig_cnt_out_tolerance                1.
% 2.03/0.95  --trig_cnt_out_sk_spl                   false
% 2.03/0.95  --abstr_cl_out                          false
% 2.03/0.95  
% 2.03/0.95  ------ Global Options
% 2.03/0.95  
% 2.03/0.95  --schedule                              default
% 2.03/0.95  --add_important_lit                     false
% 2.03/0.95  --prop_solver_per_cl                    1000
% 2.03/0.95  --min_unsat_core                        false
% 2.03/0.95  --soft_assumptions                      false
% 2.03/0.95  --soft_lemma_size                       3
% 2.03/0.95  --prop_impl_unit_size                   0
% 2.03/0.95  --prop_impl_unit                        []
% 2.03/0.95  --share_sel_clauses                     true
% 2.03/0.95  --reset_solvers                         false
% 2.03/0.95  --bc_imp_inh                            [conj_cone]
% 2.03/0.95  --conj_cone_tolerance                   3.
% 2.03/0.95  --extra_neg_conj                        none
% 2.03/0.95  --large_theory_mode                     true
% 2.03/0.95  --prolific_symb_bound                   200
% 2.03/0.95  --lt_threshold                          2000
% 2.03/0.95  --clause_weak_htbl                      true
% 2.03/0.95  --gc_record_bc_elim                     false
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing Options
% 2.03/0.95  
% 2.03/0.95  --preprocessing_flag                    true
% 2.03/0.95  --time_out_prep_mult                    0.1
% 2.03/0.95  --splitting_mode                        input
% 2.03/0.95  --splitting_grd                         true
% 2.03/0.95  --splitting_cvd                         false
% 2.03/0.95  --splitting_cvd_svl                     false
% 2.03/0.95  --splitting_nvd                         32
% 2.03/0.95  --sub_typing                            true
% 2.03/0.95  --prep_gs_sim                           true
% 2.03/0.95  --prep_unflatten                        true
% 2.03/0.95  --prep_res_sim                          true
% 2.03/0.95  --prep_upred                            true
% 2.03/0.95  --prep_sem_filter                       exhaustive
% 2.03/0.95  --prep_sem_filter_out                   false
% 2.03/0.95  --pred_elim                             true
% 2.03/0.95  --res_sim_input                         true
% 2.03/0.95  --eq_ax_congr_red                       true
% 2.03/0.95  --pure_diseq_elim                       true
% 2.03/0.95  --brand_transform                       false
% 2.03/0.95  --non_eq_to_eq                          false
% 2.03/0.95  --prep_def_merge                        true
% 2.03/0.95  --prep_def_merge_prop_impl              false
% 2.03/0.95  --prep_def_merge_mbd                    true
% 2.03/0.95  --prep_def_merge_tr_red                 false
% 2.03/0.95  --prep_def_merge_tr_cl                  false
% 2.03/0.95  --smt_preprocessing                     true
% 2.03/0.95  --smt_ac_axioms                         fast
% 2.03/0.95  --preprocessed_out                      false
% 2.03/0.95  --preprocessed_stats                    false
% 2.03/0.95  
% 2.03/0.95  ------ Abstraction refinement Options
% 2.03/0.95  
% 2.03/0.95  --abstr_ref                             []
% 2.03/0.95  --abstr_ref_prep                        false
% 2.03/0.95  --abstr_ref_until_sat                   false
% 2.03/0.95  --abstr_ref_sig_restrict                funpre
% 2.03/0.95  --abstr_ref_af_restrict_to_split_sk     false
% 2.03/0.95  --abstr_ref_under                       []
% 2.03/0.95  
% 2.03/0.95  ------ SAT Options
% 2.03/0.95  
% 2.03/0.95  --sat_mode                              false
% 2.03/0.95  --sat_fm_restart_options                ""
% 2.03/0.95  --sat_gr_def                            false
% 2.03/0.95  --sat_epr_types                         true
% 2.03/0.95  --sat_non_cyclic_types                  false
% 2.03/0.95  --sat_finite_models                     false
% 2.03/0.95  --sat_fm_lemmas                         false
% 2.03/0.95  --sat_fm_prep                           false
% 2.03/0.95  --sat_fm_uc_incr                        true
% 2.03/0.95  --sat_out_model                         small
% 2.03/0.95  --sat_out_clauses                       false
% 2.03/0.95  
% 2.03/0.95  ------ QBF Options
% 2.03/0.95  
% 2.03/0.95  --qbf_mode                              false
% 2.03/0.95  --qbf_elim_univ                         false
% 2.03/0.95  --qbf_dom_inst                          none
% 2.03/0.95  --qbf_dom_pre_inst                      false
% 2.03/0.95  --qbf_sk_in                             false
% 2.03/0.95  --qbf_pred_elim                         true
% 2.03/0.95  --qbf_split                             512
% 2.03/0.95  
% 2.03/0.95  ------ BMC1 Options
% 2.03/0.95  
% 2.03/0.95  --bmc1_incremental                      false
% 2.03/0.95  --bmc1_axioms                           reachable_all
% 2.03/0.95  --bmc1_min_bound                        0
% 2.03/0.95  --bmc1_max_bound                        -1
% 2.03/0.95  --bmc1_max_bound_default                -1
% 2.03/0.95  --bmc1_symbol_reachability              true
% 2.03/0.95  --bmc1_property_lemmas                  false
% 2.03/0.95  --bmc1_k_induction                      false
% 2.03/0.95  --bmc1_non_equiv_states                 false
% 2.03/0.95  --bmc1_deadlock                         false
% 2.03/0.95  --bmc1_ucm                              false
% 2.03/0.95  --bmc1_add_unsat_core                   none
% 2.03/0.95  --bmc1_unsat_core_children              false
% 2.03/0.95  --bmc1_unsat_core_extrapolate_axioms    false
% 2.03/0.95  --bmc1_out_stat                         full
% 2.03/0.95  --bmc1_ground_init                      false
% 2.03/0.95  --bmc1_pre_inst_next_state              false
% 2.03/0.95  --bmc1_pre_inst_state                   false
% 2.03/0.95  --bmc1_pre_inst_reach_state             false
% 2.03/0.95  --bmc1_out_unsat_core                   false
% 2.03/0.95  --bmc1_aig_witness_out                  false
% 2.03/0.95  --bmc1_verbose                          false
% 2.03/0.95  --bmc1_dump_clauses_tptp                false
% 2.03/0.95  --bmc1_dump_unsat_core_tptp             false
% 2.03/0.95  --bmc1_dump_file                        -
% 2.03/0.95  --bmc1_ucm_expand_uc_limit              128
% 2.03/0.95  --bmc1_ucm_n_expand_iterations          6
% 2.03/0.95  --bmc1_ucm_extend_mode                  1
% 2.03/0.95  --bmc1_ucm_init_mode                    2
% 2.03/0.95  --bmc1_ucm_cone_mode                    none
% 2.03/0.95  --bmc1_ucm_reduced_relation_type        0
% 2.03/0.95  --bmc1_ucm_relax_model                  4
% 2.03/0.95  --bmc1_ucm_full_tr_after_sat            true
% 2.03/0.95  --bmc1_ucm_expand_neg_assumptions       false
% 2.03/0.95  --bmc1_ucm_layered_model                none
% 2.03/0.95  --bmc1_ucm_max_lemma_size               10
% 2.03/0.95  
% 2.03/0.95  ------ AIG Options
% 2.03/0.95  
% 2.03/0.95  --aig_mode                              false
% 2.03/0.95  
% 2.03/0.95  ------ Instantiation Options
% 2.03/0.95  
% 2.03/0.95  --instantiation_flag                    true
% 2.03/0.95  --inst_sos_flag                         false
% 2.03/0.95  --inst_sos_phase                        true
% 2.03/0.95  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.03/0.95  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.03/0.95  --inst_lit_sel_side                     none
% 2.03/0.95  --inst_solver_per_active                1400
% 2.03/0.95  --inst_solver_calls_frac                1.
% 2.03/0.95  --inst_passive_queue_type               priority_queues
% 2.03/0.95  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.03/0.95  --inst_passive_queues_freq              [25;2]
% 2.03/0.95  --inst_dismatching                      true
% 2.03/0.95  --inst_eager_unprocessed_to_passive     true
% 2.03/0.95  --inst_prop_sim_given                   true
% 2.03/0.95  --inst_prop_sim_new                     false
% 2.03/0.95  --inst_subs_new                         false
% 2.03/0.95  --inst_eq_res_simp                      false
% 2.03/0.95  --inst_subs_given                       false
% 2.03/0.95  --inst_orphan_elimination               true
% 2.03/0.95  --inst_learning_loop_flag               true
% 2.03/0.95  --inst_learning_start                   3000
% 2.03/0.95  --inst_learning_factor                  2
% 2.03/0.95  --inst_start_prop_sim_after_learn       3
% 2.03/0.95  --inst_sel_renew                        solver
% 2.03/0.95  --inst_lit_activity_flag                true
% 2.03/0.95  --inst_restr_to_given                   false
% 2.03/0.95  --inst_activity_threshold               500
% 2.03/0.95  --inst_out_proof                        true
% 2.03/0.95  
% 2.03/0.95  ------ Resolution Options
% 2.03/0.95  
% 2.03/0.95  --resolution_flag                       false
% 2.03/0.95  --res_lit_sel                           adaptive
% 2.03/0.95  --res_lit_sel_side                      none
% 2.03/0.95  --res_ordering                          kbo
% 2.03/0.95  --res_to_prop_solver                    active
% 2.03/0.95  --res_prop_simpl_new                    false
% 2.03/0.95  --res_prop_simpl_given                  true
% 2.03/0.95  --res_passive_queue_type                priority_queues
% 2.03/0.95  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.03/0.95  --res_passive_queues_freq               [15;5]
% 2.03/0.95  --res_forward_subs                      full
% 2.03/0.95  --res_backward_subs                     full
% 2.03/0.95  --res_forward_subs_resolution           true
% 2.03/0.95  --res_backward_subs_resolution          true
% 2.03/0.95  --res_orphan_elimination                true
% 2.03/0.95  --res_time_limit                        2.
% 2.03/0.95  --res_out_proof                         true
% 2.03/0.95  
% 2.03/0.95  ------ Superposition Options
% 2.03/0.95  
% 2.03/0.95  --superposition_flag                    true
% 2.03/0.95  --sup_passive_queue_type                priority_queues
% 2.03/0.95  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.03/0.95  --sup_passive_queues_freq               [8;1;4]
% 2.03/0.95  --demod_completeness_check              fast
% 2.03/0.95  --demod_use_ground                      true
% 2.03/0.95  --sup_to_prop_solver                    passive
% 2.03/0.95  --sup_prop_simpl_new                    true
% 2.03/0.95  --sup_prop_simpl_given                  true
% 2.03/0.95  --sup_fun_splitting                     false
% 2.03/0.95  --sup_smt_interval                      50000
% 2.03/0.95  
% 2.03/0.95  ------ Superposition Simplification Setup
% 2.03/0.95  
% 2.03/0.95  --sup_indices_passive                   []
% 2.03/0.95  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.03/0.95  --sup_full_triv                         [TrivRules;PropSubs]
% 2.03/0.95  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_full_bw                           [BwDemod]
% 2.03/0.95  --sup_immed_triv                        [TrivRules]
% 2.03/0.95  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.03/0.95  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_immed_bw_main                     []
% 2.03/0.95  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.95  --sup_input_triv                        [Unflattening;TrivRules]
% 2.03/0.95  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.03/0.95  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.03/0.95  
% 2.03/0.95  ------ Combination Options
% 2.03/0.95  
% 2.03/0.95  --comb_res_mult                         3
% 2.03/0.95  --comb_sup_mult                         2
% 2.03/0.95  --comb_inst_mult                        10
% 2.03/0.95  
% 2.03/0.95  ------ Debug Options
% 2.03/0.95  
% 2.03/0.95  --dbg_backtrace                         false
% 2.03/0.95  --dbg_dump_prop_clauses                 false
% 2.03/0.95  --dbg_dump_prop_clauses_file            -
% 2.03/0.95  --dbg_out_stat                          false
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  ------ Proving...
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  % SZS status Theorem for theBenchmark.p
% 2.03/0.95  
% 2.03/0.95  % SZS output start CNFRefutation for theBenchmark.p
% 2.03/0.95  
% 2.03/0.95  fof(f8,conjecture,(
% 2.03/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f9,negated_conjecture,(
% 2.03/0.95    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.03/0.95    inference(negated_conjecture,[],[f8])).
% 2.03/0.95  
% 2.03/0.95  fof(f18,plain,(
% 2.03/0.95    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.03/0.95    inference(ennf_transformation,[],[f9])).
% 2.03/0.95  
% 2.03/0.95  fof(f19,plain,(
% 2.03/0.95    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.03/0.95    inference(flattening,[],[f18])).
% 2.03/0.95  
% 2.03/0.95  fof(f31,plain,(
% 2.03/0.95    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK4) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK4))) & r2_hidden(sK4,X1) & m1_subset_1(sK4,u1_struct_0(X0)))) )),
% 2.03/0.95    introduced(choice_axiom,[])).
% 2.03/0.95  
% 2.03/0.95  fof(f30,plain,(
% 2.03/0.95    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK3,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK3) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.03/0.95    introduced(choice_axiom,[])).
% 2.03/0.95  
% 2.03/0.95  fof(f29,plain,(
% 2.03/0.95    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK2),X2) != k9_subset_1(u1_struct_0(sK2),X1,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK2))) & v2_tex_2(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.03/0.95    introduced(choice_axiom,[])).
% 2.03/0.95  
% 2.03/0.95  fof(f32,plain,(
% 2.03/0.95    ((k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) & r2_hidden(sK4,sK3) & m1_subset_1(sK4,u1_struct_0(sK2))) & v2_tex_2(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.03/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f19,f31,f30,f29])).
% 2.03/0.95  
% 2.03/0.95  fof(f50,plain,(
% 2.03/0.95    m1_subset_1(sK4,u1_struct_0(sK2))),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f6,axiom,(
% 2.03/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f14,plain,(
% 2.03/0.95    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.03/0.95    inference(ennf_transformation,[],[f6])).
% 2.03/0.95  
% 2.03/0.95  fof(f15,plain,(
% 2.03/0.95    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.03/0.95    inference(flattening,[],[f14])).
% 2.03/0.95  
% 2.03/0.95  fof(f40,plain,(
% 2.03/0.95    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f15])).
% 2.03/0.95  
% 2.03/0.95  fof(f48,plain,(
% 2.03/0.95    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f1,axiom,(
% 2.03/0.95    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f20,plain,(
% 2.03/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.95    inference(nnf_transformation,[],[f1])).
% 2.03/0.95  
% 2.03/0.95  fof(f21,plain,(
% 2.03/0.95    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.95    inference(rectify,[],[f20])).
% 2.03/0.95  
% 2.03/0.95  fof(f22,plain,(
% 2.03/0.95    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.03/0.95    introduced(choice_axiom,[])).
% 2.03/0.95  
% 2.03/0.95  fof(f23,plain,(
% 2.03/0.95    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.03/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f22])).
% 2.03/0.95  
% 2.03/0.95  fof(f33,plain,(
% 2.03/0.95    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f23])).
% 2.03/0.95  
% 2.03/0.95  fof(f51,plain,(
% 2.03/0.95    r2_hidden(sK4,sK3)),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f2,axiom,(
% 2.03/0.95    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f10,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 2.03/0.95    inference(ennf_transformation,[],[f2])).
% 2.03/0.95  
% 2.03/0.95  fof(f35,plain,(
% 2.03/0.95    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f10])).
% 2.03/0.95  
% 2.03/0.95  fof(f5,axiom,(
% 2.03/0.95    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f12,plain,(
% 2.03/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.03/0.95    inference(ennf_transformation,[],[f5])).
% 2.03/0.95  
% 2.03/0.95  fof(f13,plain,(
% 2.03/0.95    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.03/0.95    inference(flattening,[],[f12])).
% 2.03/0.95  
% 2.03/0.95  fof(f39,plain,(
% 2.03/0.95    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f13])).
% 2.03/0.95  
% 2.03/0.95  fof(f4,axiom,(
% 2.03/0.95    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f24,plain,(
% 2.03/0.95    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.03/0.95    inference(nnf_transformation,[],[f4])).
% 2.03/0.95  
% 2.03/0.95  fof(f37,plain,(
% 2.03/0.95    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.03/0.95    inference(cnf_transformation,[],[f24])).
% 2.03/0.95  
% 2.03/0.95  fof(f7,axiom,(
% 2.03/0.95    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f16,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.03/0.95    inference(ennf_transformation,[],[f7])).
% 2.03/0.95  
% 2.03/0.95  fof(f17,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.95    inference(flattening,[],[f16])).
% 2.03/0.95  
% 2.03/0.95  fof(f25,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.95    inference(nnf_transformation,[],[f17])).
% 2.03/0.95  
% 2.03/0.95  fof(f26,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.95    inference(rectify,[],[f25])).
% 2.03/0.95  
% 2.03/0.95  fof(f27,plain,(
% 2.03/0.95    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.03/0.95    introduced(choice_axiom,[])).
% 2.03/0.95  
% 2.03/0.95  fof(f28,plain,(
% 2.03/0.95    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.03/0.95    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f26,f27])).
% 2.03/0.95  
% 2.03/0.95  fof(f41,plain,(
% 2.03/0.95    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f28])).
% 2.03/0.95  
% 2.03/0.95  fof(f47,plain,(
% 2.03/0.95    l1_pre_topc(sK2)),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f45,plain,(
% 2.03/0.95    ~v2_struct_0(sK2)),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f46,plain,(
% 2.03/0.95    v2_pre_topc(sK2)),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f52,plain,(
% 2.03/0.95    k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4)))),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  fof(f3,axiom,(
% 2.03/0.95    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.03/0.95    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.03/0.95  
% 2.03/0.95  fof(f11,plain,(
% 2.03/0.95    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.03/0.95    inference(ennf_transformation,[],[f3])).
% 2.03/0.95  
% 2.03/0.95  fof(f36,plain,(
% 2.03/0.95    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.03/0.95    inference(cnf_transformation,[],[f11])).
% 2.03/0.95  
% 2.03/0.95  fof(f49,plain,(
% 2.03/0.95    v2_tex_2(sK3,sK2)),
% 2.03/0.95    inference(cnf_transformation,[],[f32])).
% 2.03/0.95  
% 2.03/0.95  cnf(c_14,negated_conjecture,
% 2.03/0.95      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.03/0.95      inference(cnf_transformation,[],[f50]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_935,negated_conjecture,
% 2.03/0.95      ( m1_subset_1(sK4,u1_struct_0(sK2)) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_14]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1209,plain,
% 2.03/0.95      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_935]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_7,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0,X1)
% 2.03/0.95      | v1_xboole_0(X1)
% 2.03/0.95      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.03/0.95      inference(cnf_transformation,[],[f40]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_937,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0_47,X1_47)
% 2.03/0.95      | v1_xboole_0(X1_47)
% 2.03/0.95      | k6_domain_1(X1_47,X0_47) = k1_tarski(X0_47) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_7]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1208,plain,
% 2.03/0.95      ( k6_domain_1(X0_47,X1_47) = k1_tarski(X1_47)
% 2.03/0.95      | m1_subset_1(X1_47,X0_47) != iProver_top
% 2.03/0.95      | v1_xboole_0(X0_47) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1565,plain,
% 2.03/0.95      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4)
% 2.03/0.95      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.95      inference(superposition,[status(thm)],[c_1209,c_1208]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_16,negated_conjecture,
% 2.03/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.03/0.95      inference(cnf_transformation,[],[f48]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1,plain,
% 2.03/0.95      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.03/0.95      inference(cnf_transformation,[],[f33]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_13,negated_conjecture,
% 2.03/0.95      ( r2_hidden(sK4,sK3) ),
% 2.03/0.95      inference(cnf_transformation,[],[f51]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_275,plain,
% 2.03/0.95      ( ~ v1_xboole_0(X0) | sK3 != X0 | sK4 != X1 ),
% 2.03/0.95      inference(resolution_lifted,[status(thm)],[c_1,c_13]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_276,plain,
% 2.03/0.95      ( ~ v1_xboole_0(sK3) ),
% 2.03/0.95      inference(unflattening,[status(thm)],[c_275]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1337,plain,
% 2.03/0.95      ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
% 2.03/0.95      | v1_xboole_0(u1_struct_0(sK2))
% 2.03/0.95      | k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_937]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_2,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.03/0.95      | ~ v1_xboole_0(X1)
% 2.03/0.95      | v1_xboole_0(X0) ),
% 2.03/0.95      inference(cnf_transformation,[],[f35]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_939,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.03/0.95      | ~ v1_xboole_0(X1_47)
% 2.03/0.95      | v1_xboole_0(X0_47) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_2]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1396,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | v1_xboole_0(X0_47)
% 2.03/0.95      | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_939]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1398,plain,
% 2.03/0.95      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ v1_xboole_0(u1_struct_0(sK2))
% 2.03/0.95      | v1_xboole_0(sK3) ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_1396]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1758,plain,
% 2.03/0.95      ( k6_domain_1(u1_struct_0(sK2),sK4) = k1_tarski(sK4) ),
% 2.03/0.95      inference(global_propositional_subsumption,
% 2.03/0.95                [status(thm)],
% 2.03/0.95                [c_1565,c_16,c_14,c_276,c_1337,c_1398]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_6,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0,X1)
% 2.03/0.95      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.03/0.95      | v1_xboole_0(X1) ),
% 2.03/0.95      inference(cnf_transformation,[],[f39]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_938,plain,
% 2.03/0.95      ( ~ m1_subset_1(X0_47,X1_47)
% 2.03/0.95      | m1_subset_1(k6_domain_1(X1_47,X0_47),k1_zfmisc_1(X1_47))
% 2.03/0.95      | v1_xboole_0(X1_47) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_6]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1207,plain,
% 2.03/0.95      ( m1_subset_1(X0_47,X1_47) != iProver_top
% 2.03/0.95      | m1_subset_1(k6_domain_1(X1_47,X0_47),k1_zfmisc_1(X1_47)) = iProver_top
% 2.03/0.95      | v1_xboole_0(X1_47) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1762,plain,
% 2.03/0.95      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 2.03/0.95      | m1_subset_1(sK4,u1_struct_0(sK2)) != iProver_top
% 2.03/0.95      | v1_xboole_0(u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.95      inference(superposition,[status(thm)],[c_1758,c_1207]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_23,plain,
% 2.03/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_25,plain,
% 2.03/0.95      ( m1_subset_1(sK4,u1_struct_0(sK2)) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_277,plain,
% 2.03/0.95      ( v1_xboole_0(sK3) != iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1397,plain,
% 2.03/0.95      ( m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.03/0.95      | v1_xboole_0(X0_47) = iProver_top
% 2.03/0.95      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_1396]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1399,plain,
% 2.03/0.95      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.03/0.95      | v1_xboole_0(u1_struct_0(sK2)) != iProver_top
% 2.03/0.95      | v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_1397]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_2017,plain,
% 2.03/0.95      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.03/0.95      inference(global_propositional_subsumption,
% 2.03/0.95                [status(thm)],
% 2.03/0.95                [c_1762,c_23,c_25,c_277,c_1399]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_5,plain,
% 2.03/0.95      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.03/0.95      inference(cnf_transformation,[],[f37]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_142,plain,
% 2.03/0.95      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.03/0.95      inference(prop_impl,[status(thm)],[c_5]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_11,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,X1)
% 2.03/0.95      | ~ r1_tarski(X2,X0)
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.95      | v2_struct_0(X1)
% 2.03/0.95      | ~ v2_pre_topc(X1)
% 2.03/0.95      | ~ l1_pre_topc(X1)
% 2.03/0.95      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.03/0.95      inference(cnf_transformation,[],[f41]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_17,negated_conjecture,
% 2.03/0.95      ( l1_pre_topc(sK2) ),
% 2.03/0.95      inference(cnf_transformation,[],[f47]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_289,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,X1)
% 2.03/0.95      | ~ r1_tarski(X2,X0)
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.95      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.03/0.95      | v2_struct_0(X1)
% 2.03/0.95      | ~ v2_pre_topc(X1)
% 2.03/0.95      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.03/0.95      | sK2 != X1 ),
% 2.03/0.95      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_290,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,sK2)
% 2.03/0.95      | ~ r1_tarski(X1,X0)
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | v2_struct_0(sK2)
% 2.03/0.95      | ~ v2_pre_topc(sK2)
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.03/0.95      inference(unflattening,[status(thm)],[c_289]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_19,negated_conjecture,
% 2.03/0.95      ( ~ v2_struct_0(sK2) ),
% 2.03/0.95      inference(cnf_transformation,[],[f45]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_18,negated_conjecture,
% 2.03/0.95      ( v2_pre_topc(sK2) ),
% 2.03/0.95      inference(cnf_transformation,[],[f46]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_294,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,sK2)
% 2.03/0.95      | ~ r1_tarski(X1,X0)
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.03/0.95      inference(global_propositional_subsumption,
% 2.03/0.95                [status(thm)],
% 2.03/0.95                [c_290,c_19,c_18]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_295,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,sK2)
% 2.03/0.95      | ~ r1_tarski(X1,X0)
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.03/0.95      inference(renaming,[status(thm)],[c_294]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_509,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,sK2)
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 2.03/0.95      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | X3 != X1
% 2.03/0.95      | X0 != X2
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X3)) = X3 ),
% 2.03/0.95      inference(resolution_lifted,[status(thm)],[c_142,c_295]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_510,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0,sK2)
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
% 2.03/0.95      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 2.03/0.95      inference(unflattening,[status(thm)],[c_509]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_927,plain,
% 2.03/0.95      ( ~ v2_tex_2(X0_47,sK2)
% 2.03/0.95      | ~ m1_subset_1(X1_47,k1_zfmisc_1(X0_47))
% 2.03/0.95      | ~ m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | ~ m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.03/0.95      | k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,X1_47)) = X1_47 ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_510]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1217,plain,
% 2.03/0.95      ( k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,X1_47)) = X1_47
% 2.03/0.95      | v2_tex_2(X0_47,sK2) != iProver_top
% 2.03/0.95      | m1_subset_1(X1_47,k1_zfmisc_1(X0_47)) != iProver_top
% 2.03/0.95      | m1_subset_1(X1_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.03/0.95      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_927]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_2023,plain,
% 2.03/0.95      ( k9_subset_1(u1_struct_0(sK2),X0_47,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4)
% 2.03/0.95      | v2_tex_2(X0_47,sK2) != iProver_top
% 2.03/0.95      | m1_subset_1(X0_47,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.03/0.95      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(X0_47)) != iProver_top ),
% 2.03/0.95      inference(superposition,[status(thm)],[c_2017,c_1217]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_2046,plain,
% 2.03/0.95      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) = k1_tarski(sK4)
% 2.03/0.95      | v2_tex_2(sK3,sK2) != iProver_top
% 2.03/0.95      | m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) != iProver_top
% 2.03/0.95      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_2023]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_12,negated_conjecture,
% 2.03/0.95      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.03/0.95      inference(cnf_transformation,[],[f52]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_936,negated_conjecture,
% 2.03/0.95      ( k6_domain_1(u1_struct_0(sK2),sK4) != k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k6_domain_1(u1_struct_0(sK2),sK4))) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_12]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1761,plain,
% 2.03/0.95      ( k9_subset_1(u1_struct_0(sK2),sK3,k2_pre_topc(sK2,k1_tarski(sK4))) != k1_tarski(sK4) ),
% 2.03/0.95      inference(demodulation,[status(thm)],[c_1758,c_936]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_3,plain,
% 2.03/0.95      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.03/0.95      inference(cnf_transformation,[],[f36]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_268,plain,
% 2.03/0.95      ( m1_subset_1(X0,X1) | sK3 != X1 | sK4 != X0 ),
% 2.03/0.95      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_269,plain,
% 2.03/0.95      ( m1_subset_1(sK4,sK3) ),
% 2.03/0.95      inference(unflattening,[status(thm)],[c_268]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_931,plain,
% 2.03/0.95      ( m1_subset_1(sK4,sK3) ),
% 2.03/0.95      inference(subtyping,[status(esa)],[c_269]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1213,plain,
% 2.03/0.95      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1567,plain,
% 2.03/0.95      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4)
% 2.03/0.95      | v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.95      inference(superposition,[status(thm)],[c_1213,c_1208]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1343,plain,
% 2.03/0.95      ( ~ m1_subset_1(sK4,sK3)
% 2.03/0.95      | v1_xboole_0(sK3)
% 2.03/0.95      | k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.03/0.95      inference(instantiation,[status(thm)],[c_937]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1752,plain,
% 2.03/0.95      ( k6_domain_1(sK3,sK4) = k1_tarski(sK4) ),
% 2.03/0.95      inference(global_propositional_subsumption,
% 2.03/0.95                [status(thm)],
% 2.03/0.95                [c_1567,c_269,c_276,c_1343]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_1755,plain,
% 2.03/0.95      ( m1_subset_1(k1_tarski(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 2.03/0.95      | m1_subset_1(sK4,sK3) != iProver_top
% 2.03/0.95      | v1_xboole_0(sK3) = iProver_top ),
% 2.03/0.95      inference(superposition,[status(thm)],[c_1752,c_1207]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_270,plain,
% 2.03/0.95      ( m1_subset_1(sK4,sK3) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_269]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_15,negated_conjecture,
% 2.03/0.95      ( v2_tex_2(sK3,sK2) ),
% 2.03/0.95      inference(cnf_transformation,[],[f49]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(c_24,plain,
% 2.03/0.95      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 2.03/0.95      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.03/0.95  
% 2.03/0.95  cnf(contradiction,plain,
% 2.03/0.95      ( $false ),
% 2.03/0.95      inference(minisat,
% 2.03/0.95                [status(thm)],
% 2.03/0.95                [c_2046,c_1761,c_1755,c_277,c_270,c_24,c_23]) ).
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  % SZS output end CNFRefutation for theBenchmark.p
% 2.03/0.95  
% 2.03/0.95  ------                               Statistics
% 2.03/0.95  
% 2.03/0.95  ------ General
% 2.03/0.95  
% 2.03/0.95  abstr_ref_over_cycles:                  0
% 2.03/0.95  abstr_ref_under_cycles:                 0
% 2.03/0.95  gc_basic_clause_elim:                   0
% 2.03/0.95  forced_gc_time:                         0
% 2.03/0.95  parsing_time:                           0.008
% 2.03/0.95  unif_index_cands_time:                  0.
% 2.03/0.95  unif_index_add_time:                    0.
% 2.03/0.95  orderings_time:                         0.
% 2.03/0.95  out_proof_time:                         0.007
% 2.03/0.95  total_time:                             0.084
% 2.03/0.95  num_of_symbols:                         53
% 2.03/0.95  num_of_terms:                           1593
% 2.03/0.95  
% 2.03/0.95  ------ Preprocessing
% 2.03/0.95  
% 2.03/0.95  num_of_splits:                          0
% 2.03/0.95  num_of_split_atoms:                     0
% 2.03/0.95  num_of_reused_defs:                     0
% 2.03/0.95  num_eq_ax_congr_red:                    16
% 2.03/0.95  num_of_sem_filtered_clauses:            1
% 2.03/0.95  num_of_subtypes:                        3
% 2.03/0.95  monotx_restored_types:                  0
% 2.03/0.95  sat_num_of_epr_types:                   0
% 2.03/0.95  sat_num_of_non_cyclic_types:            0
% 2.03/0.95  sat_guarded_non_collapsed_types:        1
% 2.03/0.95  num_pure_diseq_elim:                    0
% 2.03/0.95  simp_replaced_by:                       0
% 2.03/0.95  res_preprocessed:                       86
% 2.03/0.95  prep_upred:                             0
% 2.03/0.95  prep_unflattend:                        23
% 2.03/0.95  smt_new_axioms:                         0
% 2.03/0.95  pred_elim_cands:                        3
% 2.03/0.95  pred_elim:                              5
% 2.03/0.95  pred_elim_cl:                           5
% 2.03/0.95  pred_elim_cycles:                       8
% 2.03/0.95  merged_defs:                            2
% 2.03/0.95  merged_defs_ncl:                        0
% 2.03/0.95  bin_hyper_res:                          3
% 2.03/0.95  prep_cycles:                            4
% 2.03/0.95  pred_elim_time:                         0.011
% 2.03/0.95  splitting_time:                         0.
% 2.03/0.95  sem_filter_time:                        0.
% 2.03/0.95  monotx_time:                            0.
% 2.03/0.95  subtype_inf_time:                       0.
% 2.03/0.95  
% 2.03/0.95  ------ Problem properties
% 2.03/0.95  
% 2.03/0.95  clauses:                                15
% 2.03/0.95  conjectures:                            4
% 2.03/0.95  epr:                                    3
% 2.03/0.95  horn:                                   9
% 2.03/0.95  ground:                                 6
% 2.03/0.95  unary:                                  6
% 2.03/0.95  binary:                                 1
% 2.03/0.95  lits:                                   35
% 2.03/0.95  lits_eq:                                4
% 2.03/0.95  fd_pure:                                0
% 2.03/0.95  fd_pseudo:                              0
% 2.03/0.95  fd_cond:                                0
% 2.03/0.95  fd_pseudo_cond:                         0
% 2.03/0.95  ac_symbols:                             0
% 2.03/0.95  
% 2.03/0.95  ------ Propositional Solver
% 2.03/0.95  
% 2.03/0.95  prop_solver_calls:                      26
% 2.03/0.95  prop_fast_solver_calls:                 606
% 2.03/0.95  smt_solver_calls:                       0
% 2.03/0.95  smt_fast_solver_calls:                  0
% 2.03/0.95  prop_num_of_clauses:                    540
% 2.03/0.95  prop_preprocess_simplified:             2584
% 2.03/0.95  prop_fo_subsumed:                       17
% 2.03/0.95  prop_solver_time:                       0.
% 2.03/0.95  smt_solver_time:                        0.
% 2.03/0.95  smt_fast_solver_time:                   0.
% 2.03/0.95  prop_fast_solver_time:                  0.
% 2.03/0.95  prop_unsat_core_time:                   0.
% 2.03/0.95  
% 2.03/0.95  ------ QBF
% 2.03/0.95  
% 2.03/0.95  qbf_q_res:                              0
% 2.03/0.95  qbf_num_tautologies:                    0
% 2.03/0.95  qbf_prep_cycles:                        0
% 2.03/0.95  
% 2.03/0.95  ------ BMC1
% 2.03/0.95  
% 2.03/0.95  bmc1_current_bound:                     -1
% 2.03/0.95  bmc1_last_solved_bound:                 -1
% 2.03/0.95  bmc1_unsat_core_size:                   -1
% 2.03/0.95  bmc1_unsat_core_parents_size:           -1
% 2.03/0.95  bmc1_merge_next_fun:                    0
% 2.03/0.95  bmc1_unsat_core_clauses_time:           0.
% 2.03/0.95  
% 2.03/0.95  ------ Instantiation
% 2.03/0.95  
% 2.03/0.95  inst_num_of_clauses:                    149
% 2.03/0.95  inst_num_in_passive:                    12
% 2.03/0.95  inst_num_in_active:                     96
% 2.03/0.95  inst_num_in_unprocessed:                41
% 2.03/0.95  inst_num_of_loops:                      100
% 2.03/0.95  inst_num_of_learning_restarts:          0
% 2.03/0.95  inst_num_moves_active_passive:          2
% 2.03/0.95  inst_lit_activity:                      0
% 2.03/0.95  inst_lit_activity_moves:                0
% 2.03/0.95  inst_num_tautologies:                   0
% 2.03/0.95  inst_num_prop_implied:                  0
% 2.03/0.95  inst_num_existing_simplified:           0
% 2.03/0.95  inst_num_eq_res_simplified:             0
% 2.03/0.95  inst_num_child_elim:                    0
% 2.03/0.95  inst_num_of_dismatching_blockings:      12
% 2.03/0.95  inst_num_of_non_proper_insts:           123
% 2.03/0.95  inst_num_of_duplicates:                 0
% 2.03/0.95  inst_inst_num_from_inst_to_res:         0
% 2.03/0.95  inst_dismatching_checking_time:         0.
% 2.03/0.95  
% 2.03/0.95  ------ Resolution
% 2.03/0.95  
% 2.03/0.95  res_num_of_clauses:                     0
% 2.03/0.95  res_num_in_passive:                     0
% 2.03/0.95  res_num_in_active:                      0
% 2.03/0.95  res_num_of_loops:                       90
% 2.03/0.95  res_forward_subset_subsumed:            6
% 2.03/0.95  res_backward_subset_subsumed:           0
% 2.03/0.95  res_forward_subsumed:                   0
% 2.03/0.95  res_backward_subsumed:                  0
% 2.03/0.95  res_forward_subsumption_resolution:     0
% 2.03/0.95  res_backward_subsumption_resolution:    0
% 2.03/0.95  res_clause_to_clause_subsumption:       89
% 2.03/0.95  res_orphan_elimination:                 0
% 2.03/0.95  res_tautology_del:                      20
% 2.03/0.95  res_num_eq_res_simplified:              0
% 2.03/0.95  res_num_sel_changes:                    0
% 2.03/0.95  res_moves_from_active_to_pass:          0
% 2.03/0.95  
% 2.03/0.95  ------ Superposition
% 2.03/0.95  
% 2.03/0.95  sup_time_total:                         0.
% 2.03/0.95  sup_time_generating:                    0.
% 2.03/0.95  sup_time_sim_full:                      0.
% 2.03/0.95  sup_time_sim_immed:                     0.
% 2.03/0.95  
% 2.03/0.95  sup_num_of_clauses:                     32
% 2.03/0.95  sup_num_in_active:                      19
% 2.03/0.95  sup_num_in_passive:                     13
% 2.03/0.95  sup_num_of_loops:                       19
% 2.03/0.95  sup_fw_superposition:                   12
% 2.03/0.95  sup_bw_superposition:                   8
% 2.03/0.95  sup_immediate_simplified:               0
% 2.03/0.95  sup_given_eliminated:                   0
% 2.03/0.95  comparisons_done:                       0
% 2.03/0.95  comparisons_avoided:                    0
% 2.03/0.95  
% 2.03/0.95  ------ Simplifications
% 2.03/0.95  
% 2.03/0.95  
% 2.03/0.95  sim_fw_subset_subsumed:                 1
% 2.03/0.95  sim_bw_subset_subsumed:                 0
% 2.03/0.95  sim_fw_subsumed:                        0
% 2.03/0.95  sim_bw_subsumed:                        0
% 2.03/0.95  sim_fw_subsumption_res:                 0
% 2.03/0.95  sim_bw_subsumption_res:                 0
% 2.03/0.95  sim_tautology_del:                      1
% 2.03/0.95  sim_eq_tautology_del:                   0
% 2.03/0.95  sim_eq_res_simp:                        0
% 2.03/0.95  sim_fw_demodulated:                     0
% 2.03/0.95  sim_bw_demodulated:                     1
% 2.03/0.95  sim_light_normalised:                   0
% 2.03/0.95  sim_joinable_taut:                      0
% 2.03/0.95  sim_joinable_simp:                      0
% 2.03/0.95  sim_ac_normalised:                      0
% 2.03/0.95  sim_smt_subsumption:                    0
% 2.03/0.95  
%------------------------------------------------------------------------------
