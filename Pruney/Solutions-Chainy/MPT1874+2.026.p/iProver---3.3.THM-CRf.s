%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:32 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 196 expanded)
%              Number of clauses        :   60 (  64 expanded)
%              Number of leaves         :   18 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :  441 (1026 expanded)
%              Number of equality atoms :   70 ( 155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f27,plain,(
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

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(flattening,[],[f19])).

fof(f32,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1)
        & r1_tarski(sK2(X0,X1),X1)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f21,plain,(
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
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5)))
        & r2_hidden(sK5,X1)
        & m1_subset_1(sK5,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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

fof(f36,plain,
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

fof(f39,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    & r2_hidden(sK5,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & v2_tex_2(sK4,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f38,f37,f36])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f23])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_921,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1631,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_921])).

cnf(c_2029,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),X1),sK4)
    | k6_domain_1(u1_struct_0(sK3),X1) != X0 ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_3309,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_2029])).

cnf(c_7563,plain,
    ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | ~ r1_tarski(k6_domain_1(sK4,sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_3309])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1622,plain,
    ( r1_tarski(X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_7163,plain,
    ( r1_tarski(k6_domain_1(sK4,sK5),sK4)
    | ~ r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1622])).

cnf(c_919,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1599,plain,
    ( X0 != X1
    | k6_domain_1(u1_struct_0(sK3),sK5) != X1
    | k6_domain_1(u1_struct_0(sK3),sK5) = X0 ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1996,plain,
    ( X0 != k1_tarski(sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_1599])).

cnf(c_2534,plain,
    ( k6_domain_1(X0,sK5) != k1_tarski(sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(X0,sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_1996])).

cnf(c_5100,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(sK4,sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5)
    | k6_domain_1(sK4,sK5) != k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1621,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4474,plain,
    ( r1_tarski(k6_domain_1(sK4,sK5),sK4)
    | r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),k6_domain_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1621])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2108,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ r2_hidden(X1,X0)
    | r2_hidden(X1,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3230,plain,
    ( ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(X0,k6_domain_1(sK4,sK5))
    | r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_2108])).

cnf(c_4473,plain,
    ( ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),k6_domain_1(sK4,sK5))
    | r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_3230])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_271,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_272,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_276,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_272,c_24,c_23])).

cnf(c_277,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_276])).

cnf(c_1474,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_277])).

cnf(c_1915,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),X0),sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0))) = k6_domain_1(u1_struct_0(sK3),X0) ),
    inference(instantiation,[status(thm)],[c_1474])).

cnf(c_2559,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1915])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(X0,sK4)
    | v1_xboole_0(sK4)
    | k6_domain_1(sK4,X0) = k1_tarski(X0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2384,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4)
    | k6_domain_1(sK4,sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1544,plain,
    ( ~ m1_subset_1(X0,sK4)
    | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2386,plain,
    ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_142,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7,c_1])).

cnf(c_143,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_1705,plain,
    ( m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_143])).

cnf(c_2118,plain,
    ( m1_subset_1(sK5,sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1705])).

cnf(c_1914,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2014,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1914])).

cnf(c_1939,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
    | k6_domain_1(u1_struct_0(sK3),sK5) = k1_tarski(sK5) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_918,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1598,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_918])).

cnf(c_1512,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(instantiation,[status(thm)],[c_919])).

cnf(c_1597,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1512])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1497,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1497])).

cnf(c_1480,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_17,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f60])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7563,c_7163,c_5100,c_4474,c_4473,c_2559,c_2384,c_2386,c_2118,c_2014,c_1939,c_1598,c_1597,c_1568,c_1480,c_17,c_18,c_19,c_20,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.78/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.78/0.97  
% 2.78/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/0.97  
% 2.78/0.97  ------  iProver source info
% 2.78/0.97  
% 2.78/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.78/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/0.97  git: non_committed_changes: false
% 2.78/0.97  git: last_make_outside_of_git: false
% 2.78/0.97  
% 2.78/0.97  ------ 
% 2.78/0.97  
% 2.78/0.97  ------ Input Options
% 2.78/0.97  
% 2.78/0.97  --out_options                           all
% 2.78/0.97  --tptp_safe_out                         true
% 2.78/0.97  --problem_path                          ""
% 2.78/0.97  --include_path                          ""
% 2.78/0.97  --clausifier                            res/vclausify_rel
% 2.78/0.97  --clausifier_options                    --mode clausify
% 2.78/0.97  --stdin                                 false
% 2.78/0.97  --stats_out                             all
% 2.78/0.97  
% 2.78/0.97  ------ General Options
% 2.78/0.97  
% 2.78/0.97  --fof                                   false
% 2.78/0.97  --time_out_real                         305.
% 2.78/0.97  --time_out_virtual                      -1.
% 2.78/0.97  --symbol_type_check                     false
% 2.78/0.97  --clausify_out                          false
% 2.78/0.97  --sig_cnt_out                           false
% 2.78/0.97  --trig_cnt_out                          false
% 2.78/0.97  --trig_cnt_out_tolerance                1.
% 2.78/0.97  --trig_cnt_out_sk_spl                   false
% 2.78/0.97  --abstr_cl_out                          false
% 2.78/0.97  
% 2.78/0.97  ------ Global Options
% 2.78/0.97  
% 2.78/0.97  --schedule                              default
% 2.78/0.97  --add_important_lit                     false
% 2.78/0.97  --prop_solver_per_cl                    1000
% 2.78/0.97  --min_unsat_core                        false
% 2.78/0.97  --soft_assumptions                      false
% 2.78/0.97  --soft_lemma_size                       3
% 2.78/0.97  --prop_impl_unit_size                   0
% 2.78/0.97  --prop_impl_unit                        []
% 2.78/0.97  --share_sel_clauses                     true
% 2.78/0.97  --reset_solvers                         false
% 2.78/0.97  --bc_imp_inh                            [conj_cone]
% 2.78/0.97  --conj_cone_tolerance                   3.
% 2.78/0.97  --extra_neg_conj                        none
% 2.78/0.97  --large_theory_mode                     true
% 2.78/0.97  --prolific_symb_bound                   200
% 2.78/0.97  --lt_threshold                          2000
% 2.78/0.97  --clause_weak_htbl                      true
% 2.78/0.97  --gc_record_bc_elim                     false
% 2.78/0.97  
% 2.78/0.97  ------ Preprocessing Options
% 2.78/0.97  
% 2.78/0.97  --preprocessing_flag                    true
% 2.78/0.97  --time_out_prep_mult                    0.1
% 2.78/0.97  --splitting_mode                        input
% 2.78/0.97  --splitting_grd                         true
% 2.78/0.97  --splitting_cvd                         false
% 2.78/0.97  --splitting_cvd_svl                     false
% 2.78/0.97  --splitting_nvd                         32
% 2.78/0.97  --sub_typing                            true
% 2.78/0.97  --prep_gs_sim                           true
% 2.78/0.97  --prep_unflatten                        true
% 2.78/0.97  --prep_res_sim                          true
% 2.78/0.97  --prep_upred                            true
% 2.78/0.97  --prep_sem_filter                       exhaustive
% 2.78/0.97  --prep_sem_filter_out                   false
% 2.78/0.97  --pred_elim                             true
% 2.78/0.97  --res_sim_input                         true
% 2.78/0.97  --eq_ax_congr_red                       true
% 2.78/0.97  --pure_diseq_elim                       true
% 2.78/0.97  --brand_transform                       false
% 2.78/0.97  --non_eq_to_eq                          false
% 2.78/0.97  --prep_def_merge                        true
% 2.78/0.97  --prep_def_merge_prop_impl              false
% 2.78/0.97  --prep_def_merge_mbd                    true
% 2.78/0.97  --prep_def_merge_tr_red                 false
% 2.78/0.97  --prep_def_merge_tr_cl                  false
% 2.78/0.97  --smt_preprocessing                     true
% 2.78/0.97  --smt_ac_axioms                         fast
% 2.78/0.97  --preprocessed_out                      false
% 2.78/0.97  --preprocessed_stats                    false
% 2.78/0.97  
% 2.78/0.97  ------ Abstraction refinement Options
% 2.78/0.97  
% 2.78/0.97  --abstr_ref                             []
% 2.78/0.97  --abstr_ref_prep                        false
% 2.78/0.97  --abstr_ref_until_sat                   false
% 2.78/0.97  --abstr_ref_sig_restrict                funpre
% 2.78/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.97  --abstr_ref_under                       []
% 2.78/0.97  
% 2.78/0.97  ------ SAT Options
% 2.78/0.97  
% 2.78/0.97  --sat_mode                              false
% 2.78/0.97  --sat_fm_restart_options                ""
% 2.78/0.97  --sat_gr_def                            false
% 2.78/0.97  --sat_epr_types                         true
% 2.78/0.97  --sat_non_cyclic_types                  false
% 2.78/0.97  --sat_finite_models                     false
% 2.78/0.97  --sat_fm_lemmas                         false
% 2.78/0.97  --sat_fm_prep                           false
% 2.78/0.97  --sat_fm_uc_incr                        true
% 2.78/0.97  --sat_out_model                         small
% 2.78/0.97  --sat_out_clauses                       false
% 2.78/0.97  
% 2.78/0.97  ------ QBF Options
% 2.78/0.97  
% 2.78/0.97  --qbf_mode                              false
% 2.78/0.97  --qbf_elim_univ                         false
% 2.78/0.97  --qbf_dom_inst                          none
% 2.78/0.97  --qbf_dom_pre_inst                      false
% 2.78/0.97  --qbf_sk_in                             false
% 2.78/0.97  --qbf_pred_elim                         true
% 2.78/0.97  --qbf_split                             512
% 2.78/0.97  
% 2.78/0.97  ------ BMC1 Options
% 2.78/0.97  
% 2.78/0.97  --bmc1_incremental                      false
% 2.78/0.97  --bmc1_axioms                           reachable_all
% 2.78/0.97  --bmc1_min_bound                        0
% 2.78/0.97  --bmc1_max_bound                        -1
% 2.78/0.97  --bmc1_max_bound_default                -1
% 2.78/0.97  --bmc1_symbol_reachability              true
% 2.78/0.97  --bmc1_property_lemmas                  false
% 2.78/0.97  --bmc1_k_induction                      false
% 2.78/0.97  --bmc1_non_equiv_states                 false
% 2.78/0.97  --bmc1_deadlock                         false
% 2.78/0.97  --bmc1_ucm                              false
% 2.78/0.97  --bmc1_add_unsat_core                   none
% 2.78/0.97  --bmc1_unsat_core_children              false
% 2.78/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.97  --bmc1_out_stat                         full
% 2.78/0.97  --bmc1_ground_init                      false
% 2.78/0.97  --bmc1_pre_inst_next_state              false
% 2.78/0.97  --bmc1_pre_inst_state                   false
% 2.78/0.97  --bmc1_pre_inst_reach_state             false
% 2.78/0.97  --bmc1_out_unsat_core                   false
% 2.78/0.97  --bmc1_aig_witness_out                  false
% 2.78/0.97  --bmc1_verbose                          false
% 2.78/0.97  --bmc1_dump_clauses_tptp                false
% 2.78/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.97  --bmc1_dump_file                        -
% 2.78/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.97  --bmc1_ucm_extend_mode                  1
% 2.78/0.97  --bmc1_ucm_init_mode                    2
% 2.78/0.97  --bmc1_ucm_cone_mode                    none
% 2.78/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.97  --bmc1_ucm_relax_model                  4
% 2.78/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.97  --bmc1_ucm_layered_model                none
% 2.78/0.97  --bmc1_ucm_max_lemma_size               10
% 2.78/0.97  
% 2.78/0.97  ------ AIG Options
% 2.78/0.97  
% 2.78/0.97  --aig_mode                              false
% 2.78/0.97  
% 2.78/0.97  ------ Instantiation Options
% 2.78/0.97  
% 2.78/0.97  --instantiation_flag                    true
% 2.78/0.97  --inst_sos_flag                         false
% 2.78/0.97  --inst_sos_phase                        true
% 2.78/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.97  --inst_lit_sel_side                     num_symb
% 2.78/0.97  --inst_solver_per_active                1400
% 2.78/0.97  --inst_solver_calls_frac                1.
% 2.78/0.97  --inst_passive_queue_type               priority_queues
% 2.78/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.97  --inst_passive_queues_freq              [25;2]
% 2.78/0.97  --inst_dismatching                      true
% 2.78/0.97  --inst_eager_unprocessed_to_passive     true
% 2.78/0.97  --inst_prop_sim_given                   true
% 2.78/0.97  --inst_prop_sim_new                     false
% 2.78/0.97  --inst_subs_new                         false
% 2.78/0.97  --inst_eq_res_simp                      false
% 2.78/0.97  --inst_subs_given                       false
% 2.78/0.97  --inst_orphan_elimination               true
% 2.78/0.97  --inst_learning_loop_flag               true
% 2.78/0.97  --inst_learning_start                   3000
% 2.78/0.97  --inst_learning_factor                  2
% 2.78/0.97  --inst_start_prop_sim_after_learn       3
% 2.78/0.97  --inst_sel_renew                        solver
% 2.78/0.97  --inst_lit_activity_flag                true
% 2.78/0.97  --inst_restr_to_given                   false
% 2.78/0.97  --inst_activity_threshold               500
% 2.78/0.97  --inst_out_proof                        true
% 2.78/0.97  
% 2.78/0.97  ------ Resolution Options
% 2.78/0.97  
% 2.78/0.97  --resolution_flag                       true
% 2.78/0.97  --res_lit_sel                           adaptive
% 2.78/0.97  --res_lit_sel_side                      none
% 2.78/0.97  --res_ordering                          kbo
% 2.78/0.97  --res_to_prop_solver                    active
% 2.78/0.97  --res_prop_simpl_new                    false
% 2.78/0.97  --res_prop_simpl_given                  true
% 2.78/0.97  --res_passive_queue_type                priority_queues
% 2.78/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.97  --res_passive_queues_freq               [15;5]
% 2.78/0.97  --res_forward_subs                      full
% 2.78/0.97  --res_backward_subs                     full
% 2.78/0.97  --res_forward_subs_resolution           true
% 2.78/0.97  --res_backward_subs_resolution          true
% 2.78/0.97  --res_orphan_elimination                true
% 2.78/0.97  --res_time_limit                        2.
% 2.78/0.97  --res_out_proof                         true
% 2.78/0.97  
% 2.78/0.97  ------ Superposition Options
% 2.78/0.97  
% 2.78/0.97  --superposition_flag                    true
% 2.78/0.97  --sup_passive_queue_type                priority_queues
% 2.78/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.97  --demod_completeness_check              fast
% 2.78/0.97  --demod_use_ground                      true
% 2.78/0.97  --sup_to_prop_solver                    passive
% 2.78/0.97  --sup_prop_simpl_new                    true
% 2.78/0.97  --sup_prop_simpl_given                  true
% 2.78/0.97  --sup_fun_splitting                     false
% 2.78/0.97  --sup_smt_interval                      50000
% 2.78/0.97  
% 2.78/0.97  ------ Superposition Simplification Setup
% 2.78/0.97  
% 2.78/0.97  --sup_indices_passive                   []
% 2.78/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_full_bw                           [BwDemod]
% 2.78/0.97  --sup_immed_triv                        [TrivRules]
% 2.78/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_immed_bw_main                     []
% 2.78/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.97  
% 2.78/0.97  ------ Combination Options
% 2.78/0.97  
% 2.78/0.97  --comb_res_mult                         3
% 2.78/0.97  --comb_sup_mult                         2
% 2.78/0.97  --comb_inst_mult                        10
% 2.78/0.97  
% 2.78/0.97  ------ Debug Options
% 2.78/0.97  
% 2.78/0.97  --dbg_backtrace                         false
% 2.78/0.97  --dbg_dump_prop_clauses                 false
% 2.78/0.97  --dbg_dump_prop_clauses_file            -
% 2.78/0.97  --dbg_out_stat                          false
% 2.78/0.97  ------ Parsing...
% 2.78/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/0.97  
% 2.78/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.78/0.97  
% 2.78/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/0.97  
% 2.78/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/0.97  ------ Proving...
% 2.78/0.97  ------ Problem Properties 
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  clauses                                 22
% 2.78/0.97  conjectures                             5
% 2.78/0.97  EPR                                     8
% 2.78/0.97  Horn                                    15
% 2.78/0.97  unary                                   5
% 2.78/0.97  binary                                  5
% 2.78/0.97  lits                                    53
% 2.78/0.97  lits eq                                 4
% 2.78/0.97  fd_pure                                 0
% 2.78/0.97  fd_pseudo                               0
% 2.78/0.97  fd_cond                                 0
% 2.78/0.97  fd_pseudo_cond                          0
% 2.78/0.97  AC symbols                              0
% 2.78/0.97  
% 2.78/0.97  ------ Schedule dynamic 5 is on 
% 2.78/0.97  
% 2.78/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  ------ 
% 2.78/0.97  Current options:
% 2.78/0.97  ------ 
% 2.78/0.97  
% 2.78/0.97  ------ Input Options
% 2.78/0.97  
% 2.78/0.97  --out_options                           all
% 2.78/0.97  --tptp_safe_out                         true
% 2.78/0.97  --problem_path                          ""
% 2.78/0.97  --include_path                          ""
% 2.78/0.97  --clausifier                            res/vclausify_rel
% 2.78/0.97  --clausifier_options                    --mode clausify
% 2.78/0.97  --stdin                                 false
% 2.78/0.97  --stats_out                             all
% 2.78/0.97  
% 2.78/0.97  ------ General Options
% 2.78/0.97  
% 2.78/0.97  --fof                                   false
% 2.78/0.97  --time_out_real                         305.
% 2.78/0.97  --time_out_virtual                      -1.
% 2.78/0.97  --symbol_type_check                     false
% 2.78/0.97  --clausify_out                          false
% 2.78/0.97  --sig_cnt_out                           false
% 2.78/0.97  --trig_cnt_out                          false
% 2.78/0.97  --trig_cnt_out_tolerance                1.
% 2.78/0.97  --trig_cnt_out_sk_spl                   false
% 2.78/0.97  --abstr_cl_out                          false
% 2.78/0.97  
% 2.78/0.97  ------ Global Options
% 2.78/0.97  
% 2.78/0.97  --schedule                              default
% 2.78/0.97  --add_important_lit                     false
% 2.78/0.97  --prop_solver_per_cl                    1000
% 2.78/0.97  --min_unsat_core                        false
% 2.78/0.97  --soft_assumptions                      false
% 2.78/0.97  --soft_lemma_size                       3
% 2.78/0.97  --prop_impl_unit_size                   0
% 2.78/0.97  --prop_impl_unit                        []
% 2.78/0.97  --share_sel_clauses                     true
% 2.78/0.97  --reset_solvers                         false
% 2.78/0.97  --bc_imp_inh                            [conj_cone]
% 2.78/0.97  --conj_cone_tolerance                   3.
% 2.78/0.97  --extra_neg_conj                        none
% 2.78/0.97  --large_theory_mode                     true
% 2.78/0.97  --prolific_symb_bound                   200
% 2.78/0.97  --lt_threshold                          2000
% 2.78/0.97  --clause_weak_htbl                      true
% 2.78/0.97  --gc_record_bc_elim                     false
% 2.78/0.97  
% 2.78/0.97  ------ Preprocessing Options
% 2.78/0.97  
% 2.78/0.97  --preprocessing_flag                    true
% 2.78/0.97  --time_out_prep_mult                    0.1
% 2.78/0.97  --splitting_mode                        input
% 2.78/0.97  --splitting_grd                         true
% 2.78/0.97  --splitting_cvd                         false
% 2.78/0.97  --splitting_cvd_svl                     false
% 2.78/0.97  --splitting_nvd                         32
% 2.78/0.97  --sub_typing                            true
% 2.78/0.97  --prep_gs_sim                           true
% 2.78/0.97  --prep_unflatten                        true
% 2.78/0.97  --prep_res_sim                          true
% 2.78/0.97  --prep_upred                            true
% 2.78/0.97  --prep_sem_filter                       exhaustive
% 2.78/0.97  --prep_sem_filter_out                   false
% 2.78/0.97  --pred_elim                             true
% 2.78/0.97  --res_sim_input                         true
% 2.78/0.97  --eq_ax_congr_red                       true
% 2.78/0.97  --pure_diseq_elim                       true
% 2.78/0.97  --brand_transform                       false
% 2.78/0.97  --non_eq_to_eq                          false
% 2.78/0.97  --prep_def_merge                        true
% 2.78/0.97  --prep_def_merge_prop_impl              false
% 2.78/0.97  --prep_def_merge_mbd                    true
% 2.78/0.97  --prep_def_merge_tr_red                 false
% 2.78/0.97  --prep_def_merge_tr_cl                  false
% 2.78/0.97  --smt_preprocessing                     true
% 2.78/0.97  --smt_ac_axioms                         fast
% 2.78/0.97  --preprocessed_out                      false
% 2.78/0.97  --preprocessed_stats                    false
% 2.78/0.97  
% 2.78/0.97  ------ Abstraction refinement Options
% 2.78/0.97  
% 2.78/0.97  --abstr_ref                             []
% 2.78/0.97  --abstr_ref_prep                        false
% 2.78/0.97  --abstr_ref_until_sat                   false
% 2.78/0.97  --abstr_ref_sig_restrict                funpre
% 2.78/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/0.97  --abstr_ref_under                       []
% 2.78/0.97  
% 2.78/0.97  ------ SAT Options
% 2.78/0.97  
% 2.78/0.97  --sat_mode                              false
% 2.78/0.97  --sat_fm_restart_options                ""
% 2.78/0.97  --sat_gr_def                            false
% 2.78/0.97  --sat_epr_types                         true
% 2.78/0.97  --sat_non_cyclic_types                  false
% 2.78/0.97  --sat_finite_models                     false
% 2.78/0.97  --sat_fm_lemmas                         false
% 2.78/0.97  --sat_fm_prep                           false
% 2.78/0.97  --sat_fm_uc_incr                        true
% 2.78/0.97  --sat_out_model                         small
% 2.78/0.97  --sat_out_clauses                       false
% 2.78/0.97  
% 2.78/0.97  ------ QBF Options
% 2.78/0.97  
% 2.78/0.97  --qbf_mode                              false
% 2.78/0.97  --qbf_elim_univ                         false
% 2.78/0.97  --qbf_dom_inst                          none
% 2.78/0.97  --qbf_dom_pre_inst                      false
% 2.78/0.97  --qbf_sk_in                             false
% 2.78/0.97  --qbf_pred_elim                         true
% 2.78/0.97  --qbf_split                             512
% 2.78/0.97  
% 2.78/0.97  ------ BMC1 Options
% 2.78/0.97  
% 2.78/0.97  --bmc1_incremental                      false
% 2.78/0.97  --bmc1_axioms                           reachable_all
% 2.78/0.97  --bmc1_min_bound                        0
% 2.78/0.97  --bmc1_max_bound                        -1
% 2.78/0.97  --bmc1_max_bound_default                -1
% 2.78/0.97  --bmc1_symbol_reachability              true
% 2.78/0.97  --bmc1_property_lemmas                  false
% 2.78/0.97  --bmc1_k_induction                      false
% 2.78/0.97  --bmc1_non_equiv_states                 false
% 2.78/0.97  --bmc1_deadlock                         false
% 2.78/0.97  --bmc1_ucm                              false
% 2.78/0.97  --bmc1_add_unsat_core                   none
% 2.78/0.97  --bmc1_unsat_core_children              false
% 2.78/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/0.97  --bmc1_out_stat                         full
% 2.78/0.97  --bmc1_ground_init                      false
% 2.78/0.97  --bmc1_pre_inst_next_state              false
% 2.78/0.97  --bmc1_pre_inst_state                   false
% 2.78/0.97  --bmc1_pre_inst_reach_state             false
% 2.78/0.97  --bmc1_out_unsat_core                   false
% 2.78/0.97  --bmc1_aig_witness_out                  false
% 2.78/0.97  --bmc1_verbose                          false
% 2.78/0.97  --bmc1_dump_clauses_tptp                false
% 2.78/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.78/0.97  --bmc1_dump_file                        -
% 2.78/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.78/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.78/0.97  --bmc1_ucm_extend_mode                  1
% 2.78/0.97  --bmc1_ucm_init_mode                    2
% 2.78/0.97  --bmc1_ucm_cone_mode                    none
% 2.78/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.78/0.97  --bmc1_ucm_relax_model                  4
% 2.78/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.78/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/0.97  --bmc1_ucm_layered_model                none
% 2.78/0.97  --bmc1_ucm_max_lemma_size               10
% 2.78/0.97  
% 2.78/0.97  ------ AIG Options
% 2.78/0.97  
% 2.78/0.97  --aig_mode                              false
% 2.78/0.97  
% 2.78/0.97  ------ Instantiation Options
% 2.78/0.97  
% 2.78/0.97  --instantiation_flag                    true
% 2.78/0.97  --inst_sos_flag                         false
% 2.78/0.97  --inst_sos_phase                        true
% 2.78/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/0.97  --inst_lit_sel_side                     none
% 2.78/0.97  --inst_solver_per_active                1400
% 2.78/0.97  --inst_solver_calls_frac                1.
% 2.78/0.97  --inst_passive_queue_type               priority_queues
% 2.78/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/0.97  --inst_passive_queues_freq              [25;2]
% 2.78/0.97  --inst_dismatching                      true
% 2.78/0.97  --inst_eager_unprocessed_to_passive     true
% 2.78/0.97  --inst_prop_sim_given                   true
% 2.78/0.97  --inst_prop_sim_new                     false
% 2.78/0.97  --inst_subs_new                         false
% 2.78/0.97  --inst_eq_res_simp                      false
% 2.78/0.97  --inst_subs_given                       false
% 2.78/0.97  --inst_orphan_elimination               true
% 2.78/0.97  --inst_learning_loop_flag               true
% 2.78/0.97  --inst_learning_start                   3000
% 2.78/0.97  --inst_learning_factor                  2
% 2.78/0.97  --inst_start_prop_sim_after_learn       3
% 2.78/0.97  --inst_sel_renew                        solver
% 2.78/0.97  --inst_lit_activity_flag                true
% 2.78/0.97  --inst_restr_to_given                   false
% 2.78/0.97  --inst_activity_threshold               500
% 2.78/0.97  --inst_out_proof                        true
% 2.78/0.97  
% 2.78/0.97  ------ Resolution Options
% 2.78/0.97  
% 2.78/0.97  --resolution_flag                       false
% 2.78/0.97  --res_lit_sel                           adaptive
% 2.78/0.97  --res_lit_sel_side                      none
% 2.78/0.97  --res_ordering                          kbo
% 2.78/0.97  --res_to_prop_solver                    active
% 2.78/0.97  --res_prop_simpl_new                    false
% 2.78/0.97  --res_prop_simpl_given                  true
% 2.78/0.97  --res_passive_queue_type                priority_queues
% 2.78/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/0.97  --res_passive_queues_freq               [15;5]
% 2.78/0.97  --res_forward_subs                      full
% 2.78/0.97  --res_backward_subs                     full
% 2.78/0.97  --res_forward_subs_resolution           true
% 2.78/0.97  --res_backward_subs_resolution          true
% 2.78/0.97  --res_orphan_elimination                true
% 2.78/0.97  --res_time_limit                        2.
% 2.78/0.97  --res_out_proof                         true
% 2.78/0.97  
% 2.78/0.97  ------ Superposition Options
% 2.78/0.97  
% 2.78/0.97  --superposition_flag                    true
% 2.78/0.97  --sup_passive_queue_type                priority_queues
% 2.78/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.78/0.97  --demod_completeness_check              fast
% 2.78/0.97  --demod_use_ground                      true
% 2.78/0.97  --sup_to_prop_solver                    passive
% 2.78/0.97  --sup_prop_simpl_new                    true
% 2.78/0.97  --sup_prop_simpl_given                  true
% 2.78/0.97  --sup_fun_splitting                     false
% 2.78/0.97  --sup_smt_interval                      50000
% 2.78/0.97  
% 2.78/0.97  ------ Superposition Simplification Setup
% 2.78/0.97  
% 2.78/0.97  --sup_indices_passive                   []
% 2.78/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_full_bw                           [BwDemod]
% 2.78/0.97  --sup_immed_triv                        [TrivRules]
% 2.78/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_immed_bw_main                     []
% 2.78/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/0.97  
% 2.78/0.97  ------ Combination Options
% 2.78/0.97  
% 2.78/0.97  --comb_res_mult                         3
% 2.78/0.97  --comb_sup_mult                         2
% 2.78/0.97  --comb_inst_mult                        10
% 2.78/0.97  
% 2.78/0.97  ------ Debug Options
% 2.78/0.97  
% 2.78/0.97  --dbg_backtrace                         false
% 2.78/0.97  --dbg_dump_prop_clauses                 false
% 2.78/0.97  --dbg_dump_prop_clauses_file            -
% 2.78/0.97  --dbg_out_stat                          false
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  ------ Proving...
% 2.78/0.97  
% 2.78/0.97  
% 2.78/0.97  % SZS status Theorem for theBenchmark.p
% 2.78/0.97  
% 2.78/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/0.97  
% 2.78/0.97  fof(f2,axiom,(
% 2.78/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f11,plain,(
% 2.78/0.97    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f2])).
% 2.78/0.97  
% 2.78/0.97  fof(f27,plain,(
% 2.78/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.97    inference(nnf_transformation,[],[f11])).
% 2.78/0.97  
% 2.78/0.97  fof(f28,plain,(
% 2.78/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.97    inference(rectify,[],[f27])).
% 2.78/0.97  
% 2.78/0.97  fof(f29,plain,(
% 2.78/0.97    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f30,plain,(
% 2.78/0.97    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.78/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f28,f29])).
% 2.78/0.97  
% 2.78/0.97  fof(f44,plain,(
% 2.78/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f30])).
% 2.78/0.97  
% 2.78/0.97  fof(f43,plain,(
% 2.78/0.97    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f30])).
% 2.78/0.97  
% 2.78/0.97  fof(f4,axiom,(
% 2.78/0.97    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f13,plain,(
% 2.78/0.97    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f4])).
% 2.78/0.97  
% 2.78/0.97  fof(f49,plain,(
% 2.78/0.97    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.78/0.97    inference(cnf_transformation,[],[f13])).
% 2.78/0.97  
% 2.78/0.97  fof(f8,axiom,(
% 2.78/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f19,plain,(
% 2.78/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f8])).
% 2.78/0.97  
% 2.78/0.97  fof(f20,plain,(
% 2.78/0.97    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.97    inference(flattening,[],[f19])).
% 2.78/0.97  
% 2.78/0.97  fof(f32,plain,(
% 2.78/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.97    inference(nnf_transformation,[],[f20])).
% 2.78/0.97  
% 2.78/0.97  fof(f33,plain,(
% 2.78/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.97    inference(rectify,[],[f32])).
% 2.78/0.97  
% 2.78/0.97  fof(f34,plain,(
% 2.78/0.97    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f35,plain,(
% 2.78/0.97    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.78/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 2.78/0.97  
% 2.78/0.97  fof(f53,plain,(
% 2.78/0.97    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f35])).
% 2.78/0.97  
% 2.78/0.97  fof(f9,conjecture,(
% 2.78/0.97    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f10,negated_conjecture,(
% 2.78/0.97    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 2.78/0.97    inference(negated_conjecture,[],[f9])).
% 2.78/0.97  
% 2.78/0.97  fof(f21,plain,(
% 2.78/0.97    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f10])).
% 2.78/0.97  
% 2.78/0.97  fof(f22,plain,(
% 2.78/0.97    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.78/0.97    inference(flattening,[],[f21])).
% 2.78/0.97  
% 2.78/0.97  fof(f38,plain,(
% 2.78/0.97    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f37,plain,(
% 2.78/0.97    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f36,plain,(
% 2.78/0.97    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f39,plain,(
% 2.78/0.97    ((k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 2.78/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f22,f38,f37,f36])).
% 2.78/0.97  
% 2.78/0.97  fof(f59,plain,(
% 2.78/0.97    l1_pre_topc(sK3)),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f57,plain,(
% 2.78/0.97    ~v2_struct_0(sK3)),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f58,plain,(
% 2.78/0.97    v2_pre_topc(sK3)),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f7,axiom,(
% 2.78/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f17,plain,(
% 2.78/0.97    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f7])).
% 2.78/0.97  
% 2.78/0.97  fof(f18,plain,(
% 2.78/0.97    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.78/0.97    inference(flattening,[],[f17])).
% 2.78/0.97  
% 2.78/0.97  fof(f52,plain,(
% 2.78/0.97    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f18])).
% 2.78/0.97  
% 2.78/0.97  fof(f6,axiom,(
% 2.78/0.97    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f15,plain,(
% 2.78/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f6])).
% 2.78/0.97  
% 2.78/0.97  fof(f16,plain,(
% 2.78/0.97    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.78/0.97    inference(flattening,[],[f15])).
% 2.78/0.97  
% 2.78/0.97  fof(f51,plain,(
% 2.78/0.97    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f16])).
% 2.78/0.97  
% 2.78/0.97  fof(f3,axiom,(
% 2.78/0.97    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f12,plain,(
% 2.78/0.97    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.78/0.97    inference(ennf_transformation,[],[f3])).
% 2.78/0.97  
% 2.78/0.97  fof(f31,plain,(
% 2.78/0.97    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.78/0.97    inference(nnf_transformation,[],[f12])).
% 2.78/0.97  
% 2.78/0.97  fof(f46,plain,(
% 2.78/0.97    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f31])).
% 2.78/0.97  
% 2.78/0.97  fof(f1,axiom,(
% 2.78/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f23,plain,(
% 2.78/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.78/0.97    inference(nnf_transformation,[],[f1])).
% 2.78/0.97  
% 2.78/0.97  fof(f24,plain,(
% 2.78/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.78/0.97    inference(rectify,[],[f23])).
% 2.78/0.97  
% 2.78/0.97  fof(f25,plain,(
% 2.78/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.78/0.97    introduced(choice_axiom,[])).
% 2.78/0.97  
% 2.78/0.97  fof(f26,plain,(
% 2.78/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.78/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f25])).
% 2.78/0.97  
% 2.78/0.97  fof(f40,plain,(
% 2.78/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f26])).
% 2.78/0.97  
% 2.78/0.97  fof(f5,axiom,(
% 2.78/0.97    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.78/0.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.78/0.97  
% 2.78/0.97  fof(f14,plain,(
% 2.78/0.97    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.78/0.97    inference(ennf_transformation,[],[f5])).
% 2.78/0.97  
% 2.78/0.97  fof(f50,plain,(
% 2.78/0.97    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.78/0.97    inference(cnf_transformation,[],[f14])).
% 2.78/0.97  
% 2.78/0.97  fof(f64,plain,(
% 2.78/0.97    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f63,plain,(
% 2.78/0.97    r2_hidden(sK5,sK4)),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f62,plain,(
% 2.78/0.97    m1_subset_1(sK5,u1_struct_0(sK3))),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f61,plain,(
% 2.78/0.97    v2_tex_2(sK4,sK3)),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  fof(f60,plain,(
% 2.78/0.97    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 2.78/0.97    inference(cnf_transformation,[],[f39])).
% 2.78/0.97  
% 2.78/0.97  cnf(c_921,plain,
% 2.78/0.97      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 2.78/0.97      theory(equality) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_1631,plain,
% 2.78/0.97      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_921]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_2029,plain,
% 2.78/0.97      ( ~ r1_tarski(X0,sK4)
% 2.78/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK3),X1),sK4)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),X1) != X0 ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_1631]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_3309,plain,
% 2.78/0.97      ( ~ r1_tarski(X0,sK4)
% 2.78/0.97      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_2029]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_7563,plain,
% 2.78/0.97      ( r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 2.78/0.97      | ~ r1_tarski(k6_domain_1(sK4,sK5),sK4)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(sK4,sK5) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_3309]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_2,plain,
% 2.78/0.97      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 2.78/0.97      inference(cnf_transformation,[],[f44]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_1622,plain,
% 2.78/0.97      ( r1_tarski(X0,sK4) | ~ r2_hidden(sK1(X0,sK4),sK4) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_2]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_7163,plain,
% 2.78/0.97      ( r1_tarski(k6_domain_1(sK4,sK5),sK4)
% 2.78/0.97      | ~ r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),sK4) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_1622]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_919,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_1599,plain,
% 2.78/0.97      ( X0 != X1
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != X1
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) = X0 ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_919]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_1996,plain,
% 2.78/0.97      ( X0 != k1_tarski(sK5)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) = X0
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_1599]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_2534,plain,
% 2.78/0.97      ( k6_domain_1(X0,sK5) != k1_tarski(sK5)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(X0,sK5)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_1996]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_5100,plain,
% 2.78/0.97      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(sK4,sK5)
% 2.78/0.97      | k6_domain_1(u1_struct_0(sK3),sK5) != k1_tarski(sK5)
% 2.78/0.97      | k6_domain_1(sK4,sK5) != k1_tarski(sK5) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_2534]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_3,plain,
% 2.78/0.97      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 2.78/0.97      inference(cnf_transformation,[],[f43]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_1621,plain,
% 2.78/0.97      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_3]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_4474,plain,
% 2.78/0.97      ( r1_tarski(k6_domain_1(sK4,sK5),sK4)
% 2.78/0.97      | r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),k6_domain_1(sK4,sK5)) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_1621]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_9,plain,
% 2.78/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/0.97      | ~ r2_hidden(X2,X0)
% 2.78/0.97      | r2_hidden(X2,X1) ),
% 2.78/0.97      inference(cnf_transformation,[],[f49]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_2108,plain,
% 2.78/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4))
% 2.78/0.97      | ~ r2_hidden(X1,X0)
% 2.78/0.97      | r2_hidden(X1,sK4) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_9]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_3230,plain,
% 2.78/0.97      ( ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 2.78/0.97      | ~ r2_hidden(X0,k6_domain_1(sK4,sK5))
% 2.78/0.97      | r2_hidden(X0,sK4) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_2108]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_4473,plain,
% 2.78/0.97      ( ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 2.78/0.97      | ~ r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),k6_domain_1(sK4,sK5))
% 2.78/0.97      | r2_hidden(sK1(k6_domain_1(sK4,sK5),sK4),sK4) ),
% 2.78/0.97      inference(instantiation,[status(thm)],[c_3230]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_16,plain,
% 2.78/0.97      ( ~ v2_tex_2(X0,X1)
% 2.78/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.97      | ~ r1_tarski(X2,X0)
% 2.78/0.97      | v2_struct_0(X1)
% 2.78/0.97      | ~ v2_pre_topc(X1)
% 2.78/0.97      | ~ l1_pre_topc(X1)
% 2.78/0.97      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 2.78/0.97      inference(cnf_transformation,[],[f53]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_22,negated_conjecture,
% 2.78/0.97      ( l1_pre_topc(sK3) ),
% 2.78/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_271,plain,
% 2.78/0.97      ( ~ v2_tex_2(X0,X1)
% 2.78/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.78/0.97      | ~ r1_tarski(X2,X0)
% 2.78/0.97      | v2_struct_0(X1)
% 2.78/0.97      | ~ v2_pre_topc(X1)
% 2.78/0.97      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 2.78/0.97      | sK3 != X1 ),
% 2.78/0.97      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_272,plain,
% 2.78/0.97      ( ~ v2_tex_2(X0,sK3)
% 2.78/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.97      | ~ r1_tarski(X1,X0)
% 2.78/0.97      | v2_struct_0(sK3)
% 2.78/0.97      | ~ v2_pre_topc(sK3)
% 2.78/0.97      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.78/0.97      inference(unflattening,[status(thm)],[c_271]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_24,negated_conjecture,
% 2.78/0.97      ( ~ v2_struct_0(sK3) ),
% 2.78/0.97      inference(cnf_transformation,[],[f57]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_23,negated_conjecture,
% 2.78/0.97      ( v2_pre_topc(sK3) ),
% 2.78/0.97      inference(cnf_transformation,[],[f58]) ).
% 2.78/0.97  
% 2.78/0.97  cnf(c_276,plain,
% 2.78/0.97      ( ~ v2_tex_2(X0,sK3)
% 2.78/0.97      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.97      | ~ r1_tarski(X1,X0)
% 2.78/0.97      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.78/0.97      inference(global_propositional_subsumption,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_272,c_24,c_23]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_277,plain,
% 2.78/0.98      ( ~ v2_tex_2(X0,sK3)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ r1_tarski(X1,X0)
% 2.78/0.98      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_276]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1474,plain,
% 2.78/0.98      ( ~ v2_tex_2(sK4,sK3)
% 2.78/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ r1_tarski(X0,sK4)
% 2.78/0.98      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_277]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1915,plain,
% 2.78/0.98      ( ~ v2_tex_2(sK4,sK3)
% 2.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),X0),sK4)
% 2.78/0.98      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X0))) = k6_domain_1(u1_struct_0(sK3),X0) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1474]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2559,plain,
% 2.78/0.98      ( ~ v2_tex_2(sK4,sK3)
% 2.78/0.98      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 2.78/0.98      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1915]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_12,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,X1)
% 2.78/0.98      | v1_xboole_0(X1)
% 2.78/0.98      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.78/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1543,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,sK4)
% 2.78/0.98      | v1_xboole_0(sK4)
% 2.78/0.98      | k6_domain_1(sK4,X0) = k1_tarski(X0) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2384,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK5,sK4)
% 2.78/0.98      | v1_xboole_0(sK4)
% 2.78/0.98      | k6_domain_1(sK4,sK5) = k1_tarski(sK5) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1543]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_11,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,X1)
% 2.78/0.98      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.78/0.98      | v1_xboole_0(X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1544,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,sK4)
% 2.78/0.98      | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
% 2.78/0.98      | v1_xboole_0(sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2386,plain,
% 2.78/0.98      ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 2.78/0.98      | ~ m1_subset_1(sK5,sK4)
% 2.78/0.98      | v1_xboole_0(sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_7,plain,
% 2.78/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f46]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f40]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_142,plain,
% 2.78/0.98      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 2.78/0.98      inference(global_propositional_subsumption,[status(thm)],[c_7,c_1]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_143,plain,
% 2.78/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.78/0.98      inference(renaming,[status(thm)],[c_142]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1705,plain,
% 2.78/0.98      ( m1_subset_1(X0,sK4) | ~ r2_hidden(X0,sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_143]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2118,plain,
% 2.78/0.98      ( m1_subset_1(sK5,sK4) | ~ r2_hidden(sK5,sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1705]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1914,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 2.78/0.98      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_2014,plain,
% 2.78/0.98      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.78/0.98      | v1_xboole_0(u1_struct_0(sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1914]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1939,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 2.78/0.98      | v1_xboole_0(u1_struct_0(sK3))
% 2.78/0.98      | k6_domain_1(u1_struct_0(sK3),sK5) = k1_tarski(sK5) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_918,plain,( X0 = X0 ),theory(equality) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1598,plain,
% 2.78/0.98      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_918]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1512,plain,
% 2.78/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
% 2.78/0.98      | k6_domain_1(u1_struct_0(sK3),sK5) != X0
% 2.78/0.98      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_919]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1597,plain,
% 2.78/0.98      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
% 2.78/0.98      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
% 2.78/0.98      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1512]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_10,plain,
% 2.78/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/0.98      | ~ r2_hidden(X2,X0)
% 2.78/0.98      | ~ v1_xboole_0(X1) ),
% 2.78/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1497,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 2.78/0.98      | ~ r2_hidden(sK5,sK4)
% 2.78/0.98      | ~ v1_xboole_0(X0) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1568,plain,
% 2.78/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 2.78/0.98      | ~ r2_hidden(sK5,sK4)
% 2.78/0.98      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1497]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_1480,plain,
% 2.78/0.98      ( ~ r2_hidden(sK5,sK4) | ~ v1_xboole_0(sK4) ),
% 2.78/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_17,negated_conjecture,
% 2.78/0.98      ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_18,negated_conjecture,
% 2.78/0.98      ( r2_hidden(sK5,sK4) ),
% 2.78/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_19,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 2.78/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_20,negated_conjecture,
% 2.78/0.98      ( v2_tex_2(sK4,sK3) ),
% 2.78/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(c_21,negated_conjecture,
% 2.78/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 2.78/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.78/0.98  
% 2.78/0.98  cnf(contradiction,plain,
% 2.78/0.98      ( $false ),
% 2.78/0.98      inference(minisat,
% 2.78/0.98                [status(thm)],
% 2.78/0.98                [c_7563,c_7163,c_5100,c_4474,c_4473,c_2559,c_2384,c_2386,
% 2.78/0.98                 c_2118,c_2014,c_1939,c_1598,c_1597,c_1568,c_1480,c_17,
% 2.78/0.98                 c_18,c_19,c_20,c_21]) ).
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/0.98  
% 2.78/0.98  ------                               Statistics
% 2.78/0.98  
% 2.78/0.98  ------ General
% 2.78/0.98  
% 2.78/0.98  abstr_ref_over_cycles:                  0
% 2.78/0.98  abstr_ref_under_cycles:                 0
% 2.78/0.98  gc_basic_clause_elim:                   0
% 2.78/0.98  forced_gc_time:                         0
% 2.78/0.98  parsing_time:                           0.02
% 2.78/0.98  unif_index_cands_time:                  0.
% 2.78/0.98  unif_index_add_time:                    0.
% 2.78/0.98  orderings_time:                         0.
% 2.78/0.98  out_proof_time:                         0.008
% 2.78/0.98  total_time:                             0.217
% 2.78/0.98  num_of_symbols:                         51
% 2.78/0.98  num_of_terms:                           5151
% 2.78/0.98  
% 2.78/0.98  ------ Preprocessing
% 2.78/0.98  
% 2.78/0.98  num_of_splits:                          0
% 2.78/0.98  num_of_split_atoms:                     0
% 2.78/0.98  num_of_reused_defs:                     0
% 2.78/0.98  num_eq_ax_congr_red:                    22
% 2.78/0.98  num_of_sem_filtered_clauses:            1
% 2.78/0.98  num_of_subtypes:                        0
% 2.78/0.98  monotx_restored_types:                  0
% 2.78/0.98  sat_num_of_epr_types:                   0
% 2.78/0.98  sat_num_of_non_cyclic_types:            0
% 2.78/0.98  sat_guarded_non_collapsed_types:        0
% 2.78/0.98  num_pure_diseq_elim:                    0
% 2.78/0.98  simp_replaced_by:                       0
% 2.78/0.98  res_preprocessed:                       116
% 2.78/0.98  prep_upred:                             0
% 2.78/0.98  prep_unflattend:                        22
% 2.78/0.98  smt_new_axioms:                         0
% 2.78/0.98  pred_elim_cands:                        5
% 2.78/0.98  pred_elim:                              3
% 2.78/0.98  pred_elim_cl:                           3
% 2.78/0.98  pred_elim_cycles:                       7
% 2.78/0.98  merged_defs:                            0
% 2.78/0.98  merged_defs_ncl:                        0
% 2.78/0.98  bin_hyper_res:                          0
% 2.78/0.98  prep_cycles:                            4
% 2.78/0.98  pred_elim_time:                         0.01
% 2.78/0.98  splitting_time:                         0.
% 2.78/0.98  sem_filter_time:                        0.
% 2.78/0.98  monotx_time:                            0.001
% 2.78/0.98  subtype_inf_time:                       0.
% 2.78/0.98  
% 2.78/0.98  ------ Problem properties
% 2.78/0.98  
% 2.78/0.98  clauses:                                22
% 2.78/0.98  conjectures:                            5
% 2.78/0.98  epr:                                    8
% 2.78/0.98  horn:                                   15
% 2.78/0.98  ground:                                 5
% 2.78/0.98  unary:                                  5
% 2.78/0.98  binary:                                 5
% 2.78/0.98  lits:                                   53
% 2.78/0.98  lits_eq:                                4
% 2.78/0.98  fd_pure:                                0
% 2.78/0.98  fd_pseudo:                              0
% 2.78/0.98  fd_cond:                                0
% 2.78/0.98  fd_pseudo_cond:                         0
% 2.78/0.98  ac_symbols:                             0
% 2.78/0.98  
% 2.78/0.98  ------ Propositional Solver
% 2.78/0.98  
% 2.78/0.98  prop_solver_calls:                      29
% 2.78/0.98  prop_fast_solver_calls:                 1053
% 2.78/0.98  smt_solver_calls:                       0
% 2.78/0.98  smt_fast_solver_calls:                  0
% 2.78/0.98  prop_num_of_clauses:                    2744
% 2.78/0.98  prop_preprocess_simplified:             6317
% 2.78/0.98  prop_fo_subsumed:                       57
% 2.78/0.98  prop_solver_time:                       0.
% 2.78/0.98  smt_solver_time:                        0.
% 2.78/0.98  smt_fast_solver_time:                   0.
% 2.78/0.98  prop_fast_solver_time:                  0.
% 2.78/0.98  prop_unsat_core_time:                   0.
% 2.78/0.98  
% 2.78/0.98  ------ QBF
% 2.78/0.98  
% 2.78/0.98  qbf_q_res:                              0
% 2.78/0.98  qbf_num_tautologies:                    0
% 2.78/0.98  qbf_prep_cycles:                        0
% 2.78/0.98  
% 2.78/0.98  ------ BMC1
% 2.78/0.98  
% 2.78/0.98  bmc1_current_bound:                     -1
% 2.78/0.98  bmc1_last_solved_bound:                 -1
% 2.78/0.98  bmc1_unsat_core_size:                   -1
% 2.78/0.98  bmc1_unsat_core_parents_size:           -1
% 2.78/0.98  bmc1_merge_next_fun:                    0
% 2.78/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.78/0.98  
% 2.78/0.98  ------ Instantiation
% 2.78/0.98  
% 2.78/0.98  inst_num_of_clauses:                    760
% 2.78/0.98  inst_num_in_passive:                    223
% 2.78/0.98  inst_num_in_active:                     383
% 2.78/0.98  inst_num_in_unprocessed:                153
% 2.78/0.98  inst_num_of_loops:                      488
% 2.78/0.98  inst_num_of_learning_restarts:          0
% 2.78/0.98  inst_num_moves_active_passive:          100
% 2.78/0.98  inst_lit_activity:                      0
% 2.78/0.98  inst_lit_activity_moves:                0
% 2.78/0.98  inst_num_tautologies:                   0
% 2.78/0.98  inst_num_prop_implied:                  0
% 2.78/0.98  inst_num_existing_simplified:           0
% 2.78/0.98  inst_num_eq_res_simplified:             0
% 2.78/0.98  inst_num_child_elim:                    0
% 2.78/0.98  inst_num_of_dismatching_blockings:      309
% 2.78/0.98  inst_num_of_non_proper_insts:           780
% 2.78/0.98  inst_num_of_duplicates:                 0
% 2.78/0.98  inst_inst_num_from_inst_to_res:         0
% 2.78/0.98  inst_dismatching_checking_time:         0.
% 2.78/0.98  
% 2.78/0.98  ------ Resolution
% 2.78/0.98  
% 2.78/0.98  res_num_of_clauses:                     0
% 2.78/0.98  res_num_in_passive:                     0
% 2.78/0.98  res_num_in_active:                      0
% 2.78/0.98  res_num_of_loops:                       120
% 2.78/0.98  res_forward_subset_subsumed:            102
% 2.78/0.98  res_backward_subset_subsumed:           0
% 2.78/0.98  res_forward_subsumed:                   0
% 2.78/0.98  res_backward_subsumed:                  0
% 2.78/0.98  res_forward_subsumption_resolution:     0
% 2.78/0.98  res_backward_subsumption_resolution:    0
% 2.78/0.98  res_clause_to_clause_subsumption:       512
% 2.78/0.98  res_orphan_elimination:                 0
% 2.78/0.98  res_tautology_del:                      70
% 2.78/0.98  res_num_eq_res_simplified:              0
% 2.78/0.98  res_num_sel_changes:                    0
% 2.78/0.98  res_moves_from_active_to_pass:          0
% 2.78/0.98  
% 2.78/0.98  ------ Superposition
% 2.78/0.98  
% 2.78/0.98  sup_time_total:                         0.
% 2.78/0.98  sup_time_generating:                    0.
% 2.78/0.98  sup_time_sim_full:                      0.
% 2.78/0.98  sup_time_sim_immed:                     0.
% 2.78/0.98  
% 2.78/0.98  sup_num_of_clauses:                     178
% 2.78/0.98  sup_num_in_active:                      94
% 2.78/0.98  sup_num_in_passive:                     84
% 2.78/0.98  sup_num_of_loops:                       96
% 2.78/0.98  sup_fw_superposition:                   117
% 2.78/0.98  sup_bw_superposition:                   116
% 2.78/0.98  sup_immediate_simplified:               46
% 2.78/0.98  sup_given_eliminated:                   0
% 2.78/0.98  comparisons_done:                       0
% 2.78/0.98  comparisons_avoided:                    0
% 2.78/0.98  
% 2.78/0.98  ------ Simplifications
% 2.78/0.98  
% 2.78/0.98  
% 2.78/0.98  sim_fw_subset_subsumed:                 38
% 2.78/0.98  sim_bw_subset_subsumed:                 1
% 2.78/0.98  sim_fw_subsumed:                        5
% 2.78/0.98  sim_bw_subsumed:                        0
% 2.78/0.98  sim_fw_subsumption_res:                 1
% 2.78/0.98  sim_bw_subsumption_res:                 0
% 2.78/0.98  sim_tautology_del:                      9
% 2.78/0.98  sim_eq_tautology_del:                   0
% 2.78/0.98  sim_eq_res_simp:                        0
% 2.78/0.98  sim_fw_demodulated:                     0
% 2.78/0.98  sim_bw_demodulated:                     1
% 2.78/0.98  sim_light_normalised:                   6
% 2.78/0.98  sim_joinable_taut:                      0
% 2.78/0.98  sim_joinable_simp:                      0
% 2.78/0.98  sim_ac_normalised:                      0
% 2.78/0.98  sim_smt_subsumption:                    0
% 2.78/0.98  
%------------------------------------------------------------------------------
