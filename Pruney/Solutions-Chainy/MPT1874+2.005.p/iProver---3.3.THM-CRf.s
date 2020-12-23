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
% DateTime   : Thu Dec  3 12:26:28 EST 2020

% Result     : Theorem 7.20s
% Output     : CNFRefutation 7.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 247 expanded)
%              Number of clauses        :   61 (  74 expanded)
%              Number of leaves         :   19 (  71 expanded)
%              Depth                    :   14
%              Number of atoms          :  414 (1276 expanded)
%              Number of equality atoms :   80 ( 199 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f31])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

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
    inference(nnf_transformation,[],[f21])).

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
    inference(cnf_transformation,[],[f35])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f38,f37,f36])).

fof(f57,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f56,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f39])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_tarski(X1,X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f50,f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f40,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f62,plain,(
    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f58,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10023,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(sK1(X0,sK4),X0)
    | r2_hidden(sK1(X0,sK4),X1) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_17490,plain,
    ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
    | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5))
    | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_10023])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1450,plain,
    ( r1_tarski(X0,sK4)
    | r2_hidden(sK1(X0,sK4),X0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6646,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),sK4)
    | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5)) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK1(X0,X1),X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1451,plain,
    ( r1_tarski(X0,sK4)
    | ~ r2_hidden(sK1(X0,sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_6647,plain,
    ( r1_tarski(k2_tarski(sK5,sK5),sK4)
    | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_864,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1460,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(X1,sK4)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_864])).

cnf(c_2895,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
    inference(instantiation,[status(thm)],[c_1460])).

cnf(c_5057,plain,
    ( ~ r1_tarski(k2_tarski(sK5,sK5),sK4)
    | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k6_domain_1(u1_struct_0(sK3),sK5) != k2_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_2895])).

cnf(c_866,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1730,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | X0 != k6_domain_1(sK4,sK5)
    | X1 != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_866])).

cnf(c_2384,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK4))
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | X0 != k6_domain_1(sK4,sK5)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1730])).

cnf(c_4249,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | k2_tarski(sK5,sK5) != k6_domain_1(sK4,sK5)
    | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2384])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_19,negated_conjecture,
    ( l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_232,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_19])).

cnf(c_233,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK3)
    | ~ v2_pre_topc(sK3)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_232])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_237,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_233,c_21,c_20])).

cnf(c_238,plain,
    ( ~ v2_tex_2(X0,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
    inference(renaming,[status(thm)],[c_237])).

cnf(c_1348,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(X0,sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_238])).

cnf(c_2551,plain,
    ( ~ v2_tex_2(sK4,sK3)
    | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
    | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1348])).

cnf(c_861,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2385,plain,
    ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1682,plain,
    ( ~ m1_subset_1(X0,u1_struct_0(sK3))
    | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2119,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1682])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1205,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1207,plain,
    ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
    | m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2089,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1207])).

cnf(c_1410,plain,
    ( ~ m1_subset_1(X0,sK4)
    | v1_xboole_0(sK4)
    | k2_tarski(X0,X0) = k6_domain_1(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1617,plain,
    ( ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4)
    | k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1410])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,sK4)
    | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1572,plain,
    ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK5,sK4)
    | v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1512,plain,
    ( ~ r2_hidden(sK5,u1_struct_0(sK3))
    | ~ v1_xboole_0(u1_struct_0(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1513,plain,
    ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1512])).

cnf(c_1444,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_861])).

cnf(c_862,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1374,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) != X0
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(instantiation,[status(thm)],[c_862])).

cnf(c_1443,plain,
    ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
    | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
    inference(instantiation,[status(thm)],[c_1374])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
    | r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1440,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK5,u1_struct_0(sK3))
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_1441,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
    | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
    | r2_hidden(sK5,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1440])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1357,plain,
    ( m1_subset_1(sK5,sK4)
    | ~ r2_hidden(sK5,sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1354,plain,
    ( ~ r2_hidden(sK5,sK4)
    | ~ v1_xboole_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_14,negated_conjecture,
    ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_15,negated_conjecture,
    ( r2_hidden(sK5,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_28,plain,
    ( r2_hidden(sK5,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_17,negated_conjecture,
    ( v2_tex_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17490,c_6646,c_6647,c_5057,c_4249,c_2551,c_2385,c_2119,c_2089,c_1617,c_1572,c_1513,c_1512,c_1444,c_1443,c_1441,c_1440,c_1357,c_1354,c_14,c_28,c_15,c_16,c_17,c_25,c_18])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:58:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.20/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.20/1.53  
% 7.20/1.53  ------  iProver source info
% 7.20/1.53  
% 7.20/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.20/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.20/1.53  git: non_committed_changes: false
% 7.20/1.53  git: last_make_outside_of_git: false
% 7.20/1.53  
% 7.20/1.53  ------ 
% 7.20/1.53  
% 7.20/1.53  ------ Input Options
% 7.20/1.53  
% 7.20/1.53  --out_options                           all
% 7.20/1.53  --tptp_safe_out                         true
% 7.20/1.53  --problem_path                          ""
% 7.20/1.53  --include_path                          ""
% 7.20/1.53  --clausifier                            res/vclausify_rel
% 7.20/1.53  --clausifier_options                    --mode clausify
% 7.20/1.53  --stdin                                 false
% 7.20/1.53  --stats_out                             all
% 7.20/1.53  
% 7.20/1.53  ------ General Options
% 7.20/1.53  
% 7.20/1.53  --fof                                   false
% 7.20/1.53  --time_out_real                         305.
% 7.20/1.53  --time_out_virtual                      -1.
% 7.20/1.53  --symbol_type_check                     false
% 7.20/1.53  --clausify_out                          false
% 7.20/1.53  --sig_cnt_out                           false
% 7.20/1.53  --trig_cnt_out                          false
% 7.20/1.53  --trig_cnt_out_tolerance                1.
% 7.20/1.53  --trig_cnt_out_sk_spl                   false
% 7.20/1.53  --abstr_cl_out                          false
% 7.20/1.53  
% 7.20/1.53  ------ Global Options
% 7.20/1.53  
% 7.20/1.53  --schedule                              default
% 7.20/1.53  --add_important_lit                     false
% 7.20/1.53  --prop_solver_per_cl                    1000
% 7.20/1.53  --min_unsat_core                        false
% 7.20/1.53  --soft_assumptions                      false
% 7.20/1.53  --soft_lemma_size                       3
% 7.20/1.53  --prop_impl_unit_size                   0
% 7.20/1.53  --prop_impl_unit                        []
% 7.20/1.53  --share_sel_clauses                     true
% 7.20/1.53  --reset_solvers                         false
% 7.20/1.53  --bc_imp_inh                            [conj_cone]
% 7.20/1.53  --conj_cone_tolerance                   3.
% 7.20/1.53  --extra_neg_conj                        none
% 7.20/1.53  --large_theory_mode                     true
% 7.20/1.53  --prolific_symb_bound                   200
% 7.20/1.53  --lt_threshold                          2000
% 7.20/1.53  --clause_weak_htbl                      true
% 7.20/1.53  --gc_record_bc_elim                     false
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing Options
% 7.20/1.53  
% 7.20/1.53  --preprocessing_flag                    true
% 7.20/1.53  --time_out_prep_mult                    0.1
% 7.20/1.53  --splitting_mode                        input
% 7.20/1.53  --splitting_grd                         true
% 7.20/1.53  --splitting_cvd                         false
% 7.20/1.53  --splitting_cvd_svl                     false
% 7.20/1.53  --splitting_nvd                         32
% 7.20/1.53  --sub_typing                            true
% 7.20/1.53  --prep_gs_sim                           true
% 7.20/1.53  --prep_unflatten                        true
% 7.20/1.53  --prep_res_sim                          true
% 7.20/1.53  --prep_upred                            true
% 7.20/1.53  --prep_sem_filter                       exhaustive
% 7.20/1.53  --prep_sem_filter_out                   false
% 7.20/1.53  --pred_elim                             true
% 7.20/1.53  --res_sim_input                         true
% 7.20/1.53  --eq_ax_congr_red                       true
% 7.20/1.53  --pure_diseq_elim                       true
% 7.20/1.53  --brand_transform                       false
% 7.20/1.53  --non_eq_to_eq                          false
% 7.20/1.53  --prep_def_merge                        true
% 7.20/1.53  --prep_def_merge_prop_impl              false
% 7.20/1.53  --prep_def_merge_mbd                    true
% 7.20/1.53  --prep_def_merge_tr_red                 false
% 7.20/1.53  --prep_def_merge_tr_cl                  false
% 7.20/1.53  --smt_preprocessing                     true
% 7.20/1.53  --smt_ac_axioms                         fast
% 7.20/1.53  --preprocessed_out                      false
% 7.20/1.53  --preprocessed_stats                    false
% 7.20/1.53  
% 7.20/1.53  ------ Abstraction refinement Options
% 7.20/1.53  
% 7.20/1.53  --abstr_ref                             []
% 7.20/1.53  --abstr_ref_prep                        false
% 7.20/1.53  --abstr_ref_until_sat                   false
% 7.20/1.53  --abstr_ref_sig_restrict                funpre
% 7.20/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.53  --abstr_ref_under                       []
% 7.20/1.53  
% 7.20/1.53  ------ SAT Options
% 7.20/1.53  
% 7.20/1.53  --sat_mode                              false
% 7.20/1.53  --sat_fm_restart_options                ""
% 7.20/1.53  --sat_gr_def                            false
% 7.20/1.53  --sat_epr_types                         true
% 7.20/1.53  --sat_non_cyclic_types                  false
% 7.20/1.53  --sat_finite_models                     false
% 7.20/1.53  --sat_fm_lemmas                         false
% 7.20/1.53  --sat_fm_prep                           false
% 7.20/1.53  --sat_fm_uc_incr                        true
% 7.20/1.53  --sat_out_model                         small
% 7.20/1.53  --sat_out_clauses                       false
% 7.20/1.53  
% 7.20/1.53  ------ QBF Options
% 7.20/1.53  
% 7.20/1.53  --qbf_mode                              false
% 7.20/1.53  --qbf_elim_univ                         false
% 7.20/1.53  --qbf_dom_inst                          none
% 7.20/1.53  --qbf_dom_pre_inst                      false
% 7.20/1.53  --qbf_sk_in                             false
% 7.20/1.53  --qbf_pred_elim                         true
% 7.20/1.53  --qbf_split                             512
% 7.20/1.53  
% 7.20/1.53  ------ BMC1 Options
% 7.20/1.53  
% 7.20/1.53  --bmc1_incremental                      false
% 7.20/1.53  --bmc1_axioms                           reachable_all
% 7.20/1.53  --bmc1_min_bound                        0
% 7.20/1.53  --bmc1_max_bound                        -1
% 7.20/1.53  --bmc1_max_bound_default                -1
% 7.20/1.53  --bmc1_symbol_reachability              true
% 7.20/1.53  --bmc1_property_lemmas                  false
% 7.20/1.53  --bmc1_k_induction                      false
% 7.20/1.53  --bmc1_non_equiv_states                 false
% 7.20/1.53  --bmc1_deadlock                         false
% 7.20/1.53  --bmc1_ucm                              false
% 7.20/1.53  --bmc1_add_unsat_core                   none
% 7.20/1.53  --bmc1_unsat_core_children              false
% 7.20/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.53  --bmc1_out_stat                         full
% 7.20/1.53  --bmc1_ground_init                      false
% 7.20/1.53  --bmc1_pre_inst_next_state              false
% 7.20/1.53  --bmc1_pre_inst_state                   false
% 7.20/1.53  --bmc1_pre_inst_reach_state             false
% 7.20/1.53  --bmc1_out_unsat_core                   false
% 7.20/1.53  --bmc1_aig_witness_out                  false
% 7.20/1.53  --bmc1_verbose                          false
% 7.20/1.53  --bmc1_dump_clauses_tptp                false
% 7.20/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.53  --bmc1_dump_file                        -
% 7.20/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.53  --bmc1_ucm_extend_mode                  1
% 7.20/1.53  --bmc1_ucm_init_mode                    2
% 7.20/1.53  --bmc1_ucm_cone_mode                    none
% 7.20/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.53  --bmc1_ucm_relax_model                  4
% 7.20/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.53  --bmc1_ucm_layered_model                none
% 7.20/1.53  --bmc1_ucm_max_lemma_size               10
% 7.20/1.53  
% 7.20/1.53  ------ AIG Options
% 7.20/1.53  
% 7.20/1.53  --aig_mode                              false
% 7.20/1.53  
% 7.20/1.53  ------ Instantiation Options
% 7.20/1.53  
% 7.20/1.53  --instantiation_flag                    true
% 7.20/1.53  --inst_sos_flag                         false
% 7.20/1.53  --inst_sos_phase                        true
% 7.20/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.53  --inst_lit_sel_side                     num_symb
% 7.20/1.53  --inst_solver_per_active                1400
% 7.20/1.53  --inst_solver_calls_frac                1.
% 7.20/1.53  --inst_passive_queue_type               priority_queues
% 7.20/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.53  --inst_passive_queues_freq              [25;2]
% 7.20/1.53  --inst_dismatching                      true
% 7.20/1.53  --inst_eager_unprocessed_to_passive     true
% 7.20/1.53  --inst_prop_sim_given                   true
% 7.20/1.53  --inst_prop_sim_new                     false
% 7.20/1.53  --inst_subs_new                         false
% 7.20/1.53  --inst_eq_res_simp                      false
% 7.20/1.53  --inst_subs_given                       false
% 7.20/1.53  --inst_orphan_elimination               true
% 7.20/1.53  --inst_learning_loop_flag               true
% 7.20/1.53  --inst_learning_start                   3000
% 7.20/1.53  --inst_learning_factor                  2
% 7.20/1.53  --inst_start_prop_sim_after_learn       3
% 7.20/1.53  --inst_sel_renew                        solver
% 7.20/1.53  --inst_lit_activity_flag                true
% 7.20/1.53  --inst_restr_to_given                   false
% 7.20/1.53  --inst_activity_threshold               500
% 7.20/1.53  --inst_out_proof                        true
% 7.20/1.53  
% 7.20/1.53  ------ Resolution Options
% 7.20/1.53  
% 7.20/1.53  --resolution_flag                       true
% 7.20/1.53  --res_lit_sel                           adaptive
% 7.20/1.53  --res_lit_sel_side                      none
% 7.20/1.53  --res_ordering                          kbo
% 7.20/1.53  --res_to_prop_solver                    active
% 7.20/1.53  --res_prop_simpl_new                    false
% 7.20/1.53  --res_prop_simpl_given                  true
% 7.20/1.53  --res_passive_queue_type                priority_queues
% 7.20/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.53  --res_passive_queues_freq               [15;5]
% 7.20/1.53  --res_forward_subs                      full
% 7.20/1.53  --res_backward_subs                     full
% 7.20/1.53  --res_forward_subs_resolution           true
% 7.20/1.53  --res_backward_subs_resolution          true
% 7.20/1.53  --res_orphan_elimination                true
% 7.20/1.53  --res_time_limit                        2.
% 7.20/1.53  --res_out_proof                         true
% 7.20/1.53  
% 7.20/1.53  ------ Superposition Options
% 7.20/1.53  
% 7.20/1.53  --superposition_flag                    true
% 7.20/1.53  --sup_passive_queue_type                priority_queues
% 7.20/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.53  --demod_completeness_check              fast
% 7.20/1.53  --demod_use_ground                      true
% 7.20/1.53  --sup_to_prop_solver                    passive
% 7.20/1.53  --sup_prop_simpl_new                    true
% 7.20/1.53  --sup_prop_simpl_given                  true
% 7.20/1.53  --sup_fun_splitting                     false
% 7.20/1.53  --sup_smt_interval                      50000
% 7.20/1.53  
% 7.20/1.53  ------ Superposition Simplification Setup
% 7.20/1.53  
% 7.20/1.53  --sup_indices_passive                   []
% 7.20/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_full_bw                           [BwDemod]
% 7.20/1.53  --sup_immed_triv                        [TrivRules]
% 7.20/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_immed_bw_main                     []
% 7.20/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.53  
% 7.20/1.53  ------ Combination Options
% 7.20/1.53  
% 7.20/1.53  --comb_res_mult                         3
% 7.20/1.53  --comb_sup_mult                         2
% 7.20/1.53  --comb_inst_mult                        10
% 7.20/1.53  
% 7.20/1.53  ------ Debug Options
% 7.20/1.53  
% 7.20/1.53  --dbg_backtrace                         false
% 7.20/1.53  --dbg_dump_prop_clauses                 false
% 7.20/1.53  --dbg_dump_prop_clauses_file            -
% 7.20/1.53  --dbg_out_stat                          false
% 7.20/1.53  ------ Parsing...
% 7.20/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.20/1.53  ------ Proving...
% 7.20/1.53  ------ Problem Properties 
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  clauses                                 19
% 7.20/1.53  conjectures                             5
% 7.20/1.53  EPR                                     5
% 7.20/1.53  Horn                                    13
% 7.20/1.53  unary                                   5
% 7.20/1.53  binary                                  5
% 7.20/1.53  lits                                    44
% 7.20/1.53  lits eq                                 4
% 7.20/1.53  fd_pure                                 0
% 7.20/1.53  fd_pseudo                               0
% 7.20/1.53  fd_cond                                 0
% 7.20/1.53  fd_pseudo_cond                          0
% 7.20/1.53  AC symbols                              0
% 7.20/1.53  
% 7.20/1.53  ------ Schedule dynamic 5 is on 
% 7.20/1.53  
% 7.20/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ 
% 7.20/1.53  Current options:
% 7.20/1.53  ------ 
% 7.20/1.53  
% 7.20/1.53  ------ Input Options
% 7.20/1.53  
% 7.20/1.53  --out_options                           all
% 7.20/1.53  --tptp_safe_out                         true
% 7.20/1.53  --problem_path                          ""
% 7.20/1.53  --include_path                          ""
% 7.20/1.53  --clausifier                            res/vclausify_rel
% 7.20/1.53  --clausifier_options                    --mode clausify
% 7.20/1.53  --stdin                                 false
% 7.20/1.53  --stats_out                             all
% 7.20/1.53  
% 7.20/1.53  ------ General Options
% 7.20/1.53  
% 7.20/1.53  --fof                                   false
% 7.20/1.53  --time_out_real                         305.
% 7.20/1.53  --time_out_virtual                      -1.
% 7.20/1.53  --symbol_type_check                     false
% 7.20/1.53  --clausify_out                          false
% 7.20/1.53  --sig_cnt_out                           false
% 7.20/1.53  --trig_cnt_out                          false
% 7.20/1.53  --trig_cnt_out_tolerance                1.
% 7.20/1.53  --trig_cnt_out_sk_spl                   false
% 7.20/1.53  --abstr_cl_out                          false
% 7.20/1.53  
% 7.20/1.53  ------ Global Options
% 7.20/1.53  
% 7.20/1.53  --schedule                              default
% 7.20/1.53  --add_important_lit                     false
% 7.20/1.53  --prop_solver_per_cl                    1000
% 7.20/1.53  --min_unsat_core                        false
% 7.20/1.53  --soft_assumptions                      false
% 7.20/1.53  --soft_lemma_size                       3
% 7.20/1.53  --prop_impl_unit_size                   0
% 7.20/1.53  --prop_impl_unit                        []
% 7.20/1.53  --share_sel_clauses                     true
% 7.20/1.53  --reset_solvers                         false
% 7.20/1.53  --bc_imp_inh                            [conj_cone]
% 7.20/1.53  --conj_cone_tolerance                   3.
% 7.20/1.53  --extra_neg_conj                        none
% 7.20/1.53  --large_theory_mode                     true
% 7.20/1.53  --prolific_symb_bound                   200
% 7.20/1.53  --lt_threshold                          2000
% 7.20/1.53  --clause_weak_htbl                      true
% 7.20/1.53  --gc_record_bc_elim                     false
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing Options
% 7.20/1.53  
% 7.20/1.53  --preprocessing_flag                    true
% 7.20/1.53  --time_out_prep_mult                    0.1
% 7.20/1.53  --splitting_mode                        input
% 7.20/1.53  --splitting_grd                         true
% 7.20/1.53  --splitting_cvd                         false
% 7.20/1.53  --splitting_cvd_svl                     false
% 7.20/1.53  --splitting_nvd                         32
% 7.20/1.53  --sub_typing                            true
% 7.20/1.53  --prep_gs_sim                           true
% 7.20/1.53  --prep_unflatten                        true
% 7.20/1.53  --prep_res_sim                          true
% 7.20/1.53  --prep_upred                            true
% 7.20/1.53  --prep_sem_filter                       exhaustive
% 7.20/1.53  --prep_sem_filter_out                   false
% 7.20/1.53  --pred_elim                             true
% 7.20/1.53  --res_sim_input                         true
% 7.20/1.53  --eq_ax_congr_red                       true
% 7.20/1.53  --pure_diseq_elim                       true
% 7.20/1.53  --brand_transform                       false
% 7.20/1.53  --non_eq_to_eq                          false
% 7.20/1.53  --prep_def_merge                        true
% 7.20/1.53  --prep_def_merge_prop_impl              false
% 7.20/1.53  --prep_def_merge_mbd                    true
% 7.20/1.53  --prep_def_merge_tr_red                 false
% 7.20/1.53  --prep_def_merge_tr_cl                  false
% 7.20/1.53  --smt_preprocessing                     true
% 7.20/1.53  --smt_ac_axioms                         fast
% 7.20/1.53  --preprocessed_out                      false
% 7.20/1.53  --preprocessed_stats                    false
% 7.20/1.53  
% 7.20/1.53  ------ Abstraction refinement Options
% 7.20/1.53  
% 7.20/1.53  --abstr_ref                             []
% 7.20/1.53  --abstr_ref_prep                        false
% 7.20/1.53  --abstr_ref_until_sat                   false
% 7.20/1.53  --abstr_ref_sig_restrict                funpre
% 7.20/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.20/1.53  --abstr_ref_under                       []
% 7.20/1.53  
% 7.20/1.53  ------ SAT Options
% 7.20/1.53  
% 7.20/1.53  --sat_mode                              false
% 7.20/1.53  --sat_fm_restart_options                ""
% 7.20/1.53  --sat_gr_def                            false
% 7.20/1.53  --sat_epr_types                         true
% 7.20/1.53  --sat_non_cyclic_types                  false
% 7.20/1.53  --sat_finite_models                     false
% 7.20/1.53  --sat_fm_lemmas                         false
% 7.20/1.53  --sat_fm_prep                           false
% 7.20/1.53  --sat_fm_uc_incr                        true
% 7.20/1.53  --sat_out_model                         small
% 7.20/1.53  --sat_out_clauses                       false
% 7.20/1.53  
% 7.20/1.53  ------ QBF Options
% 7.20/1.53  
% 7.20/1.53  --qbf_mode                              false
% 7.20/1.53  --qbf_elim_univ                         false
% 7.20/1.53  --qbf_dom_inst                          none
% 7.20/1.53  --qbf_dom_pre_inst                      false
% 7.20/1.53  --qbf_sk_in                             false
% 7.20/1.53  --qbf_pred_elim                         true
% 7.20/1.53  --qbf_split                             512
% 7.20/1.53  
% 7.20/1.53  ------ BMC1 Options
% 7.20/1.53  
% 7.20/1.53  --bmc1_incremental                      false
% 7.20/1.53  --bmc1_axioms                           reachable_all
% 7.20/1.53  --bmc1_min_bound                        0
% 7.20/1.53  --bmc1_max_bound                        -1
% 7.20/1.53  --bmc1_max_bound_default                -1
% 7.20/1.53  --bmc1_symbol_reachability              true
% 7.20/1.53  --bmc1_property_lemmas                  false
% 7.20/1.53  --bmc1_k_induction                      false
% 7.20/1.53  --bmc1_non_equiv_states                 false
% 7.20/1.53  --bmc1_deadlock                         false
% 7.20/1.53  --bmc1_ucm                              false
% 7.20/1.53  --bmc1_add_unsat_core                   none
% 7.20/1.53  --bmc1_unsat_core_children              false
% 7.20/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.20/1.53  --bmc1_out_stat                         full
% 7.20/1.53  --bmc1_ground_init                      false
% 7.20/1.53  --bmc1_pre_inst_next_state              false
% 7.20/1.53  --bmc1_pre_inst_state                   false
% 7.20/1.53  --bmc1_pre_inst_reach_state             false
% 7.20/1.53  --bmc1_out_unsat_core                   false
% 7.20/1.53  --bmc1_aig_witness_out                  false
% 7.20/1.53  --bmc1_verbose                          false
% 7.20/1.53  --bmc1_dump_clauses_tptp                false
% 7.20/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.20/1.53  --bmc1_dump_file                        -
% 7.20/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.20/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.20/1.53  --bmc1_ucm_extend_mode                  1
% 7.20/1.53  --bmc1_ucm_init_mode                    2
% 7.20/1.53  --bmc1_ucm_cone_mode                    none
% 7.20/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.20/1.53  --bmc1_ucm_relax_model                  4
% 7.20/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.20/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.20/1.53  --bmc1_ucm_layered_model                none
% 7.20/1.53  --bmc1_ucm_max_lemma_size               10
% 7.20/1.53  
% 7.20/1.53  ------ AIG Options
% 7.20/1.53  
% 7.20/1.53  --aig_mode                              false
% 7.20/1.53  
% 7.20/1.53  ------ Instantiation Options
% 7.20/1.53  
% 7.20/1.53  --instantiation_flag                    true
% 7.20/1.53  --inst_sos_flag                         false
% 7.20/1.53  --inst_sos_phase                        true
% 7.20/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.20/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.20/1.53  --inst_lit_sel_side                     none
% 7.20/1.53  --inst_solver_per_active                1400
% 7.20/1.53  --inst_solver_calls_frac                1.
% 7.20/1.53  --inst_passive_queue_type               priority_queues
% 7.20/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.20/1.53  --inst_passive_queues_freq              [25;2]
% 7.20/1.53  --inst_dismatching                      true
% 7.20/1.53  --inst_eager_unprocessed_to_passive     true
% 7.20/1.53  --inst_prop_sim_given                   true
% 7.20/1.53  --inst_prop_sim_new                     false
% 7.20/1.53  --inst_subs_new                         false
% 7.20/1.53  --inst_eq_res_simp                      false
% 7.20/1.53  --inst_subs_given                       false
% 7.20/1.53  --inst_orphan_elimination               true
% 7.20/1.53  --inst_learning_loop_flag               true
% 7.20/1.53  --inst_learning_start                   3000
% 7.20/1.53  --inst_learning_factor                  2
% 7.20/1.53  --inst_start_prop_sim_after_learn       3
% 7.20/1.53  --inst_sel_renew                        solver
% 7.20/1.53  --inst_lit_activity_flag                true
% 7.20/1.53  --inst_restr_to_given                   false
% 7.20/1.53  --inst_activity_threshold               500
% 7.20/1.53  --inst_out_proof                        true
% 7.20/1.53  
% 7.20/1.53  ------ Resolution Options
% 7.20/1.53  
% 7.20/1.53  --resolution_flag                       false
% 7.20/1.53  --res_lit_sel                           adaptive
% 7.20/1.53  --res_lit_sel_side                      none
% 7.20/1.53  --res_ordering                          kbo
% 7.20/1.53  --res_to_prop_solver                    active
% 7.20/1.53  --res_prop_simpl_new                    false
% 7.20/1.53  --res_prop_simpl_given                  true
% 7.20/1.53  --res_passive_queue_type                priority_queues
% 7.20/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.20/1.53  --res_passive_queues_freq               [15;5]
% 7.20/1.53  --res_forward_subs                      full
% 7.20/1.53  --res_backward_subs                     full
% 7.20/1.53  --res_forward_subs_resolution           true
% 7.20/1.53  --res_backward_subs_resolution          true
% 7.20/1.53  --res_orphan_elimination                true
% 7.20/1.53  --res_time_limit                        2.
% 7.20/1.53  --res_out_proof                         true
% 7.20/1.53  
% 7.20/1.53  ------ Superposition Options
% 7.20/1.53  
% 7.20/1.53  --superposition_flag                    true
% 7.20/1.53  --sup_passive_queue_type                priority_queues
% 7.20/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.20/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.20/1.53  --demod_completeness_check              fast
% 7.20/1.53  --demod_use_ground                      true
% 7.20/1.53  --sup_to_prop_solver                    passive
% 7.20/1.53  --sup_prop_simpl_new                    true
% 7.20/1.53  --sup_prop_simpl_given                  true
% 7.20/1.53  --sup_fun_splitting                     false
% 7.20/1.53  --sup_smt_interval                      50000
% 7.20/1.53  
% 7.20/1.53  ------ Superposition Simplification Setup
% 7.20/1.53  
% 7.20/1.53  --sup_indices_passive                   []
% 7.20/1.53  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.20/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.20/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_full_bw                           [BwDemod]
% 7.20/1.53  --sup_immed_triv                        [TrivRules]
% 7.20/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.20/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_immed_bw_main                     []
% 7.20/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.20/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.20/1.53  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.20/1.53  
% 7.20/1.53  ------ Combination Options
% 7.20/1.53  
% 7.20/1.53  --comb_res_mult                         3
% 7.20/1.53  --comb_sup_mult                         2
% 7.20/1.53  --comb_inst_mult                        10
% 7.20/1.53  
% 7.20/1.53  ------ Debug Options
% 7.20/1.53  
% 7.20/1.53  --dbg_backtrace                         false
% 7.20/1.53  --dbg_dump_prop_clauses                 false
% 7.20/1.53  --dbg_dump_prop_clauses_file            -
% 7.20/1.53  --dbg_out_stat                          false
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  ------ Proving...
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  % SZS status Theorem for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  fof(f4,axiom,(
% 7.20/1.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f13,plain,(
% 7.20/1.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f4])).
% 7.20/1.53  
% 7.20/1.53  fof(f46,plain,(
% 7.20/1.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 7.20/1.53    inference(cnf_transformation,[],[f13])).
% 7.20/1.53  
% 7.20/1.53  fof(f2,axiom,(
% 7.20/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f12,plain,(
% 7.20/1.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f2])).
% 7.20/1.53  
% 7.20/1.53  fof(f28,plain,(
% 7.20/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.53    inference(nnf_transformation,[],[f12])).
% 7.20/1.53  
% 7.20/1.53  fof(f29,plain,(
% 7.20/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.53    inference(rectify,[],[f28])).
% 7.20/1.53  
% 7.20/1.53  fof(f30,plain,(
% 7.20/1.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f31,plain,(
% 7.20/1.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.20/1.53  
% 7.20/1.53  fof(f43,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f31])).
% 7.20/1.53  
% 7.20/1.53  fof(f44,plain,(
% 7.20/1.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK1(X0,X1),X1)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f31])).
% 7.20/1.53  
% 7.20/1.53  fof(f9,axiom,(
% 7.20/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f20,plain,(
% 7.20/1.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f9])).
% 7.20/1.53  
% 7.20/1.53  fof(f21,plain,(
% 7.20/1.53    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.20/1.53    inference(flattening,[],[f20])).
% 7.20/1.53  
% 7.20/1.53  fof(f32,plain,(
% 7.20/1.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.20/1.53    inference(nnf_transformation,[],[f21])).
% 7.20/1.53  
% 7.20/1.53  fof(f33,plain,(
% 7.20/1.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.20/1.53    inference(rectify,[],[f32])).
% 7.20/1.53  
% 7.20/1.53  fof(f34,plain,(
% 7.20/1.53    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f35,plain,(
% 7.20/1.53    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK2(X0,X1))) != sK2(X0,X1) & r1_tarski(sK2(X0,X1),X1) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f33,f34])).
% 7.20/1.53  
% 7.20/1.53  fof(f51,plain,(
% 7.20/1.53    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f35])).
% 7.20/1.53  
% 7.20/1.53  fof(f10,conjecture,(
% 7.20/1.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f11,negated_conjecture,(
% 7.20/1.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_hidden(X2,X1) => k6_domain_1(u1_struct_0(X0),X2) = k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))))))))),
% 7.20/1.53    inference(negated_conjecture,[],[f10])).
% 7.20/1.53  
% 7.20/1.53  fof(f22,plain,(
% 7.20/1.53    ? [X0] : (? [X1] : ((? [X2] : ((k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1)) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f11])).
% 7.20/1.53  
% 7.20/1.53  fof(f23,plain,(
% 7.20/1.53    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.20/1.53    inference(flattening,[],[f22])).
% 7.20/1.53  
% 7.20/1.53  fof(f38,plain,(
% 7.20/1.53    ( ! [X0,X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) => (k6_domain_1(u1_struct_0(X0),sK5) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),sK5))) & r2_hidden(sK5,X1) & m1_subset_1(sK5,u1_struct_0(X0)))) )),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f37,plain,(
% 7.20/1.53    ( ! [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),sK4,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,sK4) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(sK4,X0) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f36,plain,(
% 7.20/1.53    ? [X0] : (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(X0),X2) != k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & v2_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k6_domain_1(u1_struct_0(sK3),X2) != k9_subset_1(u1_struct_0(sK3),X1,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),X2))) & r2_hidden(X2,X1) & m1_subset_1(X2,u1_struct_0(sK3))) & v2_tex_2(X1,sK3) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f39,plain,(
% 7.20/1.53    ((k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) & r2_hidden(sK5,sK4) & m1_subset_1(sK5,u1_struct_0(sK3))) & v2_tex_2(sK4,sK3) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f23,f38,f37,f36])).
% 7.20/1.53  
% 7.20/1.53  fof(f57,plain,(
% 7.20/1.53    l1_pre_topc(sK3)),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f55,plain,(
% 7.20/1.53    ~v2_struct_0(sK3)),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f56,plain,(
% 7.20/1.53    v2_pre_topc(sK3)),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f7,axiom,(
% 7.20/1.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f16,plain,(
% 7.20/1.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f7])).
% 7.20/1.53  
% 7.20/1.53  fof(f17,plain,(
% 7.20/1.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.20/1.53    inference(flattening,[],[f16])).
% 7.20/1.53  
% 7.20/1.53  fof(f49,plain,(
% 7.20/1.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f17])).
% 7.20/1.53  
% 7.20/1.53  fof(f60,plain,(
% 7.20/1.53    m1_subset_1(sK5,u1_struct_0(sK3))),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f8,axiom,(
% 7.20/1.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f18,plain,(
% 7.20/1.53    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 7.20/1.53    inference(ennf_transformation,[],[f8])).
% 7.20/1.53  
% 7.20/1.53  fof(f19,plain,(
% 7.20/1.53    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 7.20/1.53    inference(flattening,[],[f18])).
% 7.20/1.53  
% 7.20/1.53  fof(f50,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f19])).
% 7.20/1.53  
% 7.20/1.53  fof(f3,axiom,(
% 7.20/1.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f45,plain,(
% 7.20/1.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f3])).
% 7.20/1.53  
% 7.20/1.53  fof(f63,plain,(
% 7.20/1.53    ( ! [X0,X1] : (k2_tarski(X1,X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 7.20/1.53    inference(definition_unfolding,[],[f50,f45])).
% 7.20/1.53  
% 7.20/1.53  fof(f1,axiom,(
% 7.20/1.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f24,plain,(
% 7.20/1.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.53    inference(nnf_transformation,[],[f1])).
% 7.20/1.53  
% 7.20/1.53  fof(f25,plain,(
% 7.20/1.53    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.53    inference(rectify,[],[f24])).
% 7.20/1.53  
% 7.20/1.53  fof(f26,plain,(
% 7.20/1.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 7.20/1.53    introduced(choice_axiom,[])).
% 7.20/1.53  
% 7.20/1.53  fof(f27,plain,(
% 7.20/1.53    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 7.20/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.20/1.53  
% 7.20/1.53  fof(f40,plain,(
% 7.20/1.53    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f27])).
% 7.20/1.53  
% 7.20/1.53  fof(f6,axiom,(
% 7.20/1.53    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 7.20/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.20/1.53  
% 7.20/1.53  fof(f15,plain,(
% 7.20/1.53    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 7.20/1.53    inference(ennf_transformation,[],[f6])).
% 7.20/1.53  
% 7.20/1.53  fof(f48,plain,(
% 7.20/1.53    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 7.20/1.53    inference(cnf_transformation,[],[f15])).
% 7.20/1.53  
% 7.20/1.53  fof(f62,plain,(
% 7.20/1.53    k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f61,plain,(
% 7.20/1.53    r2_hidden(sK5,sK4)),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f59,plain,(
% 7.20/1.53    v2_tex_2(sK4,sK3)),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  fof(f58,plain,(
% 7.20/1.53    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))),
% 7.20/1.53    inference(cnf_transformation,[],[f39])).
% 7.20/1.53  
% 7.20/1.53  cnf(c_5,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.20/1.53      | ~ r2_hidden(X2,X0)
% 7.20/1.53      | r2_hidden(X2,X1) ),
% 7.20/1.53      inference(cnf_transformation,[],[f46]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_10023,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.20/1.53      | ~ r2_hidden(sK1(X0,sK4),X0)
% 7.20/1.53      | r2_hidden(sK1(X0,sK4),X1) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_17490,plain,
% 7.20/1.53      ( ~ m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5))
% 7.20/1.53      | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_10023]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_3,plain,
% 7.20/1.53      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 7.20/1.53      inference(cnf_transformation,[],[f43]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1450,plain,
% 7.20/1.53      ( r1_tarski(X0,sK4) | r2_hidden(sK1(X0,sK4),X0) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_3]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_6646,plain,
% 7.20/1.53      ( r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.20/1.53      | r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),k2_tarski(sK5,sK5)) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1450]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2,plain,
% 7.20/1.53      ( r1_tarski(X0,X1) | ~ r2_hidden(sK1(X0,X1),X1) ),
% 7.20/1.53      inference(cnf_transformation,[],[f44]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1451,plain,
% 7.20/1.53      ( r1_tarski(X0,sK4) | ~ r2_hidden(sK1(X0,sK4),sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_2]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_6647,plain,
% 7.20/1.53      ( r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.20/1.53      | ~ r2_hidden(sK1(k2_tarski(sK5,sK5),sK4),sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1451]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_864,plain,
% 7.20/1.53      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 7.20/1.53      theory(equality) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1460,plain,
% 7.20/1.53      ( ~ r1_tarski(X0,sK4) | r1_tarski(X1,sK4) | X1 != X0 ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_864]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2895,plain,
% 7.20/1.53      ( ~ r1_tarski(X0,sK4)
% 7.20/1.53      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) != X0 ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1460]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_5057,plain,
% 7.20/1.53      ( ~ r1_tarski(k2_tarski(sK5,sK5),sK4)
% 7.20/1.53      | r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) != k2_tarski(sK5,sK5) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_2895]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_866,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.20/1.53      theory(equality) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1730,plain,
% 7.20/1.53      ( m1_subset_1(X0,X1)
% 7.20/1.53      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | X0 != k6_domain_1(sK4,sK5)
% 7.20/1.53      | X1 != k1_zfmisc_1(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_866]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2384,plain,
% 7.20/1.53      ( m1_subset_1(X0,k1_zfmisc_1(sK4))
% 7.20/1.53      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | X0 != k6_domain_1(sK4,sK5)
% 7.20/1.53      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1730]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_4249,plain,
% 7.20/1.53      ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | ~ m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | k2_tarski(sK5,sK5) != k6_domain_1(sK4,sK5)
% 7.20/1.53      | k1_zfmisc_1(sK4) != k1_zfmisc_1(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_2384]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_13,plain,
% 7.20/1.53      ( ~ v2_tex_2(X0,X1)
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.20/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.20/1.53      | ~ r1_tarski(X2,X0)
% 7.20/1.53      | v2_struct_0(X1)
% 7.20/1.53      | ~ v2_pre_topc(X1)
% 7.20/1.53      | ~ l1_pre_topc(X1)
% 7.20/1.53      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 7.20/1.53      inference(cnf_transformation,[],[f51]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_19,negated_conjecture,
% 7.20/1.53      ( l1_pre_topc(sK3) ),
% 7.20/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_232,plain,
% 7.20/1.53      ( ~ v2_tex_2(X0,X1)
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.20/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.20/1.53      | ~ r1_tarski(X2,X0)
% 7.20/1.53      | v2_struct_0(X1)
% 7.20/1.53      | ~ v2_pre_topc(X1)
% 7.20/1.53      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 7.20/1.53      | sK3 != X1 ),
% 7.20/1.53      inference(resolution_lifted,[status(thm)],[c_13,c_19]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_233,plain,
% 7.20/1.53      ( ~ v2_tex_2(X0,sK3)
% 7.20/1.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ r1_tarski(X1,X0)
% 7.20/1.53      | v2_struct_0(sK3)
% 7.20/1.53      | ~ v2_pre_topc(sK3)
% 7.20/1.53      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.20/1.53      inference(unflattening,[status(thm)],[c_232]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_21,negated_conjecture,
% 7.20/1.53      ( ~ v2_struct_0(sK3) ),
% 7.20/1.53      inference(cnf_transformation,[],[f55]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_20,negated_conjecture,
% 7.20/1.53      ( v2_pre_topc(sK3) ),
% 7.20/1.53      inference(cnf_transformation,[],[f56]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_237,plain,
% 7.20/1.53      ( ~ v2_tex_2(X0,sK3)
% 7.20/1.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ r1_tarski(X1,X0)
% 7.20/1.53      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.20/1.53      inference(global_propositional_subsumption,
% 7.20/1.53                [status(thm)],
% 7.20/1.53                [c_233,c_21,c_20]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_238,plain,
% 7.20/1.53      ( ~ v2_tex_2(X0,sK3)
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ r1_tarski(X1,X0)
% 7.20/1.53      | k9_subset_1(u1_struct_0(sK3),X0,k2_pre_topc(sK3,X1)) = X1 ),
% 7.20/1.53      inference(renaming,[status(thm)],[c_237]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1348,plain,
% 7.20/1.53      ( ~ v2_tex_2(sK4,sK3)
% 7.20/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ r1_tarski(X0,sK4)
% 7.20/1.53      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,X0)) = X0 ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_238]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2551,plain,
% 7.20/1.53      ( ~ v2_tex_2(sK4,sK3)
% 7.20/1.53      | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ r1_tarski(k6_domain_1(u1_struct_0(sK3),sK5),sK4)
% 7.20/1.53      | k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1348]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_861,plain,( X0 = X0 ),theory(equality) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2385,plain,
% 7.20/1.53      ( k1_zfmisc_1(sK4) = k1_zfmisc_1(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_861]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_8,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,X1)
% 7.20/1.53      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 7.20/1.53      | v1_xboole_0(X1) ),
% 7.20/1.53      inference(cnf_transformation,[],[f49]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1682,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
% 7.20/1.53      | m1_subset_1(k6_domain_1(u1_struct_0(sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2119,plain,
% 7.20/1.53      ( m1_subset_1(k6_domain_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | ~ m1_subset_1(sK5,u1_struct_0(sK3))
% 7.20/1.53      | v1_xboole_0(u1_struct_0(sK3)) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1682]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_16,negated_conjecture,
% 7.20/1.53      ( m1_subset_1(sK5,u1_struct_0(sK3)) ),
% 7.20/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1205,plain,
% 7.20/1.53      ( m1_subset_1(sK5,u1_struct_0(sK3)) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_9,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,X1)
% 7.20/1.53      | v1_xboole_0(X1)
% 7.20/1.53      | k2_tarski(X0,X0) = k6_domain_1(X1,X0) ),
% 7.20/1.53      inference(cnf_transformation,[],[f63]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1207,plain,
% 7.20/1.53      ( k2_tarski(X0,X0) = k6_domain_1(X1,X0)
% 7.20/1.53      | m1_subset_1(X0,X1) != iProver_top
% 7.20/1.53      | v1_xboole_0(X1) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_2089,plain,
% 7.20/1.53      ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
% 7.20/1.53      | v1_xboole_0(u1_struct_0(sK3)) = iProver_top ),
% 7.20/1.53      inference(superposition,[status(thm)],[c_1205,c_1207]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1410,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,sK4)
% 7.20/1.53      | v1_xboole_0(sK4)
% 7.20/1.53      | k2_tarski(X0,X0) = k6_domain_1(sK4,X0) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_9]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1617,plain,
% 7.20/1.53      ( ~ m1_subset_1(sK5,sK4)
% 7.20/1.53      | v1_xboole_0(sK4)
% 7.20/1.53      | k2_tarski(sK5,sK5) = k6_domain_1(sK4,sK5) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1410]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1411,plain,
% 7.20/1.53      ( ~ m1_subset_1(X0,sK4)
% 7.20/1.53      | m1_subset_1(k6_domain_1(sK4,X0),k1_zfmisc_1(sK4))
% 7.20/1.53      | v1_xboole_0(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_8]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1572,plain,
% 7.20/1.53      ( m1_subset_1(k6_domain_1(sK4,sK5),k1_zfmisc_1(sK4))
% 7.20/1.53      | ~ m1_subset_1(sK5,sK4)
% 7.20/1.53      | v1_xboole_0(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1411]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1,plain,
% 7.20/1.53      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 7.20/1.53      inference(cnf_transformation,[],[f40]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1512,plain,
% 7.20/1.53      ( ~ r2_hidden(sK5,u1_struct_0(sK3))
% 7.20/1.53      | ~ v1_xboole_0(u1_struct_0(sK3)) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1513,plain,
% 7.20/1.53      ( r2_hidden(sK5,u1_struct_0(sK3)) != iProver_top
% 7.20/1.53      | v1_xboole_0(u1_struct_0(sK3)) != iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_1512]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1444,plain,
% 7.20/1.53      ( k6_domain_1(u1_struct_0(sK3),sK5) = k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_861]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_862,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1374,plain,
% 7.20/1.53      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != X0
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) != X0
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_862]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1443,plain,
% 7.20/1.53      ( k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) != k6_domain_1(u1_struct_0(sK3),sK5)
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) = k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
% 7.20/1.53      | k6_domain_1(u1_struct_0(sK3),sK5) != k6_domain_1(u1_struct_0(sK3),sK5) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1374]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1365,plain,
% 7.20/1.53      ( ~ m1_subset_1(sK4,k1_zfmisc_1(X0))
% 7.20/1.53      | r2_hidden(sK5,X0)
% 7.20/1.53      | ~ r2_hidden(sK5,sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_5]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1440,plain,
% 7.20/1.53      ( ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3)))
% 7.20/1.53      | r2_hidden(sK5,u1_struct_0(sK3))
% 7.20/1.53      | ~ r2_hidden(sK5,sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1365]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1441,plain,
% 7.20/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) != iProver_top
% 7.20/1.53      | r2_hidden(sK5,u1_struct_0(sK3)) = iProver_top
% 7.20/1.53      | r2_hidden(sK5,sK4) != iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_1440]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_7,plain,
% 7.20/1.53      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 7.20/1.53      inference(cnf_transformation,[],[f48]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1357,plain,
% 7.20/1.53      ( m1_subset_1(sK5,sK4) | ~ r2_hidden(sK5,sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_7]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_1354,plain,
% 7.20/1.53      ( ~ r2_hidden(sK5,sK4) | ~ v1_xboole_0(sK4) ),
% 7.20/1.53      inference(instantiation,[status(thm)],[c_1]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_14,negated_conjecture,
% 7.20/1.53      ( k6_domain_1(u1_struct_0(sK3),sK5) != k9_subset_1(u1_struct_0(sK3),sK4,k2_pre_topc(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
% 7.20/1.53      inference(cnf_transformation,[],[f62]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_15,negated_conjecture,
% 7.20/1.53      ( r2_hidden(sK5,sK4) ),
% 7.20/1.53      inference(cnf_transformation,[],[f61]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_28,plain,
% 7.20/1.53      ( r2_hidden(sK5,sK4) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_17,negated_conjecture,
% 7.20/1.53      ( v2_tex_2(sK4,sK3) ),
% 7.20/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_18,negated_conjecture,
% 7.20/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) ),
% 7.20/1.53      inference(cnf_transformation,[],[f58]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(c_25,plain,
% 7.20/1.53      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK3))) = iProver_top ),
% 7.20/1.53      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.20/1.53  
% 7.20/1.53  cnf(contradiction,plain,
% 7.20/1.53      ( $false ),
% 7.20/1.53      inference(minisat,
% 7.20/1.53                [status(thm)],
% 7.20/1.53                [c_17490,c_6646,c_6647,c_5057,c_4249,c_2551,c_2385,
% 7.20/1.53                 c_2119,c_2089,c_1617,c_1572,c_1513,c_1512,c_1444,c_1443,
% 7.20/1.53                 c_1441,c_1440,c_1357,c_1354,c_14,c_28,c_15,c_16,c_17,
% 7.20/1.53                 c_25,c_18]) ).
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.20/1.53  
% 7.20/1.53  ------                               Statistics
% 7.20/1.53  
% 7.20/1.53  ------ General
% 7.20/1.53  
% 7.20/1.53  abstr_ref_over_cycles:                  0
% 7.20/1.53  abstr_ref_under_cycles:                 0
% 7.20/1.53  gc_basic_clause_elim:                   0
% 7.20/1.53  forced_gc_time:                         0
% 7.20/1.53  parsing_time:                           0.01
% 7.20/1.53  unif_index_cands_time:                  0.
% 7.20/1.53  unif_index_add_time:                    0.
% 7.20/1.53  orderings_time:                         0.
% 7.20/1.53  out_proof_time:                         0.008
% 7.20/1.53  total_time:                             0.581
% 7.20/1.53  num_of_symbols:                         51
% 7.20/1.53  num_of_terms:                           13178
% 7.20/1.53  
% 7.20/1.53  ------ Preprocessing
% 7.20/1.53  
% 7.20/1.53  num_of_splits:                          0
% 7.20/1.53  num_of_split_atoms:                     0
% 7.20/1.53  num_of_reused_defs:                     0
% 7.20/1.53  num_eq_ax_congr_red:                    25
% 7.20/1.53  num_of_sem_filtered_clauses:            1
% 7.20/1.53  num_of_subtypes:                        0
% 7.20/1.53  monotx_restored_types:                  0
% 7.20/1.53  sat_num_of_epr_types:                   0
% 7.20/1.53  sat_num_of_non_cyclic_types:            0
% 7.20/1.53  sat_guarded_non_collapsed_types:        0
% 7.20/1.53  num_pure_diseq_elim:                    0
% 7.20/1.53  simp_replaced_by:                       0
% 7.20/1.53  res_preprocessed:                       104
% 7.20/1.53  prep_upred:                             0
% 7.20/1.53  prep_unflattend:                        22
% 7.20/1.53  smt_new_axioms:                         0
% 7.20/1.53  pred_elim_cands:                        5
% 7.20/1.53  pred_elim:                              3
% 7.20/1.53  pred_elim_cl:                           3
% 7.20/1.53  pred_elim_cycles:                       7
% 7.20/1.53  merged_defs:                            0
% 7.20/1.53  merged_defs_ncl:                        0
% 7.20/1.53  bin_hyper_res:                          0
% 7.20/1.53  prep_cycles:                            4
% 7.20/1.53  pred_elim_time:                         0.011
% 7.20/1.53  splitting_time:                         0.
% 7.20/1.53  sem_filter_time:                        0.
% 7.20/1.53  monotx_time:                            0.001
% 7.20/1.53  subtype_inf_time:                       0.
% 7.20/1.53  
% 7.20/1.53  ------ Problem properties
% 7.20/1.53  
% 7.20/1.53  clauses:                                19
% 7.20/1.53  conjectures:                            5
% 7.20/1.53  epr:                                    5
% 7.20/1.53  horn:                                   13
% 7.20/1.53  ground:                                 5
% 7.20/1.53  unary:                                  5
% 7.20/1.53  binary:                                 5
% 7.20/1.53  lits:                                   44
% 7.20/1.53  lits_eq:                                4
% 7.20/1.53  fd_pure:                                0
% 7.20/1.53  fd_pseudo:                              0
% 7.20/1.53  fd_cond:                                0
% 7.20/1.53  fd_pseudo_cond:                         0
% 7.20/1.53  ac_symbols:                             0
% 7.20/1.53  
% 7.20/1.53  ------ Propositional Solver
% 7.20/1.53  
% 7.20/1.53  prop_solver_calls:                      31
% 7.20/1.53  prop_fast_solver_calls:                 1358
% 7.20/1.53  smt_solver_calls:                       0
% 7.20/1.53  smt_fast_solver_calls:                  0
% 7.20/1.53  prop_num_of_clauses:                    5907
% 7.20/1.53  prop_preprocess_simplified:             9923
% 7.20/1.53  prop_fo_subsumed:                       41
% 7.20/1.53  prop_solver_time:                       0.
% 7.20/1.53  smt_solver_time:                        0.
% 7.20/1.53  smt_fast_solver_time:                   0.
% 7.20/1.53  prop_fast_solver_time:                  0.
% 7.20/1.53  prop_unsat_core_time:                   0.
% 7.20/1.53  
% 7.20/1.53  ------ QBF
% 7.20/1.53  
% 7.20/1.53  qbf_q_res:                              0
% 7.20/1.53  qbf_num_tautologies:                    0
% 7.20/1.53  qbf_prep_cycles:                        0
% 7.20/1.53  
% 7.20/1.53  ------ BMC1
% 7.20/1.53  
% 7.20/1.53  bmc1_current_bound:                     -1
% 7.20/1.53  bmc1_last_solved_bound:                 -1
% 7.20/1.53  bmc1_unsat_core_size:                   -1
% 7.20/1.53  bmc1_unsat_core_parents_size:           -1
% 7.20/1.53  bmc1_merge_next_fun:                    0
% 7.20/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.20/1.53  
% 7.20/1.53  ------ Instantiation
% 7.20/1.53  
% 7.20/1.53  inst_num_of_clauses:                    1453
% 7.20/1.53  inst_num_in_passive:                    290
% 7.20/1.53  inst_num_in_active:                     798
% 7.20/1.53  inst_num_in_unprocessed:                364
% 7.20/1.53  inst_num_of_loops:                      963
% 7.20/1.53  inst_num_of_learning_restarts:          0
% 7.20/1.53  inst_num_moves_active_passive:          158
% 7.20/1.53  inst_lit_activity:                      0
% 7.20/1.53  inst_lit_activity_moves:                0
% 7.20/1.53  inst_num_tautologies:                   0
% 7.20/1.53  inst_num_prop_implied:                  0
% 7.20/1.53  inst_num_existing_simplified:           0
% 7.20/1.53  inst_num_eq_res_simplified:             0
% 7.20/1.53  inst_num_child_elim:                    0
% 7.20/1.53  inst_num_of_dismatching_blockings:      366
% 7.20/1.53  inst_num_of_non_proper_insts:           1508
% 7.20/1.53  inst_num_of_duplicates:                 0
% 7.20/1.53  inst_inst_num_from_inst_to_res:         0
% 7.20/1.53  inst_dismatching_checking_time:         0.
% 7.20/1.53  
% 7.20/1.53  ------ Resolution
% 7.20/1.53  
% 7.20/1.53  res_num_of_clauses:                     0
% 7.20/1.53  res_num_in_passive:                     0
% 7.20/1.53  res_num_in_active:                      0
% 7.20/1.53  res_num_of_loops:                       108
% 7.20/1.53  res_forward_subset_subsumed:            153
% 7.20/1.53  res_backward_subset_subsumed:           0
% 7.20/1.53  res_forward_subsumed:                   0
% 7.20/1.53  res_backward_subsumed:                  0
% 7.20/1.53  res_forward_subsumption_resolution:     0
% 7.20/1.53  res_backward_subsumption_resolution:    0
% 7.20/1.53  res_clause_to_clause_subsumption:       2878
% 7.20/1.53  res_orphan_elimination:                 0
% 7.20/1.53  res_tautology_del:                      219
% 7.20/1.53  res_num_eq_res_simplified:              0
% 7.20/1.53  res_num_sel_changes:                    0
% 7.20/1.53  res_moves_from_active_to_pass:          0
% 7.20/1.53  
% 7.20/1.53  ------ Superposition
% 7.20/1.53  
% 7.20/1.53  sup_time_total:                         0.
% 7.20/1.53  sup_time_generating:                    0.
% 7.20/1.53  sup_time_sim_full:                      0.
% 7.20/1.53  sup_time_sim_immed:                     0.
% 7.20/1.53  
% 7.20/1.53  sup_num_of_clauses:                     632
% 7.20/1.53  sup_num_in_active:                      187
% 7.20/1.53  sup_num_in_passive:                     445
% 7.20/1.53  sup_num_of_loops:                       192
% 7.20/1.53  sup_fw_superposition:                   357
% 7.20/1.53  sup_bw_superposition:                   388
% 7.20/1.53  sup_immediate_simplified:               83
% 7.20/1.53  sup_given_eliminated:                   0
% 7.20/1.53  comparisons_done:                       0
% 7.20/1.53  comparisons_avoided:                    66
% 7.20/1.53  
% 7.20/1.53  ------ Simplifications
% 7.20/1.53  
% 7.20/1.53  
% 7.20/1.53  sim_fw_subset_subsumed:                 55
% 7.20/1.53  sim_bw_subset_subsumed:                 5
% 7.20/1.53  sim_fw_subsumed:                        16
% 7.20/1.53  sim_bw_subsumed:                        0
% 7.20/1.53  sim_fw_subsumption_res:                 1
% 7.20/1.53  sim_bw_subsumption_res:                 0
% 7.20/1.53  sim_tautology_del:                      16
% 7.20/1.53  sim_eq_tautology_del:                   2
% 7.20/1.53  sim_eq_res_simp:                        0
% 7.20/1.53  sim_fw_demodulated:                     3
% 7.20/1.53  sim_bw_demodulated:                     4
% 7.20/1.53  sim_light_normalised:                   13
% 7.20/1.53  sim_joinable_taut:                      0
% 7.20/1.53  sim_joinable_simp:                      0
% 7.20/1.53  sim_ac_normalised:                      0
% 7.20/1.53  sim_smt_subsumption:                    0
% 7.20/1.53  
%------------------------------------------------------------------------------
