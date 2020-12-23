%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:01 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :  168 ( 733 expanded)
%              Number of clauses        :   93 ( 205 expanded)
%              Number of leaves         :   23 ( 181 expanded)
%              Depth                    :   23
%              Number of atoms          :  555 (3367 expanded)
%              Number of equality atoms :  150 ( 222 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f58,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f19,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f47])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

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

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK6,X0)
        & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK5)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK5)
      & v2_pre_topc(sK5)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,
    ( v3_tex_2(sK6,sK5)
    & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))
    & v1_xboole_0(sK6)
    & l1_pre_topc(sK5)
    & v2_pre_topc(sK5)
    & ~ v2_struct_0(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f55,f54])).

fof(f83,plain,(
    v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f82,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f84,plain,(
    l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f59,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f85,plain,(
    v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f56])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f49,plain,(
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

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f51,plain,(
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
    inference(rectify,[],[f50])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != X1
        & r1_tarski(X1,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK4(X0,X1) != X1
                & r1_tarski(X1,sK4(X0,X1))
                & v2_tex_2(sK4(X0,X1),X0)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v3_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f56])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2561,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_17,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_29,negated_conjecture,
    ( v2_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_405,plain,
    ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_406,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( l1_pre_topc(sK5) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_408,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_30,c_28])).

cnf(c_2543,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_13,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2550,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4354,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
    | r2_hidden(X0,sK3(sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2550])).

cnf(c_4559,plain,
    ( m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
    | v1_xboole_0(sK3(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2561,c_4354])).

cnf(c_31,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_407,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | l1_pre_topc(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_406])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK3(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_416,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK3(X0))
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_417,plain,
    ( v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5)
    | ~ v1_xboole_0(sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_419,plain,
    ( ~ v1_xboole_0(sK3(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_30,c_28])).

cnf(c_520,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK3(sK5) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_419])).

cnf(c_521,plain,
    ( r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_522,plain,
    ( r2_hidden(sK0(sK3(sK5)),sK3(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_521])).

cnf(c_2620,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2708,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5))
    | ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r2_hidden(X0,sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_2620])).

cnf(c_2842,plain,
    ( ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
    | m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5))
    | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_2708])).

cnf(c_2843,plain,
    ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
    | r2_hidden(sK0(sK3(sK5)),sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2842])).

cnf(c_6325,plain,
    ( m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4559,c_31,c_33,c_407,c_522,c_2843])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2548,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6329,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_tarski(sK0(sK3(sK5)))
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6325,c_2548])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2551,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3916,plain,
    ( r1_tarski(sK3(sK5),u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2543,c_2551])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_3164,plain,
    ( ~ r1_tarski(sK3(sK5),X0)
    | r2_hidden(sK0(sK3(sK5)),X0)
    | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4127,plain,
    ( ~ r1_tarski(sK3(sK5),u1_struct_0(sK5))
    | r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5))
    | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
    inference(instantiation,[status(thm)],[c_3164])).

cnf(c_4131,plain,
    ( r1_tarski(sK3(sK5),u1_struct_0(sK5)) != iProver_top
    | r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
    | r2_hidden(sK0(sK3(sK5)),sK3(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4127])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_6314,plain,
    ( ~ r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5))
    | ~ v1_xboole_0(u1_struct_0(sK5)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6315,plain,
    ( r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6314])).

cnf(c_9211,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_tarski(sK0(sK3(sK5))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6329,c_522,c_3916,c_4131,c_6315])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2549,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_27,negated_conjecture,
    ( v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2545,plain,
    ( v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2556,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3532,plain,
    ( sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2545,c_2556])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2546,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_603,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_604,plain,
    ( ~ v2_tex_2(X0,sK5)
    | ~ v3_tex_2(X1,sK5)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_2540,plain,
    ( X0 = X1
    | v2_tex_2(X1,sK5) != iProver_top
    | v3_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_3100,plain,
    ( sK6 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(sK6,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_2540])).

cnf(c_25,negated_conjecture,
    ( v3_tex_2(sK6,sK5) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,plain,
    ( v3_tex_2(sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3150,plain,
    ( v2_tex_2(X0,sK5) != iProver_top
    | sK6 = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3100,c_36])).

cnf(c_3151,plain,
    ( sK6 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(sK6,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3150])).

cnf(c_3630,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3532,c_3151])).

cnf(c_7,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_86,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_515,plain,
    ( sK6 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_27])).

cnf(c_516,plain,
    ( k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_1925,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2992,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_1936,plain,
    ( ~ v3_tex_2(X0,X1)
    | v3_tex_2(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2633,plain,
    ( ~ v3_tex_2(X0,X1)
    | v3_tex_2(X2,sK5)
    | X2 != X0
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_1936])).

cnf(c_2780,plain,
    ( ~ v3_tex_2(X0,sK5)
    | v3_tex_2(X1,sK5)
    | X1 != X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2633])).

cnf(c_3189,plain,
    ( v3_tex_2(X0,sK5)
    | ~ v3_tex_2(sK6,sK5)
    | X0 != sK6
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2780])).

cnf(c_3190,plain,
    ( X0 != sK6
    | sK5 != sK5
    | v3_tex_2(X0,sK5) = iProver_top
    | v3_tex_2(sK6,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3189])).

cnf(c_3192,plain,
    ( sK5 != sK5
    | k1_xboole_0 != sK6
    | v3_tex_2(sK6,sK5) != iProver_top
    | v3_tex_2(k1_xboole_0,sK5) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3190])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2553,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3460,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | v3_tex_2(k1_xboole_0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2553,c_2540])).

cnf(c_4328,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
    | v2_tex_2(X0,sK5) != iProver_top
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3630,c_36,c_86,c_516,c_2992,c_3192,c_3460])).

cnf(c_4329,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4328])).

cnf(c_4335,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0
    | v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5) != iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2549,c_4329])).

cnf(c_24,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_387,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK5 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_388,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5))
    | v2_struct_0(sK5)
    | ~ l1_pre_topc(sK5) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_392,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5)
    | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_30,c_28])).

cnf(c_394,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_8510,plain,
    ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
    | k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4335,c_394,c_522,c_3916,c_4131,c_6315])).

cnf(c_8511,plain,
    ( k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0
    | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8510])).

cnf(c_8517,plain,
    ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6325,c_8511])).

cnf(c_9213,plain,
    ( k1_tarski(sK0(sK3(sK5))) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9211,c_8517])).

cnf(c_6,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_8,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3032,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6,c_8])).

cnf(c_9214,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_9213,c_3032])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:04:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.99/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.99/1.02  
% 3.99/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.99/1.02  
% 3.99/1.02  ------  iProver source info
% 3.99/1.02  
% 3.99/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.99/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.99/1.02  git: non_committed_changes: false
% 3.99/1.02  git: last_make_outside_of_git: false
% 3.99/1.02  
% 3.99/1.02  ------ 
% 3.99/1.02  
% 3.99/1.02  ------ Input Options
% 3.99/1.02  
% 3.99/1.02  --out_options                           all
% 3.99/1.02  --tptp_safe_out                         true
% 3.99/1.02  --problem_path                          ""
% 3.99/1.02  --include_path                          ""
% 3.99/1.02  --clausifier                            res/vclausify_rel
% 3.99/1.02  --clausifier_options                    ""
% 3.99/1.02  --stdin                                 false
% 3.99/1.02  --stats_out                             all
% 3.99/1.02  
% 3.99/1.02  ------ General Options
% 3.99/1.02  
% 3.99/1.02  --fof                                   false
% 3.99/1.02  --time_out_real                         305.
% 3.99/1.02  --time_out_virtual                      -1.
% 3.99/1.02  --symbol_type_check                     false
% 3.99/1.02  --clausify_out                          false
% 3.99/1.02  --sig_cnt_out                           false
% 3.99/1.02  --trig_cnt_out                          false
% 3.99/1.02  --trig_cnt_out_tolerance                1.
% 3.99/1.02  --trig_cnt_out_sk_spl                   false
% 3.99/1.02  --abstr_cl_out                          false
% 3.99/1.02  
% 3.99/1.02  ------ Global Options
% 3.99/1.02  
% 3.99/1.02  --schedule                              default
% 3.99/1.02  --add_important_lit                     false
% 3.99/1.02  --prop_solver_per_cl                    1000
% 3.99/1.02  --min_unsat_core                        false
% 3.99/1.02  --soft_assumptions                      false
% 3.99/1.02  --soft_lemma_size                       3
% 3.99/1.02  --prop_impl_unit_size                   0
% 3.99/1.02  --prop_impl_unit                        []
% 3.99/1.02  --share_sel_clauses                     true
% 3.99/1.02  --reset_solvers                         false
% 3.99/1.02  --bc_imp_inh                            [conj_cone]
% 3.99/1.02  --conj_cone_tolerance                   3.
% 3.99/1.02  --extra_neg_conj                        none
% 3.99/1.02  --large_theory_mode                     true
% 3.99/1.02  --prolific_symb_bound                   200
% 3.99/1.02  --lt_threshold                          2000
% 3.99/1.02  --clause_weak_htbl                      true
% 3.99/1.02  --gc_record_bc_elim                     false
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing Options
% 3.99/1.02  
% 3.99/1.02  --preprocessing_flag                    true
% 3.99/1.02  --time_out_prep_mult                    0.1
% 3.99/1.02  --splitting_mode                        input
% 3.99/1.02  --splitting_grd                         true
% 3.99/1.02  --splitting_cvd                         false
% 3.99/1.02  --splitting_cvd_svl                     false
% 3.99/1.02  --splitting_nvd                         32
% 3.99/1.02  --sub_typing                            true
% 3.99/1.02  --prep_gs_sim                           true
% 3.99/1.02  --prep_unflatten                        true
% 3.99/1.02  --prep_res_sim                          true
% 3.99/1.02  --prep_upred                            true
% 3.99/1.02  --prep_sem_filter                       exhaustive
% 3.99/1.02  --prep_sem_filter_out                   false
% 3.99/1.02  --pred_elim                             true
% 3.99/1.02  --res_sim_input                         true
% 3.99/1.02  --eq_ax_congr_red                       true
% 3.99/1.02  --pure_diseq_elim                       true
% 3.99/1.02  --brand_transform                       false
% 3.99/1.02  --non_eq_to_eq                          false
% 3.99/1.02  --prep_def_merge                        true
% 3.99/1.02  --prep_def_merge_prop_impl              false
% 3.99/1.02  --prep_def_merge_mbd                    true
% 3.99/1.02  --prep_def_merge_tr_red                 false
% 3.99/1.02  --prep_def_merge_tr_cl                  false
% 3.99/1.02  --smt_preprocessing                     true
% 3.99/1.02  --smt_ac_axioms                         fast
% 3.99/1.02  --preprocessed_out                      false
% 3.99/1.02  --preprocessed_stats                    false
% 3.99/1.02  
% 3.99/1.02  ------ Abstraction refinement Options
% 3.99/1.02  
% 3.99/1.02  --abstr_ref                             []
% 3.99/1.02  --abstr_ref_prep                        false
% 3.99/1.02  --abstr_ref_until_sat                   false
% 3.99/1.02  --abstr_ref_sig_restrict                funpre
% 3.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/1.02  --abstr_ref_under                       []
% 3.99/1.02  
% 3.99/1.02  ------ SAT Options
% 3.99/1.02  
% 3.99/1.02  --sat_mode                              false
% 3.99/1.02  --sat_fm_restart_options                ""
% 3.99/1.02  --sat_gr_def                            false
% 3.99/1.02  --sat_epr_types                         true
% 3.99/1.02  --sat_non_cyclic_types                  false
% 3.99/1.02  --sat_finite_models                     false
% 3.99/1.02  --sat_fm_lemmas                         false
% 3.99/1.02  --sat_fm_prep                           false
% 3.99/1.02  --sat_fm_uc_incr                        true
% 3.99/1.02  --sat_out_model                         small
% 3.99/1.02  --sat_out_clauses                       false
% 3.99/1.02  
% 3.99/1.02  ------ QBF Options
% 3.99/1.02  
% 3.99/1.02  --qbf_mode                              false
% 3.99/1.02  --qbf_elim_univ                         false
% 3.99/1.02  --qbf_dom_inst                          none
% 3.99/1.02  --qbf_dom_pre_inst                      false
% 3.99/1.02  --qbf_sk_in                             false
% 3.99/1.02  --qbf_pred_elim                         true
% 3.99/1.02  --qbf_split                             512
% 3.99/1.02  
% 3.99/1.02  ------ BMC1 Options
% 3.99/1.02  
% 3.99/1.02  --bmc1_incremental                      false
% 3.99/1.02  --bmc1_axioms                           reachable_all
% 3.99/1.02  --bmc1_min_bound                        0
% 3.99/1.02  --bmc1_max_bound                        -1
% 3.99/1.02  --bmc1_max_bound_default                -1
% 3.99/1.02  --bmc1_symbol_reachability              true
% 3.99/1.02  --bmc1_property_lemmas                  false
% 3.99/1.02  --bmc1_k_induction                      false
% 3.99/1.02  --bmc1_non_equiv_states                 false
% 3.99/1.02  --bmc1_deadlock                         false
% 3.99/1.02  --bmc1_ucm                              false
% 3.99/1.02  --bmc1_add_unsat_core                   none
% 3.99/1.02  --bmc1_unsat_core_children              false
% 3.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/1.02  --bmc1_out_stat                         full
% 3.99/1.02  --bmc1_ground_init                      false
% 3.99/1.02  --bmc1_pre_inst_next_state              false
% 3.99/1.02  --bmc1_pre_inst_state                   false
% 3.99/1.02  --bmc1_pre_inst_reach_state             false
% 3.99/1.02  --bmc1_out_unsat_core                   false
% 3.99/1.02  --bmc1_aig_witness_out                  false
% 3.99/1.02  --bmc1_verbose                          false
% 3.99/1.02  --bmc1_dump_clauses_tptp                false
% 3.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.99/1.02  --bmc1_dump_file                        -
% 3.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.99/1.02  --bmc1_ucm_extend_mode                  1
% 3.99/1.02  --bmc1_ucm_init_mode                    2
% 3.99/1.02  --bmc1_ucm_cone_mode                    none
% 3.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.99/1.02  --bmc1_ucm_relax_model                  4
% 3.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/1.02  --bmc1_ucm_layered_model                none
% 3.99/1.02  --bmc1_ucm_max_lemma_size               10
% 3.99/1.02  
% 3.99/1.02  ------ AIG Options
% 3.99/1.02  
% 3.99/1.02  --aig_mode                              false
% 3.99/1.02  
% 3.99/1.02  ------ Instantiation Options
% 3.99/1.02  
% 3.99/1.02  --instantiation_flag                    true
% 3.99/1.02  --inst_sos_flag                         true
% 3.99/1.02  --inst_sos_phase                        true
% 3.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/1.02  --inst_lit_sel_side                     num_symb
% 3.99/1.02  --inst_solver_per_active                1400
% 3.99/1.02  --inst_solver_calls_frac                1.
% 3.99/1.02  --inst_passive_queue_type               priority_queues
% 3.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/1.02  --inst_passive_queues_freq              [25;2]
% 3.99/1.02  --inst_dismatching                      true
% 3.99/1.02  --inst_eager_unprocessed_to_passive     true
% 3.99/1.02  --inst_prop_sim_given                   true
% 3.99/1.02  --inst_prop_sim_new                     false
% 3.99/1.02  --inst_subs_new                         false
% 3.99/1.02  --inst_eq_res_simp                      false
% 3.99/1.02  --inst_subs_given                       false
% 3.99/1.02  --inst_orphan_elimination               true
% 3.99/1.02  --inst_learning_loop_flag               true
% 3.99/1.02  --inst_learning_start                   3000
% 3.99/1.02  --inst_learning_factor                  2
% 3.99/1.02  --inst_start_prop_sim_after_learn       3
% 3.99/1.02  --inst_sel_renew                        solver
% 3.99/1.02  --inst_lit_activity_flag                true
% 3.99/1.02  --inst_restr_to_given                   false
% 3.99/1.02  --inst_activity_threshold               500
% 3.99/1.02  --inst_out_proof                        true
% 3.99/1.02  
% 3.99/1.02  ------ Resolution Options
% 3.99/1.02  
% 3.99/1.02  --resolution_flag                       true
% 3.99/1.02  --res_lit_sel                           adaptive
% 3.99/1.02  --res_lit_sel_side                      none
% 3.99/1.02  --res_ordering                          kbo
% 3.99/1.02  --res_to_prop_solver                    active
% 3.99/1.02  --res_prop_simpl_new                    false
% 3.99/1.02  --res_prop_simpl_given                  true
% 3.99/1.02  --res_passive_queue_type                priority_queues
% 3.99/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.02  --res_passive_queues_freq               [15;5]
% 3.99/1.02  --res_forward_subs                      full
% 3.99/1.02  --res_backward_subs                     full
% 3.99/1.02  --res_forward_subs_resolution           true
% 3.99/1.02  --res_backward_subs_resolution          true
% 3.99/1.02  --res_orphan_elimination                true
% 3.99/1.02  --res_time_limit                        2.
% 3.99/1.02  --res_out_proof                         true
% 3.99/1.02  
% 3.99/1.02  ------ Superposition Options
% 3.99/1.02  
% 3.99/1.02  --superposition_flag                    true
% 3.99/1.02  --sup_passive_queue_type                priority_queues
% 3.99/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.99/1.02  --demod_completeness_check              fast
% 3.99/1.02  --demod_use_ground                      true
% 3.99/1.02  --sup_to_prop_solver                    passive
% 3.99/1.02  --sup_prop_simpl_new                    true
% 3.99/1.02  --sup_prop_simpl_given                  true
% 3.99/1.02  --sup_fun_splitting                     true
% 3.99/1.02  --sup_smt_interval                      50000
% 3.99/1.02  
% 3.99/1.02  ------ Superposition Simplification Setup
% 3.99/1.02  
% 3.99/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.99/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.99/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.99/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.99/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.99/1.02  --sup_immed_triv                        [TrivRules]
% 3.99/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_immed_bw_main                     []
% 3.99/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.99/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_input_bw                          []
% 3.99/1.02  
% 3.99/1.02  ------ Combination Options
% 3.99/1.02  
% 3.99/1.02  --comb_res_mult                         3
% 3.99/1.02  --comb_sup_mult                         2
% 3.99/1.02  --comb_inst_mult                        10
% 3.99/1.02  
% 3.99/1.02  ------ Debug Options
% 3.99/1.02  
% 3.99/1.02  --dbg_backtrace                         false
% 3.99/1.02  --dbg_dump_prop_clauses                 false
% 3.99/1.02  --dbg_dump_prop_clauses_file            -
% 3.99/1.02  --dbg_out_stat                          false
% 3.99/1.02  ------ Parsing...
% 3.99/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.99/1.02  ------ Proving...
% 3.99/1.02  ------ Problem Properties 
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  clauses                                 28
% 3.99/1.02  conjectures                             3
% 3.99/1.02  EPR                                     6
% 3.99/1.02  Horn                                    21
% 3.99/1.02  unary                                   10
% 3.99/1.02  binary                                  8
% 3.99/1.02  lits                                    63
% 3.99/1.02  lits eq                                 6
% 3.99/1.02  fd_pure                                 0
% 3.99/1.02  fd_pseudo                               0
% 3.99/1.02  fd_cond                                 1
% 3.99/1.02  fd_pseudo_cond                          1
% 3.99/1.02  AC symbols                              0
% 3.99/1.02  
% 3.99/1.02  ------ Schedule dynamic 5 is on 
% 3.99/1.02  
% 3.99/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  ------ 
% 3.99/1.02  Current options:
% 3.99/1.02  ------ 
% 3.99/1.02  
% 3.99/1.02  ------ Input Options
% 3.99/1.02  
% 3.99/1.02  --out_options                           all
% 3.99/1.02  --tptp_safe_out                         true
% 3.99/1.02  --problem_path                          ""
% 3.99/1.02  --include_path                          ""
% 3.99/1.02  --clausifier                            res/vclausify_rel
% 3.99/1.02  --clausifier_options                    ""
% 3.99/1.02  --stdin                                 false
% 3.99/1.02  --stats_out                             all
% 3.99/1.02  
% 3.99/1.02  ------ General Options
% 3.99/1.02  
% 3.99/1.02  --fof                                   false
% 3.99/1.02  --time_out_real                         305.
% 3.99/1.02  --time_out_virtual                      -1.
% 3.99/1.02  --symbol_type_check                     false
% 3.99/1.02  --clausify_out                          false
% 3.99/1.02  --sig_cnt_out                           false
% 3.99/1.02  --trig_cnt_out                          false
% 3.99/1.02  --trig_cnt_out_tolerance                1.
% 3.99/1.02  --trig_cnt_out_sk_spl                   false
% 3.99/1.02  --abstr_cl_out                          false
% 3.99/1.02  
% 3.99/1.02  ------ Global Options
% 3.99/1.02  
% 3.99/1.02  --schedule                              default
% 3.99/1.02  --add_important_lit                     false
% 3.99/1.02  --prop_solver_per_cl                    1000
% 3.99/1.02  --min_unsat_core                        false
% 3.99/1.02  --soft_assumptions                      false
% 3.99/1.02  --soft_lemma_size                       3
% 3.99/1.02  --prop_impl_unit_size                   0
% 3.99/1.02  --prop_impl_unit                        []
% 3.99/1.02  --share_sel_clauses                     true
% 3.99/1.02  --reset_solvers                         false
% 3.99/1.02  --bc_imp_inh                            [conj_cone]
% 3.99/1.02  --conj_cone_tolerance                   3.
% 3.99/1.02  --extra_neg_conj                        none
% 3.99/1.02  --large_theory_mode                     true
% 3.99/1.02  --prolific_symb_bound                   200
% 3.99/1.02  --lt_threshold                          2000
% 3.99/1.02  --clause_weak_htbl                      true
% 3.99/1.02  --gc_record_bc_elim                     false
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing Options
% 3.99/1.02  
% 3.99/1.02  --preprocessing_flag                    true
% 3.99/1.02  --time_out_prep_mult                    0.1
% 3.99/1.02  --splitting_mode                        input
% 3.99/1.02  --splitting_grd                         true
% 3.99/1.02  --splitting_cvd                         false
% 3.99/1.02  --splitting_cvd_svl                     false
% 3.99/1.02  --splitting_nvd                         32
% 3.99/1.02  --sub_typing                            true
% 3.99/1.02  --prep_gs_sim                           true
% 3.99/1.02  --prep_unflatten                        true
% 3.99/1.02  --prep_res_sim                          true
% 3.99/1.02  --prep_upred                            true
% 3.99/1.02  --prep_sem_filter                       exhaustive
% 3.99/1.02  --prep_sem_filter_out                   false
% 3.99/1.02  --pred_elim                             true
% 3.99/1.02  --res_sim_input                         true
% 3.99/1.02  --eq_ax_congr_red                       true
% 3.99/1.02  --pure_diseq_elim                       true
% 3.99/1.02  --brand_transform                       false
% 3.99/1.02  --non_eq_to_eq                          false
% 3.99/1.02  --prep_def_merge                        true
% 3.99/1.02  --prep_def_merge_prop_impl              false
% 3.99/1.02  --prep_def_merge_mbd                    true
% 3.99/1.02  --prep_def_merge_tr_red                 false
% 3.99/1.02  --prep_def_merge_tr_cl                  false
% 3.99/1.02  --smt_preprocessing                     true
% 3.99/1.02  --smt_ac_axioms                         fast
% 3.99/1.02  --preprocessed_out                      false
% 3.99/1.02  --preprocessed_stats                    false
% 3.99/1.02  
% 3.99/1.02  ------ Abstraction refinement Options
% 3.99/1.02  
% 3.99/1.02  --abstr_ref                             []
% 3.99/1.02  --abstr_ref_prep                        false
% 3.99/1.02  --abstr_ref_until_sat                   false
% 3.99/1.02  --abstr_ref_sig_restrict                funpre
% 3.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.99/1.02  --abstr_ref_under                       []
% 3.99/1.02  
% 3.99/1.02  ------ SAT Options
% 3.99/1.02  
% 3.99/1.02  --sat_mode                              false
% 3.99/1.02  --sat_fm_restart_options                ""
% 3.99/1.02  --sat_gr_def                            false
% 3.99/1.02  --sat_epr_types                         true
% 3.99/1.02  --sat_non_cyclic_types                  false
% 3.99/1.02  --sat_finite_models                     false
% 3.99/1.02  --sat_fm_lemmas                         false
% 3.99/1.02  --sat_fm_prep                           false
% 3.99/1.02  --sat_fm_uc_incr                        true
% 3.99/1.02  --sat_out_model                         small
% 3.99/1.02  --sat_out_clauses                       false
% 3.99/1.02  
% 3.99/1.02  ------ QBF Options
% 3.99/1.02  
% 3.99/1.02  --qbf_mode                              false
% 3.99/1.02  --qbf_elim_univ                         false
% 3.99/1.02  --qbf_dom_inst                          none
% 3.99/1.02  --qbf_dom_pre_inst                      false
% 3.99/1.02  --qbf_sk_in                             false
% 3.99/1.02  --qbf_pred_elim                         true
% 3.99/1.02  --qbf_split                             512
% 3.99/1.02  
% 3.99/1.02  ------ BMC1 Options
% 3.99/1.02  
% 3.99/1.02  --bmc1_incremental                      false
% 3.99/1.02  --bmc1_axioms                           reachable_all
% 3.99/1.02  --bmc1_min_bound                        0
% 3.99/1.02  --bmc1_max_bound                        -1
% 3.99/1.02  --bmc1_max_bound_default                -1
% 3.99/1.02  --bmc1_symbol_reachability              true
% 3.99/1.02  --bmc1_property_lemmas                  false
% 3.99/1.02  --bmc1_k_induction                      false
% 3.99/1.02  --bmc1_non_equiv_states                 false
% 3.99/1.02  --bmc1_deadlock                         false
% 3.99/1.02  --bmc1_ucm                              false
% 3.99/1.02  --bmc1_add_unsat_core                   none
% 3.99/1.02  --bmc1_unsat_core_children              false
% 3.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.99/1.02  --bmc1_out_stat                         full
% 3.99/1.02  --bmc1_ground_init                      false
% 3.99/1.02  --bmc1_pre_inst_next_state              false
% 3.99/1.02  --bmc1_pre_inst_state                   false
% 3.99/1.02  --bmc1_pre_inst_reach_state             false
% 3.99/1.02  --bmc1_out_unsat_core                   false
% 3.99/1.02  --bmc1_aig_witness_out                  false
% 3.99/1.02  --bmc1_verbose                          false
% 3.99/1.02  --bmc1_dump_clauses_tptp                false
% 3.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.99/1.02  --bmc1_dump_file                        -
% 3.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.99/1.02  --bmc1_ucm_extend_mode                  1
% 3.99/1.02  --bmc1_ucm_init_mode                    2
% 3.99/1.02  --bmc1_ucm_cone_mode                    none
% 3.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.99/1.02  --bmc1_ucm_relax_model                  4
% 3.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.99/1.02  --bmc1_ucm_layered_model                none
% 3.99/1.02  --bmc1_ucm_max_lemma_size               10
% 3.99/1.02  
% 3.99/1.02  ------ AIG Options
% 3.99/1.02  
% 3.99/1.02  --aig_mode                              false
% 3.99/1.02  
% 3.99/1.02  ------ Instantiation Options
% 3.99/1.02  
% 3.99/1.02  --instantiation_flag                    true
% 3.99/1.02  --inst_sos_flag                         true
% 3.99/1.02  --inst_sos_phase                        true
% 3.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.99/1.02  --inst_lit_sel_side                     none
% 3.99/1.02  --inst_solver_per_active                1400
% 3.99/1.02  --inst_solver_calls_frac                1.
% 3.99/1.02  --inst_passive_queue_type               priority_queues
% 3.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.99/1.02  --inst_passive_queues_freq              [25;2]
% 3.99/1.02  --inst_dismatching                      true
% 3.99/1.02  --inst_eager_unprocessed_to_passive     true
% 3.99/1.02  --inst_prop_sim_given                   true
% 3.99/1.02  --inst_prop_sim_new                     false
% 3.99/1.02  --inst_subs_new                         false
% 3.99/1.02  --inst_eq_res_simp                      false
% 3.99/1.02  --inst_subs_given                       false
% 3.99/1.02  --inst_orphan_elimination               true
% 3.99/1.02  --inst_learning_loop_flag               true
% 3.99/1.02  --inst_learning_start                   3000
% 3.99/1.02  --inst_learning_factor                  2
% 3.99/1.02  --inst_start_prop_sim_after_learn       3
% 3.99/1.02  --inst_sel_renew                        solver
% 3.99/1.02  --inst_lit_activity_flag                true
% 3.99/1.02  --inst_restr_to_given                   false
% 3.99/1.02  --inst_activity_threshold               500
% 3.99/1.02  --inst_out_proof                        true
% 3.99/1.02  
% 3.99/1.02  ------ Resolution Options
% 3.99/1.02  
% 3.99/1.02  --resolution_flag                       false
% 3.99/1.02  --res_lit_sel                           adaptive
% 3.99/1.02  --res_lit_sel_side                      none
% 3.99/1.02  --res_ordering                          kbo
% 3.99/1.02  --res_to_prop_solver                    active
% 3.99/1.02  --res_prop_simpl_new                    false
% 3.99/1.02  --res_prop_simpl_given                  true
% 3.99/1.02  --res_passive_queue_type                priority_queues
% 3.99/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.99/1.02  --res_passive_queues_freq               [15;5]
% 3.99/1.02  --res_forward_subs                      full
% 3.99/1.02  --res_backward_subs                     full
% 3.99/1.02  --res_forward_subs_resolution           true
% 3.99/1.02  --res_backward_subs_resolution          true
% 3.99/1.02  --res_orphan_elimination                true
% 3.99/1.02  --res_time_limit                        2.
% 3.99/1.02  --res_out_proof                         true
% 3.99/1.02  
% 3.99/1.02  ------ Superposition Options
% 3.99/1.02  
% 3.99/1.02  --superposition_flag                    true
% 3.99/1.02  --sup_passive_queue_type                priority_queues
% 3.99/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.99/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.99/1.02  --demod_completeness_check              fast
% 3.99/1.02  --demod_use_ground                      true
% 3.99/1.02  --sup_to_prop_solver                    passive
% 3.99/1.02  --sup_prop_simpl_new                    true
% 3.99/1.02  --sup_prop_simpl_given                  true
% 3.99/1.02  --sup_fun_splitting                     true
% 3.99/1.02  --sup_smt_interval                      50000
% 3.99/1.02  
% 3.99/1.02  ------ Superposition Simplification Setup
% 3.99/1.02  
% 3.99/1.02  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.99/1.02  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.99/1.02  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.99/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.99/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.99/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.99/1.02  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.99/1.02  --sup_immed_triv                        [TrivRules]
% 3.99/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_immed_bw_main                     []
% 3.99/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.99/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.99/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.99/1.02  --sup_input_bw                          []
% 3.99/1.02  
% 3.99/1.02  ------ Combination Options
% 3.99/1.02  
% 3.99/1.02  --comb_res_mult                         3
% 3.99/1.02  --comb_sup_mult                         2
% 3.99/1.02  --comb_inst_mult                        10
% 3.99/1.02  
% 3.99/1.02  ------ Debug Options
% 3.99/1.02  
% 3.99/1.02  --dbg_backtrace                         false
% 3.99/1.02  --dbg_dump_prop_clauses                 false
% 3.99/1.02  --dbg_dump_prop_clauses_file            -
% 3.99/1.02  --dbg_out_stat                          false
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  ------ Proving...
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  % SZS status Theorem for theBenchmark.p
% 3.99/1.02  
% 3.99/1.02   Resolution empty clause
% 3.99/1.02  
% 3.99/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.99/1.02  
% 3.99/1.02  fof(f1,axiom,(
% 3.99/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f36,plain,(
% 3.99/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.99/1.02    inference(nnf_transformation,[],[f1])).
% 3.99/1.02  
% 3.99/1.02  fof(f37,plain,(
% 3.99/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.99/1.02    inference(rectify,[],[f36])).
% 3.99/1.02  
% 3.99/1.02  fof(f38,plain,(
% 3.99/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f39,plain,(
% 3.99/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.99/1.02  
% 3.99/1.02  fof(f58,plain,(
% 3.99/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f39])).
% 3.99/1.02  
% 3.99/1.02  fof(f13,axiom,(
% 3.99/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f18,plain,(
% 3.99/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.99/1.02    inference(pure_predicate_removal,[],[f13])).
% 3.99/1.02  
% 3.99/1.02  fof(f19,plain,(
% 3.99/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.99/1.02    inference(pure_predicate_removal,[],[f18])).
% 3.99/1.02  
% 3.99/1.02  fof(f28,plain,(
% 3.99/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f19])).
% 3.99/1.02  
% 3.99/1.02  fof(f29,plain,(
% 3.99/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.99/1.02    inference(flattening,[],[f28])).
% 3.99/1.02  
% 3.99/1.02  fof(f47,plain,(
% 3.99/1.02    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f48,plain,(
% 3.99/1.02    ! [X0] : ((~v1_xboole_0(sK3(X0)) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f29,f47])).
% 3.99/1.02  
% 3.99/1.02  fof(f73,plain,(
% 3.99/1.02    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f48])).
% 3.99/1.02  
% 3.99/1.02  fof(f16,conjecture,(
% 3.99/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f17,negated_conjecture,(
% 3.99/1.02    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 3.99/1.02    inference(negated_conjecture,[],[f16])).
% 3.99/1.02  
% 3.99/1.02  fof(f34,plain,(
% 3.99/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f17])).
% 3.99/1.02  
% 3.99/1.02  fof(f35,plain,(
% 3.99/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.99/1.02    inference(flattening,[],[f34])).
% 3.99/1.02  
% 3.99/1.02  fof(f55,plain,(
% 3.99/1.02    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK6,X0) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK6))) )),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f54,plain,(
% 3.99/1.02    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK5) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) & v1_xboole_0(X1)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5))),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f56,plain,(
% 3.99/1.02    (v3_tex_2(sK6,sK5) & m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) & v1_xboole_0(sK6)) & l1_pre_topc(sK5) & v2_pre_topc(sK5) & ~v2_struct_0(sK5)),
% 3.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f35,f55,f54])).
% 3.99/1.02  
% 3.99/1.02  fof(f83,plain,(
% 3.99/1.02    v2_pre_topc(sK5)),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f82,plain,(
% 3.99/1.02    ~v2_struct_0(sK5)),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f84,plain,(
% 3.99/1.02    l1_pre_topc(sK5)),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f10,axiom,(
% 3.99/1.02    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f22,plain,(
% 3.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.99/1.02    inference(ennf_transformation,[],[f10])).
% 3.99/1.02  
% 3.99/1.02  fof(f23,plain,(
% 3.99/1.02    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.99/1.02    inference(flattening,[],[f22])).
% 3.99/1.02  
% 3.99/1.02  fof(f70,plain,(
% 3.99/1.02    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f23])).
% 3.99/1.02  
% 3.99/1.02  fof(f74,plain,(
% 3.99/1.02    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f48])).
% 3.99/1.02  
% 3.99/1.02  fof(f12,axiom,(
% 3.99/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f26,plain,(
% 3.99/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f12])).
% 3.99/1.02  
% 3.99/1.02  fof(f27,plain,(
% 3.99/1.02    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.99/1.02    inference(flattening,[],[f26])).
% 3.99/1.02  
% 3.99/1.02  fof(f72,plain,(
% 3.99/1.02    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f27])).
% 3.99/1.02  
% 3.99/1.02  fof(f9,axiom,(
% 3.99/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f46,plain,(
% 3.99/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.99/1.02    inference(nnf_transformation,[],[f9])).
% 3.99/1.02  
% 3.99/1.02  fof(f68,plain,(
% 3.99/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.99/1.02    inference(cnf_transformation,[],[f46])).
% 3.99/1.02  
% 3.99/1.02  fof(f2,axiom,(
% 3.99/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f20,plain,(
% 3.99/1.02    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f2])).
% 3.99/1.02  
% 3.99/1.02  fof(f40,plain,(
% 3.99/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.99/1.02    inference(nnf_transformation,[],[f20])).
% 3.99/1.02  
% 3.99/1.02  fof(f41,plain,(
% 3.99/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.99/1.02    inference(rectify,[],[f40])).
% 3.99/1.02  
% 3.99/1.02  fof(f42,plain,(
% 3.99/1.02    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f43,plain,(
% 3.99/1.02    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.99/1.02  
% 3.99/1.02  fof(f59,plain,(
% 3.99/1.02    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f43])).
% 3.99/1.02  
% 3.99/1.02  fof(f57,plain,(
% 3.99/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f39])).
% 3.99/1.02  
% 3.99/1.02  fof(f11,axiom,(
% 3.99/1.02    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f24,plain,(
% 3.99/1.02    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f11])).
% 3.99/1.02  
% 3.99/1.02  fof(f25,plain,(
% 3.99/1.02    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 3.99/1.02    inference(flattening,[],[f24])).
% 3.99/1.02  
% 3.99/1.02  fof(f71,plain,(
% 3.99/1.02    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f25])).
% 3.99/1.02  
% 3.99/1.02  fof(f85,plain,(
% 3.99/1.02    v1_xboole_0(sK6)),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f3,axiom,(
% 3.99/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f21,plain,(
% 3.99/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.99/1.02    inference(ennf_transformation,[],[f3])).
% 3.99/1.02  
% 3.99/1.02  fof(f62,plain,(
% 3.99/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f21])).
% 3.99/1.02  
% 3.99/1.02  fof(f86,plain,(
% 3.99/1.02    m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5)))),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f14,axiom,(
% 3.99/1.02    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f30,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(ennf_transformation,[],[f14])).
% 3.99/1.02  
% 3.99/1.02  fof(f31,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(flattening,[],[f30])).
% 3.99/1.02  
% 3.99/1.02  fof(f49,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(nnf_transformation,[],[f31])).
% 3.99/1.02  
% 3.99/1.02  fof(f50,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(flattening,[],[f49])).
% 3.99/1.02  
% 3.99/1.02  fof(f51,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(rectify,[],[f50])).
% 3.99/1.02  
% 3.99/1.02  fof(f52,plain,(
% 3.99/1.02    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) != X1 & r1_tarski(X1,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.99/1.02    introduced(choice_axiom,[])).
% 3.99/1.02  
% 3.99/1.02  fof(f53,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK4(X0,X1) != X1 & r1_tarski(X1,sK4(X0,X1)) & v2_tex_2(sK4(X0,X1),X0) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.99/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f51,f52])).
% 3.99/1.02  
% 3.99/1.02  fof(f76,plain,(
% 3.99/1.02    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f53])).
% 3.99/1.02  
% 3.99/1.02  fof(f87,plain,(
% 3.99/1.02    v3_tex_2(sK6,sK5)),
% 3.99/1.02    inference(cnf_transformation,[],[f56])).
% 3.99/1.02  
% 3.99/1.02  fof(f5,axiom,(
% 3.99/1.02    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f64,plain,(
% 3.99/1.02    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f5])).
% 3.99/1.02  
% 3.99/1.02  fof(f8,axiom,(
% 3.99/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f67,plain,(
% 3.99/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.99/1.02    inference(cnf_transformation,[],[f8])).
% 3.99/1.02  
% 3.99/1.02  fof(f15,axiom,(
% 3.99/1.02    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f32,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.99/1.02    inference(ennf_transformation,[],[f15])).
% 3.99/1.02  
% 3.99/1.02  fof(f33,plain,(
% 3.99/1.02    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.99/1.02    inference(flattening,[],[f32])).
% 3.99/1.02  
% 3.99/1.02  fof(f81,plain,(
% 3.99/1.02    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f33])).
% 3.99/1.02  
% 3.99/1.02  fof(f4,axiom,(
% 3.99/1.02    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f63,plain,(
% 3.99/1.02    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.99/1.02    inference(cnf_transformation,[],[f4])).
% 3.99/1.02  
% 3.99/1.02  fof(f6,axiom,(
% 3.99/1.02    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 3.99/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.99/1.02  
% 3.99/1.02  fof(f65,plain,(
% 3.99/1.02    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 3.99/1.02    inference(cnf_transformation,[],[f6])).
% 3.99/1.02  
% 3.99/1.02  cnf(c_0,plain,
% 3.99/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.99/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2561,plain,
% 3.99/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top | v1_xboole_0(X0) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_17,plain,
% 3.99/1.02      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.99/1.02      | v2_struct_0(X0)
% 3.99/1.02      | ~ v2_pre_topc(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0) ),
% 3.99/1.02      inference(cnf_transformation,[],[f73]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_29,negated_conjecture,
% 3.99/1.02      ( v2_pre_topc(sK5) ),
% 3.99/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_405,plain,
% 3.99/1.02      ( m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 3.99/1.02      | v2_struct_0(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0)
% 3.99/1.02      | sK5 != X0 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_406,plain,
% 3.99/1.02      ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | v2_struct_0(sK5)
% 3.99/1.02      | ~ l1_pre_topc(sK5) ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_405]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_30,negated_conjecture,
% 3.99/1.02      ( ~ v2_struct_0(sK5) ),
% 3.99/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_28,negated_conjecture,
% 3.99/1.02      ( l1_pre_topc(sK5) ),
% 3.99/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_408,plain,
% 3.99/1.02      ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_406,c_30,c_28]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2543,plain,
% 3.99/1.02      ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_13,plain,
% 3.99/1.02      ( m1_subset_1(X0,X1)
% 3.99/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.99/1.02      | ~ r2_hidden(X0,X2) ),
% 3.99/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2550,plain,
% 3.99/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 3.99/1.02      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.99/1.02      | r2_hidden(X0,X2) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4354,plain,
% 3.99/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) = iProver_top
% 3.99/1.02      | r2_hidden(X0,sK3(sK5)) != iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2543,c_2550]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4559,plain,
% 3.99/1.02      ( m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
% 3.99/1.02      | v1_xboole_0(sK3(sK5)) = iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2561,c_4354]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_31,plain,
% 3.99/1.02      ( v2_struct_0(sK5) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_33,plain,
% 3.99/1.02      ( l1_pre_topc(sK5) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_407,plain,
% 3.99/1.02      ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top
% 3.99/1.02      | v2_struct_0(sK5) = iProver_top
% 3.99/1.02      | l1_pre_topc(sK5) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_406]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_16,plain,
% 3.99/1.02      ( v2_struct_0(X0)
% 3.99/1.02      | ~ v2_pre_topc(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0)
% 3.99/1.02      | ~ v1_xboole_0(sK3(X0)) ),
% 3.99/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_416,plain,
% 3.99/1.02      ( v2_struct_0(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0)
% 3.99/1.02      | ~ v1_xboole_0(sK3(X0))
% 3.99/1.02      | sK5 != X0 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_417,plain,
% 3.99/1.02      ( v2_struct_0(sK5) | ~ l1_pre_topc(sK5) | ~ v1_xboole_0(sK3(sK5)) ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_416]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_419,plain,
% 3.99/1.02      ( ~ v1_xboole_0(sK3(sK5)) ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_417,c_30,c_28]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_520,plain,
% 3.99/1.02      ( r2_hidden(sK0(X0),X0) | sK3(sK5) != X0 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_419]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_521,plain,
% 3.99/1.02      ( r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_520]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_522,plain,
% 3.99/1.02      ( r2_hidden(sK0(sK3(sK5)),sK3(sK5)) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_521]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2620,plain,
% 3.99/1.02      ( m1_subset_1(X0,u1_struct_0(sK5))
% 3.99/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | ~ r2_hidden(X0,X1) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2708,plain,
% 3.99/1.02      ( m1_subset_1(X0,u1_struct_0(sK5))
% 3.99/1.02      | ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | ~ r2_hidden(X0,sK3(sK5)) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_2620]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2842,plain,
% 3.99/1.02      ( ~ m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5))
% 3.99/1.02      | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_2708]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2843,plain,
% 3.99/1.02      ( m1_subset_1(sK3(sK5),k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
% 3.99/1.02      | r2_hidden(sK0(sK3(sK5)),sK3(sK5)) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_2842]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_6325,plain,
% 3.99/1.02      ( m1_subset_1(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_4559,c_31,c_33,c_407,c_522,c_2843]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_15,plain,
% 3.99/1.02      ( ~ m1_subset_1(X0,X1)
% 3.99/1.02      | v1_xboole_0(X1)
% 3.99/1.02      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 3.99/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2548,plain,
% 3.99/1.02      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 3.99/1.02      | m1_subset_1(X1,X0) != iProver_top
% 3.99/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_6329,plain,
% 3.99/1.02      ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_tarski(sK0(sK3(sK5)))
% 3.99/1.02      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_6325,c_2548]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_12,plain,
% 3.99/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.99/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2551,plain,
% 3.99/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.99/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3916,plain,
% 3.99/1.02      ( r1_tarski(sK3(sK5),u1_struct_0(sK5)) = iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2543,c_2551]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4,plain,
% 3.99/1.02      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.99/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3164,plain,
% 3.99/1.02      ( ~ r1_tarski(sK3(sK5),X0)
% 3.99/1.02      | r2_hidden(sK0(sK3(sK5)),X0)
% 3.99/1.02      | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_4]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4127,plain,
% 3.99/1.02      ( ~ r1_tarski(sK3(sK5),u1_struct_0(sK5))
% 3.99/1.02      | r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5))
% 3.99/1.02      | ~ r2_hidden(sK0(sK3(sK5)),sK3(sK5)) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_3164]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4131,plain,
% 3.99/1.02      ( r1_tarski(sK3(sK5),u1_struct_0(sK5)) != iProver_top
% 3.99/1.02      | r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5)) = iProver_top
% 3.99/1.02      | r2_hidden(sK0(sK3(sK5)),sK3(sK5)) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_4127]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_1,plain,
% 3.99/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.99/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_6314,plain,
% 3.99/1.02      ( ~ r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5))
% 3.99/1.02      | ~ v1_xboole_0(u1_struct_0(sK5)) ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_1]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_6315,plain,
% 3.99/1.02      ( r2_hidden(sK0(sK3(sK5)),u1_struct_0(sK5)) != iProver_top
% 3.99/1.02      | v1_xboole_0(u1_struct_0(sK5)) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_6314]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_9211,plain,
% 3.99/1.02      ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_tarski(sK0(sK3(sK5))) ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_6329,c_522,c_3916,c_4131,c_6315]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_14,plain,
% 3.99/1.02      ( ~ m1_subset_1(X0,X1)
% 3.99/1.02      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 3.99/1.02      | v1_xboole_0(X1) ),
% 3.99/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2549,plain,
% 3.99/1.02      ( m1_subset_1(X0,X1) != iProver_top
% 3.99/1.02      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 3.99/1.02      | v1_xboole_0(X1) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_27,negated_conjecture,
% 3.99/1.02      ( v1_xboole_0(sK6) ),
% 3.99/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2545,plain,
% 3.99/1.02      ( v1_xboole_0(sK6) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_5,plain,
% 3.99/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.99/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2556,plain,
% 3.99/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3532,plain,
% 3.99/1.02      ( sK6 = k1_xboole_0 ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2545,c_2556]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_26,negated_conjecture,
% 3.99/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) ),
% 3.99/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2546,plain,
% 3.99/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(u1_struct_0(sK5))) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_22,plain,
% 3.99/1.02      ( ~ v2_tex_2(X0,X1)
% 3.99/1.02      | ~ v3_tex_2(X2,X1)
% 3.99/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.99/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.99/1.02      | ~ r1_tarski(X2,X0)
% 3.99/1.02      | ~ l1_pre_topc(X1)
% 3.99/1.02      | X0 = X2 ),
% 3.99/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_603,plain,
% 3.99/1.02      ( ~ v2_tex_2(X0,X1)
% 3.99/1.02      | ~ v3_tex_2(X2,X1)
% 3.99/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.99/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.99/1.02      | ~ r1_tarski(X2,X0)
% 3.99/1.02      | X2 = X0
% 3.99/1.02      | sK5 != X1 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_604,plain,
% 3.99/1.02      ( ~ v2_tex_2(X0,sK5)
% 3.99/1.02      | ~ v3_tex_2(X1,sK5)
% 3.99/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5)))
% 3.99/1.02      | ~ r1_tarski(X1,X0)
% 3.99/1.02      | X1 = X0 ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_603]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2540,plain,
% 3.99/1.02      ( X0 = X1
% 3.99/1.02      | v2_tex_2(X1,sK5) != iProver_top
% 3.99/1.02      | v3_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(X0,X1) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3100,plain,
% 3.99/1.02      ( sK6 = X0
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | v3_tex_2(sK6,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(sK6,X0) != iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2546,c_2540]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_25,negated_conjecture,
% 3.99/1.02      ( v3_tex_2(sK6,sK5) ),
% 3.99/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_36,plain,
% 3.99/1.02      ( v3_tex_2(sK6,sK5) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3150,plain,
% 3.99/1.02      ( v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | sK6 = X0
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(sK6,X0) != iProver_top ),
% 3.99/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3100,c_36]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3151,plain,
% 3.99/1.02      ( sK6 = X0
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(sK6,X0) != iProver_top ),
% 3.99/1.02      inference(renaming,[status(thm)],[c_3150]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3630,plain,
% 3.99/1.02      ( k1_xboole_0 = X0
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.99/1.02      inference(demodulation,[status(thm)],[c_3532,c_3151]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_7,plain,
% 3.99/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 3.99/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_86,plain,
% 3.99/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_515,plain,
% 3.99/1.02      ( sK6 != X0 | k1_xboole_0 = X0 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_5,c_27]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_516,plain,
% 3.99/1.02      ( k1_xboole_0 = sK6 ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_515]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_1925,plain,( X0 = X0 ),theory(equality) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2992,plain,
% 3.99/1.02      ( sK5 = sK5 ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_1925]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_1936,plain,
% 3.99/1.02      ( ~ v3_tex_2(X0,X1) | v3_tex_2(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.99/1.02      theory(equality) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2633,plain,
% 3.99/1.02      ( ~ v3_tex_2(X0,X1) | v3_tex_2(X2,sK5) | X2 != X0 | sK5 != X1 ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_1936]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2780,plain,
% 3.99/1.02      ( ~ v3_tex_2(X0,sK5) | v3_tex_2(X1,sK5) | X1 != X0 | sK5 != sK5 ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_2633]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3189,plain,
% 3.99/1.02      ( v3_tex_2(X0,sK5) | ~ v3_tex_2(sK6,sK5) | X0 != sK6 | sK5 != sK5 ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_2780]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3190,plain,
% 3.99/1.02      ( X0 != sK6
% 3.99/1.02      | sK5 != sK5
% 3.99/1.02      | v3_tex_2(X0,sK5) = iProver_top
% 3.99/1.02      | v3_tex_2(sK6,sK5) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_3189]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3192,plain,
% 3.99/1.02      ( sK5 != sK5
% 3.99/1.02      | k1_xboole_0 != sK6
% 3.99/1.02      | v3_tex_2(sK6,sK5) != iProver_top
% 3.99/1.02      | v3_tex_2(k1_xboole_0,sK5) = iProver_top ),
% 3.99/1.02      inference(instantiation,[status(thm)],[c_3190]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_10,plain,
% 3.99/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.99/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_2553,plain,
% 3.99/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3460,plain,
% 3.99/1.02      ( k1_xboole_0 = X0
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | v3_tex_2(k1_xboole_0,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2553,c_2540]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4328,plain,
% 3.99/1.02      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | k1_xboole_0 = X0 ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_3630,c_36,c_86,c_516,c_2992,c_3192,c_3460]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4329,plain,
% 3.99/1.02      ( k1_xboole_0 = X0
% 3.99/1.02      | v2_tex_2(X0,sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK5))) != iProver_top ),
% 3.99/1.02      inference(renaming,[status(thm)],[c_4328]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_4335,plain,
% 3.99/1.02      ( k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0
% 3.99/1.02      | v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5) != iProver_top
% 3.99/1.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.99/1.02      | v1_xboole_0(u1_struct_0(sK5)) = iProver_top ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_2549,c_4329]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_24,plain,
% 3.99/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.99/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.99/1.02      | v2_struct_0(X0)
% 3.99/1.02      | ~ v2_pre_topc(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0) ),
% 3.99/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_387,plain,
% 3.99/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 3.99/1.02      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 3.99/1.02      | v2_struct_0(X0)
% 3.99/1.02      | ~ l1_pre_topc(X0)
% 3.99/1.02      | sK5 != X0 ),
% 3.99/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_388,plain,
% 3.99/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5)
% 3.99/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK5))
% 3.99/1.02      | v2_struct_0(sK5)
% 3.99/1.02      | ~ l1_pre_topc(sK5) ),
% 3.99/1.02      inference(unflattening,[status(thm)],[c_387]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_392,plain,
% 3.99/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5)
% 3.99/1.02      | ~ m1_subset_1(X0,u1_struct_0(sK5)) ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_388,c_30,c_28]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_394,plain,
% 3.99/1.02      ( v2_tex_2(k6_domain_1(u1_struct_0(sK5),X0),sK5) = iProver_top
% 3.99/1.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.99/1.02      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_8510,plain,
% 3.99/1.02      ( m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top
% 3.99/1.02      | k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0 ),
% 3.99/1.02      inference(global_propositional_subsumption,
% 3.99/1.02                [status(thm)],
% 3.99/1.02                [c_4335,c_394,c_522,c_3916,c_4131,c_6315]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_8511,plain,
% 3.99/1.02      ( k6_domain_1(u1_struct_0(sK5),X0) = k1_xboole_0
% 3.99/1.02      | m1_subset_1(X0,u1_struct_0(sK5)) != iProver_top ),
% 3.99/1.02      inference(renaming,[status(thm)],[c_8510]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_8517,plain,
% 3.99/1.02      ( k6_domain_1(u1_struct_0(sK5),sK0(sK3(sK5))) = k1_xboole_0 ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_6325,c_8511]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_9213,plain,
% 3.99/1.02      ( k1_tarski(sK0(sK3(sK5))) = k1_xboole_0 ),
% 3.99/1.02      inference(light_normalisation,[status(thm)],[c_9211,c_8517]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_6,plain,
% 3.99/1.02      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.99/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_8,plain,
% 3.99/1.02      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 3.99/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_3032,plain,
% 3.99/1.02      ( k1_tarski(X0) != k1_xboole_0 ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_6,c_8]) ).
% 3.99/1.02  
% 3.99/1.02  cnf(c_9214,plain,
% 3.99/1.02      ( $false ),
% 3.99/1.02      inference(superposition,[status(thm)],[c_9213,c_3032]) ).
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.99/1.02  
% 3.99/1.02  ------                               Statistics
% 3.99/1.02  
% 3.99/1.02  ------ General
% 3.99/1.02  
% 3.99/1.02  abstr_ref_over_cycles:                  0
% 3.99/1.02  abstr_ref_under_cycles:                 0
% 3.99/1.02  gc_basic_clause_elim:                   0
% 3.99/1.02  forced_gc_time:                         0
% 3.99/1.02  parsing_time:                           0.009
% 3.99/1.02  unif_index_cands_time:                  0.
% 3.99/1.02  unif_index_add_time:                    0.
% 3.99/1.02  orderings_time:                         0.
% 3.99/1.02  out_proof_time:                         0.01
% 3.99/1.02  total_time:                             0.299
% 3.99/1.02  num_of_symbols:                         53
% 3.99/1.02  num_of_terms:                           6576
% 3.99/1.02  
% 3.99/1.02  ------ Preprocessing
% 3.99/1.02  
% 3.99/1.02  num_of_splits:                          0
% 3.99/1.02  num_of_split_atoms:                     0
% 3.99/1.02  num_of_reused_defs:                     0
% 3.99/1.02  num_eq_ax_congr_red:                    27
% 3.99/1.02  num_of_sem_filtered_clauses:            1
% 3.99/1.02  num_of_subtypes:                        0
% 3.99/1.02  monotx_restored_types:                  0
% 3.99/1.02  sat_num_of_epr_types:                   0
% 3.99/1.02  sat_num_of_non_cyclic_types:            0
% 3.99/1.02  sat_guarded_non_collapsed_types:        0
% 3.99/1.02  num_pure_diseq_elim:                    0
% 3.99/1.02  simp_replaced_by:                       0
% 3.99/1.02  res_preprocessed:                       144
% 3.99/1.02  prep_upred:                             0
% 3.99/1.02  prep_unflattend:                        73
% 3.99/1.02  smt_new_axioms:                         0
% 3.99/1.02  pred_elim_cands:                        6
% 3.99/1.02  pred_elim:                              3
% 3.99/1.02  pred_elim_cl:                           3
% 3.99/1.02  pred_elim_cycles:                       9
% 3.99/1.02  merged_defs:                            8
% 3.99/1.02  merged_defs_ncl:                        0
% 3.99/1.02  bin_hyper_res:                          8
% 3.99/1.02  prep_cycles:                            4
% 3.99/1.02  pred_elim_time:                         0.023
% 3.99/1.02  splitting_time:                         0.
% 3.99/1.02  sem_filter_time:                        0.
% 3.99/1.02  monotx_time:                            0.001
% 3.99/1.02  subtype_inf_time:                       0.
% 3.99/1.02  
% 3.99/1.02  ------ Problem properties
% 3.99/1.02  
% 3.99/1.02  clauses:                                28
% 3.99/1.02  conjectures:                            3
% 3.99/1.02  epr:                                    6
% 3.99/1.02  horn:                                   21
% 3.99/1.02  ground:                                 5
% 3.99/1.02  unary:                                  10
% 3.99/1.02  binary:                                 8
% 3.99/1.02  lits:                                   63
% 3.99/1.02  lits_eq:                                6
% 3.99/1.02  fd_pure:                                0
% 3.99/1.02  fd_pseudo:                              0
% 3.99/1.02  fd_cond:                                1
% 3.99/1.02  fd_pseudo_cond:                         1
% 3.99/1.02  ac_symbols:                             0
% 3.99/1.02  
% 3.99/1.02  ------ Propositional Solver
% 3.99/1.02  
% 3.99/1.02  prop_solver_calls:                      31
% 3.99/1.02  prop_fast_solver_calls:                 1589
% 3.99/1.02  smt_solver_calls:                       0
% 3.99/1.02  smt_fast_solver_calls:                  0
% 3.99/1.02  prop_num_of_clauses:                    3628
% 3.99/1.02  prop_preprocess_simplified:             8503
% 3.99/1.02  prop_fo_subsumed:                       74
% 3.99/1.02  prop_solver_time:                       0.
% 3.99/1.02  smt_solver_time:                        0.
% 3.99/1.02  smt_fast_solver_time:                   0.
% 3.99/1.02  prop_fast_solver_time:                  0.
% 3.99/1.02  prop_unsat_core_time:                   0.
% 3.99/1.02  
% 3.99/1.02  ------ QBF
% 3.99/1.02  
% 3.99/1.02  qbf_q_res:                              0
% 3.99/1.02  qbf_num_tautologies:                    0
% 3.99/1.02  qbf_prep_cycles:                        0
% 3.99/1.02  
% 3.99/1.02  ------ BMC1
% 3.99/1.02  
% 3.99/1.02  bmc1_current_bound:                     -1
% 3.99/1.02  bmc1_last_solved_bound:                 -1
% 3.99/1.02  bmc1_unsat_core_size:                   -1
% 3.99/1.02  bmc1_unsat_core_parents_size:           -1
% 3.99/1.02  bmc1_merge_next_fun:                    0
% 3.99/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.99/1.02  
% 3.99/1.02  ------ Instantiation
% 3.99/1.02  
% 3.99/1.02  inst_num_of_clauses:                    984
% 3.99/1.02  inst_num_in_passive:                    329
% 3.99/1.02  inst_num_in_active:                     572
% 3.99/1.02  inst_num_in_unprocessed:                83
% 3.99/1.02  inst_num_of_loops:                      690
% 3.99/1.02  inst_num_of_learning_restarts:          0
% 3.99/1.02  inst_num_moves_active_passive:          113
% 3.99/1.02  inst_lit_activity:                      0
% 3.99/1.02  inst_lit_activity_moves:                0
% 3.99/1.02  inst_num_tautologies:                   0
% 3.99/1.02  inst_num_prop_implied:                  0
% 3.99/1.02  inst_num_existing_simplified:           0
% 3.99/1.02  inst_num_eq_res_simplified:             0
% 3.99/1.02  inst_num_child_elim:                    0
% 3.99/1.02  inst_num_of_dismatching_blockings:      322
% 3.99/1.02  inst_num_of_non_proper_insts:           1438
% 3.99/1.02  inst_num_of_duplicates:                 0
% 3.99/1.02  inst_inst_num_from_inst_to_res:         0
% 3.99/1.02  inst_dismatching_checking_time:         0.
% 3.99/1.02  
% 3.99/1.02  ------ Resolution
% 3.99/1.02  
% 3.99/1.02  res_num_of_clauses:                     0
% 3.99/1.02  res_num_in_passive:                     0
% 3.99/1.02  res_num_in_active:                      0
% 3.99/1.02  res_num_of_loops:                       148
% 3.99/1.02  res_forward_subset_subsumed:            118
% 3.99/1.02  res_backward_subset_subsumed:           0
% 3.99/1.02  res_forward_subsumed:                   0
% 3.99/1.02  res_backward_subsumed:                  0
% 3.99/1.02  res_forward_subsumption_resolution:     1
% 3.99/1.02  res_backward_subsumption_resolution:    0
% 3.99/1.02  res_clause_to_clause_subsumption:       920
% 3.99/1.02  res_orphan_elimination:                 0
% 3.99/1.02  res_tautology_del:                      88
% 3.99/1.02  res_num_eq_res_simplified:              0
% 3.99/1.02  res_num_sel_changes:                    0
% 3.99/1.02  res_moves_from_active_to_pass:          0
% 3.99/1.02  
% 3.99/1.02  ------ Superposition
% 3.99/1.02  
% 3.99/1.02  sup_time_total:                         0.
% 3.99/1.02  sup_time_generating:                    0.
% 3.99/1.02  sup_time_sim_full:                      0.
% 3.99/1.02  sup_time_sim_immed:                     0.
% 3.99/1.02  
% 3.99/1.02  sup_num_of_clauses:                     274
% 3.99/1.02  sup_num_in_active:                      128
% 3.99/1.02  sup_num_in_passive:                     146
% 3.99/1.02  sup_num_of_loops:                       137
% 3.99/1.02  sup_fw_superposition:                   192
% 3.99/1.02  sup_bw_superposition:                   166
% 3.99/1.02  sup_immediate_simplified:               61
% 3.99/1.02  sup_given_eliminated:                   0
% 3.99/1.02  comparisons_done:                       0
% 3.99/1.02  comparisons_avoided:                    14
% 3.99/1.02  
% 3.99/1.02  ------ Simplifications
% 3.99/1.02  
% 3.99/1.02  
% 3.99/1.02  sim_fw_subset_subsumed:                 34
% 3.99/1.02  sim_bw_subset_subsumed:                 4
% 3.99/1.02  sim_fw_subsumed:                        27
% 3.99/1.02  sim_bw_subsumed:                        3
% 3.99/1.02  sim_fw_subsumption_res:                 0
% 3.99/1.02  sim_bw_subsumption_res:                 0
% 3.99/1.02  sim_tautology_del:                      7
% 3.99/1.02  sim_eq_tautology_del:                   7
% 3.99/1.02  sim_eq_res_simp:                        0
% 3.99/1.02  sim_fw_demodulated:                     2
% 3.99/1.02  sim_bw_demodulated:                     6
% 3.99/1.02  sim_light_normalised:                   12
% 3.99/1.02  sim_joinable_taut:                      0
% 3.99/1.02  sim_joinable_simp:                      0
% 3.99/1.02  sim_ac_normalised:                      0
% 3.99/1.02  sim_smt_subsumption:                    0
% 3.99/1.02  
%------------------------------------------------------------------------------
