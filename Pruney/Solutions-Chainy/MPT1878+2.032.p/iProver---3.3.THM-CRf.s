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
% DateTime   : Thu Dec  3 12:27:04 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 931 expanded)
%              Number of clauses        :   81 ( 254 expanded)
%              Number of leaves         :   21 ( 247 expanded)
%              Depth                    :   21
%              Number of atoms          :  508 (4271 expanded)
%              Number of equality atoms :  118 ( 299 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4] :
                  ~ ( k3_mcart_1(X2,X3,X4) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4] :
              ( k3_mcart_1(X2,X3,X4) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X4,X3,X2] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4] :
            ( k3_mcart_1(X2,X3,X4) != sK1(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK1(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f39,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f39])).

fof(f60,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v1_xboole_0(X1) )
           => ~ v3_tex_2(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v1_xboole_0(X1) )
     => ( v3_tex_2(sK5,X0)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0)))
        & v1_xboole_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v3_tex_2(X1,sK4)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
          & v1_xboole_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( v3_tex_2(sK5,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))
    & v1_xboole_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f47,f46])).

fof(f72,plain,(
    v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f71,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f48])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK2(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f33])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).

fof(f49,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k1_tarski(X1) = k6_domain_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k6_domain_1(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f12,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f27])).

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
    inference(nnf_transformation,[],[f28])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f41])).

fof(f43,plain,(
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
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK3(X0,X1) != X1
        & r1_tarski(X1,sK3(X0,X1))
        & v2_tex_2(sK3(X0,X1),X0)
        & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK3(X0,X1) != X1
                & r1_tarski(X1,sK3(X0,X1))
                & v2_tex_2(sK3(X0,X1),X0)
                & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_10,plain,
    ( r2_hidden(sK1(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1855,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK1(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_26,negated_conjecture,
    ( v2_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_313,plain,
    ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_26])).

cnf(c_314,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,negated_conjecture,
    ( l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_316,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_314,c_27,c_25])).

cnf(c_1849,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1859,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2992,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK2(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1849,c_1859])).

cnf(c_3435,plain,
    ( sK2(sK4) = k1_xboole_0
    | m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1855,c_2992])).

cnf(c_24,negated_conjecture,
    ( v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_11,plain,
    ( v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_324,plain,
    ( v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | ~ v1_xboole_0(sK2(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_325,plain,
    ( v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4)
    | ~ v1_xboole_0(sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_324])).

cnf(c_1458,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2018,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2(sK4))
    | sK2(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2020,plain,
    ( v1_xboole_0(sK2(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_2066,plain,
    ( r2_hidden(sK1(sK5),sK5)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2194,plain,
    ( ~ r2_hidden(sK1(sK5),sK5)
    | ~ v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2746,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(sK5)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2748,plain,
    ( ~ v1_xboole_0(sK5)
    | v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2746])).

cnf(c_3592,plain,
    ( m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3435,c_27,c_25,c_24,c_325,c_2020,c_2066,c_2194,c_2748])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,X1)
    | v1_xboole_0(X1)
    | k6_domain_1(X1,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1853,plain,
    ( k6_domain_1(X0,X1) = k1_tarski(X1)
    | m1_subset_1(X1,X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3597,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK1(sK2(sK4))) = k1_tarski(sK1(sK2(sK4)))
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3592,c_1853])).

cnf(c_28,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_30,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_315,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | l1_pre_topc(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_327,plain,
    ( ~ v1_xboole_0(sK2(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_325,c_27,c_25])).

cnf(c_674,plain,
    ( r2_hidden(sK0(X0),X0)
    | sK2(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_327])).

cnf(c_675,plain,
    ( r2_hidden(sK0(sK2(sK4)),sK2(sK4)) ),
    inference(unflattening,[status(thm)],[c_674])).

cnf(c_676,plain,
    ( r2_hidden(sK0(sK2(sK4)),sK2(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2094,plain,
    ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(X0))
    | ~ r2_hidden(sK0(sK2(sK4)),sK2(sK4))
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2383,plain,
    ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r2_hidden(sK0(sK2(sK4)),sK2(sK4))
    | ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(instantiation,[status(thm)],[c_2094])).

cnf(c_2384,plain,
    ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
    | r2_hidden(sK0(sK2(sK4)),sK2(sK4)) != iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2383])).

cnf(c_3861,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK1(sK2(sK4))) = k1_tarski(sK1(sK2(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3597,c_28,c_30,c_315,c_676,c_2384])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1854,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3864,plain,
    ( m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) != iProver_top
    | m1_subset_1(k1_tarski(sK1(sK2(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
    | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3861,c_1854])).

cnf(c_4650,plain,
    ( m1_subset_1(k1_tarski(sK1(sK2(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3864,c_27,c_28,c_25,c_30,c_24,c_315,c_325,c_676,c_2020,c_2066,c_2194,c_2384,c_2748,c_3435])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1852,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2991,plain,
    ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1852,c_1859])).

cnf(c_693,plain,
    ( ~ r2_hidden(X0,X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_24])).

cnf(c_694,plain,
    ( ~ r2_hidden(X0,sK5) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_695,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_3074,plain,
    ( r2_hidden(X0,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2991,c_695])).

cnf(c_3080,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1855,c_3074])).

cnf(c_22,negated_conjecture,
    ( v3_tex_2(sK5,sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_430,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | X2 = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_431,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_557,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(X1,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 != X2
    | X0 = X1
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_431])).

cnf(c_558,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_572,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ v3_tex_2(k1_xboole_0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | X0 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_558,c_5])).

cnf(c_916,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK4 != sK4
    | sK5 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_572])).

cnf(c_1057,plain,
    ( ~ v2_tex_2(X0,sK4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(equality_resolution_simp,[status(thm)],[c_916])).

cnf(c_1840,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = X0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1057])).

cnf(c_3178,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 != k1_xboole_0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3080,c_1840])).

cnf(c_3187,plain,
    ( k1_xboole_0 = X0
    | v2_tex_2(X0,sK4) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3178])).

cnf(c_4659,plain,
    ( k1_tarski(sK1(sK2(sK4))) = k1_xboole_0
    | v2_tex_2(k1_tarski(sK1(sK2(sK4))),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4650,c_3187])).

cnf(c_21,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ v2_pre_topc(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_295,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
    | ~ m1_subset_1(X1,u1_struct_0(X0))
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_296,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4))
    | v2_struct_0(sK4)
    | ~ l1_pre_topc(sK4) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_300,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
    | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_296,c_27,c_25])).

cnf(c_1850,plain,
    ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4) = iProver_top
    | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_3865,plain,
    ( v2_tex_2(k1_tarski(sK1(sK2(sK4))),sK4) = iProver_top
    | m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3861,c_1850])).

cnf(c_5024,plain,
    ( k1_tarski(sK1(sK2(sK4))) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_27,c_25,c_24,c_325,c_2020,c_2066,c_2194,c_2748,c_3435,c_3865])).

cnf(c_2,plain,
    ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_4,plain,
    ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2360,plain,
    ( k1_tarski(X0) != k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2,c_4])).

cnf(c_5027,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5024,c_2360])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:52:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  % Running in FOF mode
% 2.43/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.43/1.01  
% 2.43/1.01  ------  iProver source info
% 2.43/1.01  
% 2.43/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.43/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.43/1.01  git: non_committed_changes: false
% 2.43/1.01  git: last_make_outside_of_git: false
% 2.43/1.01  
% 2.43/1.01  ------ 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options
% 2.43/1.01  
% 2.43/1.01  --out_options                           all
% 2.43/1.01  --tptp_safe_out                         true
% 2.43/1.01  --problem_path                          ""
% 2.43/1.01  --include_path                          ""
% 2.43/1.01  --clausifier                            res/vclausify_rel
% 2.43/1.01  --clausifier_options                    --mode clausify
% 2.43/1.01  --stdin                                 false
% 2.43/1.01  --stats_out                             all
% 2.43/1.01  
% 2.43/1.01  ------ General Options
% 2.43/1.01  
% 2.43/1.01  --fof                                   false
% 2.43/1.01  --time_out_real                         305.
% 2.43/1.01  --time_out_virtual                      -1.
% 2.43/1.01  --symbol_type_check                     false
% 2.43/1.01  --clausify_out                          false
% 2.43/1.01  --sig_cnt_out                           false
% 2.43/1.01  --trig_cnt_out                          false
% 2.43/1.01  --trig_cnt_out_tolerance                1.
% 2.43/1.01  --trig_cnt_out_sk_spl                   false
% 2.43/1.01  --abstr_cl_out                          false
% 2.43/1.01  
% 2.43/1.01  ------ Global Options
% 2.43/1.01  
% 2.43/1.01  --schedule                              default
% 2.43/1.01  --add_important_lit                     false
% 2.43/1.01  --prop_solver_per_cl                    1000
% 2.43/1.01  --min_unsat_core                        false
% 2.43/1.01  --soft_assumptions                      false
% 2.43/1.01  --soft_lemma_size                       3
% 2.43/1.01  --prop_impl_unit_size                   0
% 2.43/1.01  --prop_impl_unit                        []
% 2.43/1.01  --share_sel_clauses                     true
% 2.43/1.01  --reset_solvers                         false
% 2.43/1.01  --bc_imp_inh                            [conj_cone]
% 2.43/1.01  --conj_cone_tolerance                   3.
% 2.43/1.01  --extra_neg_conj                        none
% 2.43/1.01  --large_theory_mode                     true
% 2.43/1.01  --prolific_symb_bound                   200
% 2.43/1.01  --lt_threshold                          2000
% 2.43/1.01  --clause_weak_htbl                      true
% 2.43/1.01  --gc_record_bc_elim                     false
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing Options
% 2.43/1.01  
% 2.43/1.01  --preprocessing_flag                    true
% 2.43/1.01  --time_out_prep_mult                    0.1
% 2.43/1.01  --splitting_mode                        input
% 2.43/1.01  --splitting_grd                         true
% 2.43/1.01  --splitting_cvd                         false
% 2.43/1.01  --splitting_cvd_svl                     false
% 2.43/1.01  --splitting_nvd                         32
% 2.43/1.01  --sub_typing                            true
% 2.43/1.01  --prep_gs_sim                           true
% 2.43/1.01  --prep_unflatten                        true
% 2.43/1.01  --prep_res_sim                          true
% 2.43/1.01  --prep_upred                            true
% 2.43/1.01  --prep_sem_filter                       exhaustive
% 2.43/1.01  --prep_sem_filter_out                   false
% 2.43/1.01  --pred_elim                             true
% 2.43/1.01  --res_sim_input                         true
% 2.43/1.01  --eq_ax_congr_red                       true
% 2.43/1.01  --pure_diseq_elim                       true
% 2.43/1.01  --brand_transform                       false
% 2.43/1.01  --non_eq_to_eq                          false
% 2.43/1.01  --prep_def_merge                        true
% 2.43/1.01  --prep_def_merge_prop_impl              false
% 2.43/1.01  --prep_def_merge_mbd                    true
% 2.43/1.01  --prep_def_merge_tr_red                 false
% 2.43/1.01  --prep_def_merge_tr_cl                  false
% 2.43/1.01  --smt_preprocessing                     true
% 2.43/1.01  --smt_ac_axioms                         fast
% 2.43/1.01  --preprocessed_out                      false
% 2.43/1.01  --preprocessed_stats                    false
% 2.43/1.01  
% 2.43/1.01  ------ Abstraction refinement Options
% 2.43/1.01  
% 2.43/1.01  --abstr_ref                             []
% 2.43/1.01  --abstr_ref_prep                        false
% 2.43/1.01  --abstr_ref_until_sat                   false
% 2.43/1.01  --abstr_ref_sig_restrict                funpre
% 2.43/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.01  --abstr_ref_under                       []
% 2.43/1.01  
% 2.43/1.01  ------ SAT Options
% 2.43/1.01  
% 2.43/1.01  --sat_mode                              false
% 2.43/1.01  --sat_fm_restart_options                ""
% 2.43/1.01  --sat_gr_def                            false
% 2.43/1.01  --sat_epr_types                         true
% 2.43/1.01  --sat_non_cyclic_types                  false
% 2.43/1.01  --sat_finite_models                     false
% 2.43/1.01  --sat_fm_lemmas                         false
% 2.43/1.01  --sat_fm_prep                           false
% 2.43/1.01  --sat_fm_uc_incr                        true
% 2.43/1.01  --sat_out_model                         small
% 2.43/1.01  --sat_out_clauses                       false
% 2.43/1.01  
% 2.43/1.01  ------ QBF Options
% 2.43/1.01  
% 2.43/1.01  --qbf_mode                              false
% 2.43/1.01  --qbf_elim_univ                         false
% 2.43/1.01  --qbf_dom_inst                          none
% 2.43/1.01  --qbf_dom_pre_inst                      false
% 2.43/1.01  --qbf_sk_in                             false
% 2.43/1.01  --qbf_pred_elim                         true
% 2.43/1.01  --qbf_split                             512
% 2.43/1.01  
% 2.43/1.01  ------ BMC1 Options
% 2.43/1.01  
% 2.43/1.01  --bmc1_incremental                      false
% 2.43/1.01  --bmc1_axioms                           reachable_all
% 2.43/1.01  --bmc1_min_bound                        0
% 2.43/1.01  --bmc1_max_bound                        -1
% 2.43/1.01  --bmc1_max_bound_default                -1
% 2.43/1.01  --bmc1_symbol_reachability              true
% 2.43/1.01  --bmc1_property_lemmas                  false
% 2.43/1.01  --bmc1_k_induction                      false
% 2.43/1.01  --bmc1_non_equiv_states                 false
% 2.43/1.01  --bmc1_deadlock                         false
% 2.43/1.01  --bmc1_ucm                              false
% 2.43/1.01  --bmc1_add_unsat_core                   none
% 2.43/1.01  --bmc1_unsat_core_children              false
% 2.43/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.01  --bmc1_out_stat                         full
% 2.43/1.01  --bmc1_ground_init                      false
% 2.43/1.01  --bmc1_pre_inst_next_state              false
% 2.43/1.01  --bmc1_pre_inst_state                   false
% 2.43/1.01  --bmc1_pre_inst_reach_state             false
% 2.43/1.01  --bmc1_out_unsat_core                   false
% 2.43/1.01  --bmc1_aig_witness_out                  false
% 2.43/1.01  --bmc1_verbose                          false
% 2.43/1.01  --bmc1_dump_clauses_tptp                false
% 2.43/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.01  --bmc1_dump_file                        -
% 2.43/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.01  --bmc1_ucm_extend_mode                  1
% 2.43/1.01  --bmc1_ucm_init_mode                    2
% 2.43/1.01  --bmc1_ucm_cone_mode                    none
% 2.43/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.01  --bmc1_ucm_relax_model                  4
% 2.43/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.01  --bmc1_ucm_layered_model                none
% 2.43/1.01  --bmc1_ucm_max_lemma_size               10
% 2.43/1.01  
% 2.43/1.01  ------ AIG Options
% 2.43/1.01  
% 2.43/1.01  --aig_mode                              false
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation Options
% 2.43/1.01  
% 2.43/1.01  --instantiation_flag                    true
% 2.43/1.01  --inst_sos_flag                         false
% 2.43/1.01  --inst_sos_phase                        true
% 2.43/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel_side                     num_symb
% 2.43/1.01  --inst_solver_per_active                1400
% 2.43/1.01  --inst_solver_calls_frac                1.
% 2.43/1.01  --inst_passive_queue_type               priority_queues
% 2.43/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.01  --inst_passive_queues_freq              [25;2]
% 2.43/1.01  --inst_dismatching                      true
% 2.43/1.01  --inst_eager_unprocessed_to_passive     true
% 2.43/1.01  --inst_prop_sim_given                   true
% 2.43/1.01  --inst_prop_sim_new                     false
% 2.43/1.01  --inst_subs_new                         false
% 2.43/1.01  --inst_eq_res_simp                      false
% 2.43/1.01  --inst_subs_given                       false
% 2.43/1.01  --inst_orphan_elimination               true
% 2.43/1.01  --inst_learning_loop_flag               true
% 2.43/1.01  --inst_learning_start                   3000
% 2.43/1.01  --inst_learning_factor                  2
% 2.43/1.01  --inst_start_prop_sim_after_learn       3
% 2.43/1.01  --inst_sel_renew                        solver
% 2.43/1.01  --inst_lit_activity_flag                true
% 2.43/1.01  --inst_restr_to_given                   false
% 2.43/1.01  --inst_activity_threshold               500
% 2.43/1.01  --inst_out_proof                        true
% 2.43/1.01  
% 2.43/1.01  ------ Resolution Options
% 2.43/1.01  
% 2.43/1.01  --resolution_flag                       true
% 2.43/1.01  --res_lit_sel                           adaptive
% 2.43/1.01  --res_lit_sel_side                      none
% 2.43/1.01  --res_ordering                          kbo
% 2.43/1.01  --res_to_prop_solver                    active
% 2.43/1.01  --res_prop_simpl_new                    false
% 2.43/1.01  --res_prop_simpl_given                  true
% 2.43/1.01  --res_passive_queue_type                priority_queues
% 2.43/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.01  --res_passive_queues_freq               [15;5]
% 2.43/1.01  --res_forward_subs                      full
% 2.43/1.01  --res_backward_subs                     full
% 2.43/1.01  --res_forward_subs_resolution           true
% 2.43/1.01  --res_backward_subs_resolution          true
% 2.43/1.01  --res_orphan_elimination                true
% 2.43/1.01  --res_time_limit                        2.
% 2.43/1.01  --res_out_proof                         true
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Options
% 2.43/1.01  
% 2.43/1.01  --superposition_flag                    true
% 2.43/1.01  --sup_passive_queue_type                priority_queues
% 2.43/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.01  --demod_completeness_check              fast
% 2.43/1.01  --demod_use_ground                      true
% 2.43/1.01  --sup_to_prop_solver                    passive
% 2.43/1.01  --sup_prop_simpl_new                    true
% 2.43/1.01  --sup_prop_simpl_given                  true
% 2.43/1.01  --sup_fun_splitting                     false
% 2.43/1.01  --sup_smt_interval                      50000
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Simplification Setup
% 2.43/1.01  
% 2.43/1.01  --sup_indices_passive                   []
% 2.43/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_full_bw                           [BwDemod]
% 2.43/1.01  --sup_immed_triv                        [TrivRules]
% 2.43/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_immed_bw_main                     []
% 2.43/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  
% 2.43/1.01  ------ Combination Options
% 2.43/1.01  
% 2.43/1.01  --comb_res_mult                         3
% 2.43/1.01  --comb_sup_mult                         2
% 2.43/1.01  --comb_inst_mult                        10
% 2.43/1.01  
% 2.43/1.01  ------ Debug Options
% 2.43/1.01  
% 2.43/1.01  --dbg_backtrace                         false
% 2.43/1.01  --dbg_dump_prop_clauses                 false
% 2.43/1.01  --dbg_dump_prop_clauses_file            -
% 2.43/1.01  --dbg_out_stat                          false
% 2.43/1.01  ------ Parsing...
% 2.43/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.43/1.01  ------ Proving...
% 2.43/1.01  ------ Problem Properties 
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  clauses                                 25
% 2.43/1.01  conjectures                             2
% 2.43/1.01  EPR                                     3
% 2.43/1.01  Horn                                    19
% 2.43/1.01  unary                                   8
% 2.43/1.01  binary                                  4
% 2.43/1.01  lits                                    59
% 2.43/1.01  lits eq                                 14
% 2.43/1.01  fd_pure                                 0
% 2.43/1.01  fd_pseudo                               0
% 2.43/1.01  fd_cond                                 7
% 2.43/1.01  fd_pseudo_cond                          0
% 2.43/1.01  AC symbols                              0
% 2.43/1.01  
% 2.43/1.01  ------ Schedule dynamic 5 is on 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  ------ 
% 2.43/1.01  Current options:
% 2.43/1.01  ------ 
% 2.43/1.01  
% 2.43/1.01  ------ Input Options
% 2.43/1.01  
% 2.43/1.01  --out_options                           all
% 2.43/1.01  --tptp_safe_out                         true
% 2.43/1.01  --problem_path                          ""
% 2.43/1.01  --include_path                          ""
% 2.43/1.01  --clausifier                            res/vclausify_rel
% 2.43/1.01  --clausifier_options                    --mode clausify
% 2.43/1.01  --stdin                                 false
% 2.43/1.01  --stats_out                             all
% 2.43/1.01  
% 2.43/1.01  ------ General Options
% 2.43/1.01  
% 2.43/1.01  --fof                                   false
% 2.43/1.01  --time_out_real                         305.
% 2.43/1.01  --time_out_virtual                      -1.
% 2.43/1.01  --symbol_type_check                     false
% 2.43/1.01  --clausify_out                          false
% 2.43/1.01  --sig_cnt_out                           false
% 2.43/1.01  --trig_cnt_out                          false
% 2.43/1.01  --trig_cnt_out_tolerance                1.
% 2.43/1.01  --trig_cnt_out_sk_spl                   false
% 2.43/1.01  --abstr_cl_out                          false
% 2.43/1.01  
% 2.43/1.01  ------ Global Options
% 2.43/1.01  
% 2.43/1.01  --schedule                              default
% 2.43/1.01  --add_important_lit                     false
% 2.43/1.01  --prop_solver_per_cl                    1000
% 2.43/1.01  --min_unsat_core                        false
% 2.43/1.01  --soft_assumptions                      false
% 2.43/1.01  --soft_lemma_size                       3
% 2.43/1.01  --prop_impl_unit_size                   0
% 2.43/1.01  --prop_impl_unit                        []
% 2.43/1.01  --share_sel_clauses                     true
% 2.43/1.01  --reset_solvers                         false
% 2.43/1.01  --bc_imp_inh                            [conj_cone]
% 2.43/1.01  --conj_cone_tolerance                   3.
% 2.43/1.01  --extra_neg_conj                        none
% 2.43/1.01  --large_theory_mode                     true
% 2.43/1.01  --prolific_symb_bound                   200
% 2.43/1.01  --lt_threshold                          2000
% 2.43/1.01  --clause_weak_htbl                      true
% 2.43/1.01  --gc_record_bc_elim                     false
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing Options
% 2.43/1.01  
% 2.43/1.01  --preprocessing_flag                    true
% 2.43/1.01  --time_out_prep_mult                    0.1
% 2.43/1.01  --splitting_mode                        input
% 2.43/1.01  --splitting_grd                         true
% 2.43/1.01  --splitting_cvd                         false
% 2.43/1.01  --splitting_cvd_svl                     false
% 2.43/1.01  --splitting_nvd                         32
% 2.43/1.01  --sub_typing                            true
% 2.43/1.01  --prep_gs_sim                           true
% 2.43/1.01  --prep_unflatten                        true
% 2.43/1.01  --prep_res_sim                          true
% 2.43/1.01  --prep_upred                            true
% 2.43/1.01  --prep_sem_filter                       exhaustive
% 2.43/1.01  --prep_sem_filter_out                   false
% 2.43/1.01  --pred_elim                             true
% 2.43/1.01  --res_sim_input                         true
% 2.43/1.01  --eq_ax_congr_red                       true
% 2.43/1.01  --pure_diseq_elim                       true
% 2.43/1.01  --brand_transform                       false
% 2.43/1.01  --non_eq_to_eq                          false
% 2.43/1.01  --prep_def_merge                        true
% 2.43/1.01  --prep_def_merge_prop_impl              false
% 2.43/1.01  --prep_def_merge_mbd                    true
% 2.43/1.01  --prep_def_merge_tr_red                 false
% 2.43/1.01  --prep_def_merge_tr_cl                  false
% 2.43/1.01  --smt_preprocessing                     true
% 2.43/1.01  --smt_ac_axioms                         fast
% 2.43/1.01  --preprocessed_out                      false
% 2.43/1.01  --preprocessed_stats                    false
% 2.43/1.01  
% 2.43/1.01  ------ Abstraction refinement Options
% 2.43/1.01  
% 2.43/1.01  --abstr_ref                             []
% 2.43/1.01  --abstr_ref_prep                        false
% 2.43/1.01  --abstr_ref_until_sat                   false
% 2.43/1.01  --abstr_ref_sig_restrict                funpre
% 2.43/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.43/1.01  --abstr_ref_under                       []
% 2.43/1.01  
% 2.43/1.01  ------ SAT Options
% 2.43/1.01  
% 2.43/1.01  --sat_mode                              false
% 2.43/1.01  --sat_fm_restart_options                ""
% 2.43/1.01  --sat_gr_def                            false
% 2.43/1.01  --sat_epr_types                         true
% 2.43/1.01  --sat_non_cyclic_types                  false
% 2.43/1.01  --sat_finite_models                     false
% 2.43/1.01  --sat_fm_lemmas                         false
% 2.43/1.01  --sat_fm_prep                           false
% 2.43/1.01  --sat_fm_uc_incr                        true
% 2.43/1.01  --sat_out_model                         small
% 2.43/1.01  --sat_out_clauses                       false
% 2.43/1.01  
% 2.43/1.01  ------ QBF Options
% 2.43/1.01  
% 2.43/1.01  --qbf_mode                              false
% 2.43/1.01  --qbf_elim_univ                         false
% 2.43/1.01  --qbf_dom_inst                          none
% 2.43/1.01  --qbf_dom_pre_inst                      false
% 2.43/1.01  --qbf_sk_in                             false
% 2.43/1.01  --qbf_pred_elim                         true
% 2.43/1.01  --qbf_split                             512
% 2.43/1.01  
% 2.43/1.01  ------ BMC1 Options
% 2.43/1.01  
% 2.43/1.01  --bmc1_incremental                      false
% 2.43/1.01  --bmc1_axioms                           reachable_all
% 2.43/1.01  --bmc1_min_bound                        0
% 2.43/1.01  --bmc1_max_bound                        -1
% 2.43/1.01  --bmc1_max_bound_default                -1
% 2.43/1.01  --bmc1_symbol_reachability              true
% 2.43/1.01  --bmc1_property_lemmas                  false
% 2.43/1.01  --bmc1_k_induction                      false
% 2.43/1.01  --bmc1_non_equiv_states                 false
% 2.43/1.01  --bmc1_deadlock                         false
% 2.43/1.01  --bmc1_ucm                              false
% 2.43/1.01  --bmc1_add_unsat_core                   none
% 2.43/1.01  --bmc1_unsat_core_children              false
% 2.43/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.43/1.01  --bmc1_out_stat                         full
% 2.43/1.01  --bmc1_ground_init                      false
% 2.43/1.01  --bmc1_pre_inst_next_state              false
% 2.43/1.01  --bmc1_pre_inst_state                   false
% 2.43/1.01  --bmc1_pre_inst_reach_state             false
% 2.43/1.01  --bmc1_out_unsat_core                   false
% 2.43/1.01  --bmc1_aig_witness_out                  false
% 2.43/1.01  --bmc1_verbose                          false
% 2.43/1.01  --bmc1_dump_clauses_tptp                false
% 2.43/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.43/1.01  --bmc1_dump_file                        -
% 2.43/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.43/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.43/1.01  --bmc1_ucm_extend_mode                  1
% 2.43/1.01  --bmc1_ucm_init_mode                    2
% 2.43/1.01  --bmc1_ucm_cone_mode                    none
% 2.43/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.43/1.01  --bmc1_ucm_relax_model                  4
% 2.43/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.43/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.43/1.01  --bmc1_ucm_layered_model                none
% 2.43/1.01  --bmc1_ucm_max_lemma_size               10
% 2.43/1.01  
% 2.43/1.01  ------ AIG Options
% 2.43/1.01  
% 2.43/1.01  --aig_mode                              false
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation Options
% 2.43/1.01  
% 2.43/1.01  --instantiation_flag                    true
% 2.43/1.01  --inst_sos_flag                         false
% 2.43/1.01  --inst_sos_phase                        true
% 2.43/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.43/1.01  --inst_lit_sel_side                     none
% 2.43/1.01  --inst_solver_per_active                1400
% 2.43/1.01  --inst_solver_calls_frac                1.
% 2.43/1.01  --inst_passive_queue_type               priority_queues
% 2.43/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.43/1.01  --inst_passive_queues_freq              [25;2]
% 2.43/1.01  --inst_dismatching                      true
% 2.43/1.01  --inst_eager_unprocessed_to_passive     true
% 2.43/1.01  --inst_prop_sim_given                   true
% 2.43/1.01  --inst_prop_sim_new                     false
% 2.43/1.01  --inst_subs_new                         false
% 2.43/1.01  --inst_eq_res_simp                      false
% 2.43/1.01  --inst_subs_given                       false
% 2.43/1.01  --inst_orphan_elimination               true
% 2.43/1.01  --inst_learning_loop_flag               true
% 2.43/1.01  --inst_learning_start                   3000
% 2.43/1.01  --inst_learning_factor                  2
% 2.43/1.01  --inst_start_prop_sim_after_learn       3
% 2.43/1.01  --inst_sel_renew                        solver
% 2.43/1.01  --inst_lit_activity_flag                true
% 2.43/1.01  --inst_restr_to_given                   false
% 2.43/1.01  --inst_activity_threshold               500
% 2.43/1.01  --inst_out_proof                        true
% 2.43/1.01  
% 2.43/1.01  ------ Resolution Options
% 2.43/1.01  
% 2.43/1.01  --resolution_flag                       false
% 2.43/1.01  --res_lit_sel                           adaptive
% 2.43/1.01  --res_lit_sel_side                      none
% 2.43/1.01  --res_ordering                          kbo
% 2.43/1.01  --res_to_prop_solver                    active
% 2.43/1.01  --res_prop_simpl_new                    false
% 2.43/1.01  --res_prop_simpl_given                  true
% 2.43/1.01  --res_passive_queue_type                priority_queues
% 2.43/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.43/1.01  --res_passive_queues_freq               [15;5]
% 2.43/1.01  --res_forward_subs                      full
% 2.43/1.01  --res_backward_subs                     full
% 2.43/1.01  --res_forward_subs_resolution           true
% 2.43/1.01  --res_backward_subs_resolution          true
% 2.43/1.01  --res_orphan_elimination                true
% 2.43/1.01  --res_time_limit                        2.
% 2.43/1.01  --res_out_proof                         true
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Options
% 2.43/1.01  
% 2.43/1.01  --superposition_flag                    true
% 2.43/1.01  --sup_passive_queue_type                priority_queues
% 2.43/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.43/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.43/1.01  --demod_completeness_check              fast
% 2.43/1.01  --demod_use_ground                      true
% 2.43/1.01  --sup_to_prop_solver                    passive
% 2.43/1.01  --sup_prop_simpl_new                    true
% 2.43/1.01  --sup_prop_simpl_given                  true
% 2.43/1.01  --sup_fun_splitting                     false
% 2.43/1.01  --sup_smt_interval                      50000
% 2.43/1.01  
% 2.43/1.01  ------ Superposition Simplification Setup
% 2.43/1.01  
% 2.43/1.01  --sup_indices_passive                   []
% 2.43/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.43/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.43/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_full_bw                           [BwDemod]
% 2.43/1.01  --sup_immed_triv                        [TrivRules]
% 2.43/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.43/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_immed_bw_main                     []
% 2.43/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.43/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.43/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.43/1.01  
% 2.43/1.01  ------ Combination Options
% 2.43/1.01  
% 2.43/1.01  --comb_res_mult                         3
% 2.43/1.01  --comb_sup_mult                         2
% 2.43/1.01  --comb_inst_mult                        10
% 2.43/1.01  
% 2.43/1.01  ------ Debug Options
% 2.43/1.01  
% 2.43/1.01  --dbg_backtrace                         false
% 2.43/1.01  --dbg_dump_prop_clauses                 false
% 2.43/1.01  --dbg_dump_prop_clauses_file            -
% 2.43/1.01  --dbg_out_stat                          false
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  ------ Proving...
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS status Theorem for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01   Resolution empty clause
% 2.43/1.01  
% 2.43/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  fof(f8,axiom,(
% 2.43/1.01    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4] : ~(k3_mcart_1(X2,X3,X4) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f20,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 2.43/1.01    inference(ennf_transformation,[],[f8])).
% 2.43/1.01  
% 2.43/1.01  fof(f37,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : (! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X4,X3,X2] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f38,plain,(
% 2.43/1.01    ! [X0] : ((! [X2,X3,X4] : (k3_mcart_1(X2,X3,X4) != sK1(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK1(X0),X0)) | k1_xboole_0 = X0)),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f20,f37])).
% 2.43/1.01  
% 2.43/1.01  fof(f57,plain,(
% 2.43/1.01    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 2.43/1.01    inference(cnf_transformation,[],[f38])).
% 2.43/1.01  
% 2.43/1.01  fof(f9,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f16,plain,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    inference(pure_predicate_removal,[],[f9])).
% 2.43/1.01  
% 2.43/1.01  fof(f21,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f16])).
% 2.43/1.01  
% 2.43/1.01  fof(f22,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f21])).
% 2.43/1.01  
% 2.43/1.01  fof(f39,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f40,plain,(
% 2.43/1.01    ! [X0] : ((~v1_xboole_0(sK2(X0)) & m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f39])).
% 2.43/1.01  
% 2.43/1.01  fof(f60,plain,(
% 2.43/1.01    ( ! [X0] : (m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f14,conjecture,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f15,negated_conjecture,(
% 2.43/1.01    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 2.43/1.01    inference(negated_conjecture,[],[f14])).
% 2.43/1.01  
% 2.43/1.01  fof(f31,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f15])).
% 2.43/1.01  
% 2.43/1.01  fof(f32,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f31])).
% 2.43/1.01  
% 2.43/1.01  fof(f47,plain,(
% 2.43/1.01    ( ! [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => (v3_tex_2(sK5,X0) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(sK5))) )),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f46,plain,(
% 2.43/1.01    ? [X0] : (? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v3_tex_2(X1,sK4) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f48,plain,(
% 2.43/1.01    (v3_tex_2(sK5,sK4) & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) & v1_xboole_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f32,f47,f46])).
% 2.43/1.01  
% 2.43/1.01  fof(f72,plain,(
% 2.43/1.01    v2_pre_topc(sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f71,plain,(
% 2.43/1.01    ~v2_struct_0(sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f73,plain,(
% 2.43/1.01    l1_pre_topc(sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f6,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f17,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 2.43/1.01    inference(ennf_transformation,[],[f6])).
% 2.43/1.01  
% 2.43/1.01  fof(f18,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.43/1.01    inference(flattening,[],[f17])).
% 2.43/1.01  
% 2.43/1.01  fof(f55,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f18])).
% 2.43/1.01  
% 2.43/1.01  fof(f74,plain,(
% 2.43/1.01    v1_xboole_0(sK5)),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f61,plain,(
% 2.43/1.01    ( ! [X0] : (~v1_xboole_0(sK2(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f40])).
% 2.43/1.01  
% 2.43/1.01  fof(f1,axiom,(
% 2.43/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f33,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(nnf_transformation,[],[f1])).
% 2.43/1.01  
% 2.43/1.01  fof(f34,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(rectify,[],[f33])).
% 2.43/1.01  
% 2.43/1.01  fof(f35,plain,(
% 2.43/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f36,plain,(
% 2.43/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f34,f35])).
% 2.43/1.01  
% 2.43/1.01  fof(f49,plain,(
% 2.43/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f36])).
% 2.43/1.01  
% 2.43/1.01  fof(f11,axiom,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k1_tarski(X1) = k6_domain_1(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f25,plain,(
% 2.43/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f11])).
% 2.43/1.01  
% 2.43/1.01  fof(f26,plain,(
% 2.43/1.01    ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.43/1.01    inference(flattening,[],[f25])).
% 2.43/1.01  
% 2.43/1.01  fof(f63,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k1_tarski(X1) = k6_domain_1(X0,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f26])).
% 2.43/1.01  
% 2.43/1.01  fof(f50,plain,(
% 2.43/1.01    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f36])).
% 2.43/1.01  
% 2.43/1.01  fof(f7,axiom,(
% 2.43/1.01    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f19,plain,(
% 2.43/1.01    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.43/1.01    inference(ennf_transformation,[],[f7])).
% 2.43/1.01  
% 2.43/1.01  fof(f56,plain,(
% 2.43/1.01    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f19])).
% 2.43/1.01  
% 2.43/1.01  fof(f10,axiom,(
% 2.43/1.01    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f23,plain,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f10])).
% 2.43/1.01  
% 2.43/1.01  fof(f24,plain,(
% 2.43/1.01    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 2.43/1.01    inference(flattening,[],[f23])).
% 2.43/1.01  
% 2.43/1.01  fof(f62,plain,(
% 2.43/1.01    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f24])).
% 2.43/1.01  
% 2.43/1.01  fof(f75,plain,(
% 2.43/1.01    m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4)))),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f76,plain,(
% 2.43/1.01    v3_tex_2(sK5,sK4)),
% 2.43/1.01    inference(cnf_transformation,[],[f48])).
% 2.43/1.01  
% 2.43/1.01  fof(f3,axiom,(
% 2.43/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f52,plain,(
% 2.43/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f3])).
% 2.43/1.01  
% 2.43/1.01  fof(f12,axiom,(
% 2.43/1.01    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f27,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(ennf_transformation,[],[f12])).
% 2.43/1.01  
% 2.43/1.01  fof(f28,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f27])).
% 2.43/1.01  
% 2.43/1.01  fof(f41,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(nnf_transformation,[],[f28])).
% 2.43/1.01  
% 2.43/1.01  fof(f42,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(flattening,[],[f41])).
% 2.43/1.01  
% 2.43/1.01  fof(f43,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(rectify,[],[f42])).
% 2.43/1.01  
% 2.43/1.01  fof(f44,plain,(
% 2.43/1.01    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.43/1.01    introduced(choice_axiom,[])).
% 2.43/1.01  
% 2.43/1.01  fof(f45,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK3(X0,X1) != X1 & r1_tarski(X1,sK3(X0,X1)) & v2_tex_2(sK3(X0,X1),X0) & m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.43/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f43,f44])).
% 2.43/1.01  
% 2.43/1.01  fof(f65,plain,(
% 2.43/1.01    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f45])).
% 2.43/1.01  
% 2.43/1.01  fof(f5,axiom,(
% 2.43/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f54,plain,(
% 2.43/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.43/1.01    inference(cnf_transformation,[],[f5])).
% 2.43/1.01  
% 2.43/1.01  fof(f13,axiom,(
% 2.43/1.01    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f29,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.43/1.01    inference(ennf_transformation,[],[f13])).
% 2.43/1.01  
% 2.43/1.01  fof(f30,plain,(
% 2.43/1.01    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.43/1.01    inference(flattening,[],[f29])).
% 2.43/1.01  
% 2.43/1.01  fof(f70,plain,(
% 2.43/1.01    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f30])).
% 2.43/1.01  
% 2.43/1.01  fof(f2,axiom,(
% 2.43/1.01    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f51,plain,(
% 2.43/1.01    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.43/1.01    inference(cnf_transformation,[],[f2])).
% 2.43/1.01  
% 2.43/1.01  fof(f4,axiom,(
% 2.43/1.01    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 2.43/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.43/1.01  
% 2.43/1.01  fof(f53,plain,(
% 2.43/1.01    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 2.43/1.01    inference(cnf_transformation,[],[f4])).
% 2.43/1.01  
% 2.43/1.01  cnf(c_10,plain,
% 2.43/1.01      ( r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1855,plain,
% 2.43/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_12,plain,
% 2.43/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | ~ v2_pre_topc(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_26,negated_conjecture,
% 2.43/1.01      ( v2_pre_topc(sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_313,plain,
% 2.43/1.01      ( m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | sK4 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_26]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_314,plain,
% 2.43/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | v2_struct_0(sK4)
% 2.43/1.01      | ~ l1_pre_topc(sK4) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_313]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_27,negated_conjecture,
% 2.43/1.01      ( ~ v2_struct_0(sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_25,negated_conjecture,
% 2.43/1.01      ( l1_pre_topc(sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_316,plain,
% 2.43/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_314,c_27,c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1849,plain,
% 2.43/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_6,plain,
% 2.43/1.01      ( m1_subset_1(X0,X1)
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ r2_hidden(X0,X2) ),
% 2.43/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1859,plain,
% 2.43/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.43/1.01      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 2.43/1.01      | r2_hidden(X0,X2) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2992,plain,
% 2.43/1.01      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 2.43/1.01      | r2_hidden(X0,sK2(sK4)) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1849,c_1859]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3435,plain,
% 2.43/1.01      ( sK2(sK4) = k1_xboole_0
% 2.43/1.01      | m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1855,c_2992]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_24,negated_conjecture,
% 2.43/1.01      ( v1_xboole_0(sK5) ),
% 2.43/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_11,plain,
% 2.43/1.01      ( v2_struct_0(X0)
% 2.43/1.01      | ~ v2_pre_topc(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | ~ v1_xboole_0(sK2(X0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_324,plain,
% 2.43/1.01      ( v2_struct_0(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | ~ v1_xboole_0(sK2(X0))
% 2.43/1.01      | sK4 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_325,plain,
% 2.43/1.01      ( v2_struct_0(sK4) | ~ l1_pre_topc(sK4) | ~ v1_xboole_0(sK2(sK4)) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_324]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1458,plain,
% 2.43/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.43/1.01      theory(equality) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2018,plain,
% 2.43/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2(sK4)) | sK2(sK4) != X0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1458]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2020,plain,
% 2.43/1.01      ( v1_xboole_0(sK2(sK4))
% 2.43/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.43/1.01      | sK2(sK4) != k1_xboole_0 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2018]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2066,plain,
% 2.43/1.01      ( r2_hidden(sK1(sK5),sK5) | k1_xboole_0 = sK5 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1,plain,
% 2.43/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2194,plain,
% 2.43/1.01      ( ~ r2_hidden(sK1(sK5),sK5) | ~ v1_xboole_0(sK5) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2746,plain,
% 2.43/1.01      ( v1_xboole_0(X0) | ~ v1_xboole_0(sK5) | X0 != sK5 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_1458]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2748,plain,
% 2.43/1.01      ( ~ v1_xboole_0(sK5) | v1_xboole_0(k1_xboole_0) | k1_xboole_0 != sK5 ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2746]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3592,plain,
% 2.43/1.01      ( m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_3435,c_27,c_25,c_24,c_325,c_2020,c_2066,c_2194,c_2748]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_14,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1)
% 2.43/1.01      | v1_xboole_0(X1)
% 2.43/1.01      | k6_domain_1(X1,X0) = k1_tarski(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1853,plain,
% 2.43/1.01      ( k6_domain_1(X0,X1) = k1_tarski(X1)
% 2.43/1.01      | m1_subset_1(X1,X0) != iProver_top
% 2.43/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3597,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK4),sK1(sK2(sK4))) = k1_tarski(sK1(sK2(sK4)))
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3592,c_1853]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_28,plain,
% 2.43/1.01      ( v2_struct_0(sK4) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_30,plain,
% 2.43/1.01      ( l1_pre_topc(sK4) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_315,plain,
% 2.43/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.43/1.01      | v2_struct_0(sK4) = iProver_top
% 2.43/1.01      | l1_pre_topc(sK4) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_0,plain,
% 2.43/1.01      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_327,plain,
% 2.43/1.01      ( ~ v1_xboole_0(sK2(sK4)) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_325,c_27,c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_674,plain,
% 2.43/1.01      ( r2_hidden(sK0(X0),X0) | sK2(sK4) != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_327]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_675,plain,
% 2.43/1.01      ( r2_hidden(sK0(sK2(sK4)),sK2(sK4)) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_674]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_676,plain,
% 2.43/1.01      ( r2_hidden(sK0(sK2(sK4)),sK2(sK4)) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_7,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.43/1.01      | ~ r2_hidden(X2,X0)
% 2.43/1.01      | ~ v1_xboole_0(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2094,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(X0))
% 2.43/1.01      | ~ r2_hidden(sK0(sK2(sK4)),sK2(sK4))
% 2.43/1.01      | ~ v1_xboole_0(X0) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_7]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2383,plain,
% 2.43/1.01      ( ~ m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | ~ r2_hidden(sK0(sK2(sK4)),sK2(sK4))
% 2.43/1.01      | ~ v1_xboole_0(u1_struct_0(sK4)) ),
% 2.43/1.01      inference(instantiation,[status(thm)],[c_2094]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2384,plain,
% 2.43/1.01      ( m1_subset_1(sK2(sK4),k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top
% 2.43/1.01      | r2_hidden(sK0(sK2(sK4)),sK2(sK4)) != iProver_top
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK4)) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_2383]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3861,plain,
% 2.43/1.01      ( k6_domain_1(u1_struct_0(sK4),sK1(sK2(sK4))) = k1_tarski(sK1(sK2(sK4))) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_3597,c_28,c_30,c_315,c_676,c_2384]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_13,plain,
% 2.43/1.01      ( ~ m1_subset_1(X0,X1)
% 2.43/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1))
% 2.43/1.01      | v1_xboole_0(X1) ),
% 2.43/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1854,plain,
% 2.43/1.01      ( m1_subset_1(X0,X1) != iProver_top
% 2.43/1.01      | m1_subset_1(k6_domain_1(X1,X0),k1_zfmisc_1(X1)) = iProver_top
% 2.43/1.01      | v1_xboole_0(X1) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3864,plain,
% 2.43/1.01      ( m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) != iProver_top
% 2.43/1.01      | m1_subset_1(k1_tarski(sK1(sK2(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top
% 2.43/1.01      | v1_xboole_0(u1_struct_0(sK4)) = iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3861,c_1854]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4650,plain,
% 2.43/1.01      ( m1_subset_1(k1_tarski(sK1(sK2(sK4))),k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_3864,c_27,c_28,c_25,c_30,c_24,c_315,c_325,c_676,c_2020,
% 2.43/1.01                 c_2066,c_2194,c_2384,c_2748,c_3435]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_23,negated_conjecture,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) ),
% 2.43/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1852,plain,
% 2.43/1.01      ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK4))) = iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2991,plain,
% 2.43/1.01      ( m1_subset_1(X0,u1_struct_0(sK4)) = iProver_top
% 2.43/1.01      | r2_hidden(X0,sK5) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1852,c_1859]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_693,plain,
% 2.43/1.01      ( ~ r2_hidden(X0,X1) | sK5 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_24]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_694,plain,
% 2.43/1.01      ( ~ r2_hidden(X0,sK5) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_693]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_695,plain,
% 2.43/1.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3074,plain,
% 2.43/1.01      ( r2_hidden(X0,sK5) != iProver_top ),
% 2.43/1.01      inference(global_propositional_subsumption,[status(thm)],[c_2991,c_695]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3080,plain,
% 2.43/1.01      ( sK5 = k1_xboole_0 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_1855,c_3074]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_22,negated_conjecture,
% 2.43/1.01      ( v3_tex_2(sK5,sK4) ),
% 2.43/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3,plain,
% 2.43/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_19,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,X1)
% 2.43/1.01      | ~ v3_tex_2(X2,X1)
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ r1_tarski(X2,X0)
% 2.43/1.01      | ~ l1_pre_topc(X1)
% 2.43/1.01      | X0 = X2 ),
% 2.43/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_430,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,X1)
% 2.43/1.01      | ~ v3_tex_2(X2,X1)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.43/1.01      | ~ r1_tarski(X2,X0)
% 2.43/1.01      | X2 = X0
% 2.43/1.01      | sK4 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_431,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ v3_tex_2(X1,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | ~ r1_tarski(X1,X0)
% 2.43/1.01      | X1 = X0 ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_430]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_557,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ v3_tex_2(X1,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | X0 != X2
% 2.43/1.01      | X0 = X1
% 2.43/1.01      | k1_xboole_0 != X1 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_431]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_558,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ v3_tex_2(k1_xboole_0,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | X0 = k1_xboole_0 ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5,plain,
% 2.43/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.43/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_572,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ v3_tex_2(k1_xboole_0,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | X0 = k1_xboole_0 ),
% 2.43/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_558,c_5]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_916,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | sK4 != sK4
% 2.43/1.01      | sK5 != k1_xboole_0
% 2.43/1.01      | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_572]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1057,plain,
% 2.43/1.01      ( ~ v2_tex_2(X0,sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
% 2.43/1.01      | sK5 != k1_xboole_0
% 2.43/1.01      | k1_xboole_0 = X0 ),
% 2.43/1.01      inference(equality_resolution_simp,[status(thm)],[c_916]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1840,plain,
% 2.43/1.01      ( sK5 != k1_xboole_0
% 2.43/1.01      | k1_xboole_0 = X0
% 2.43/1.01      | v2_tex_2(X0,sK4) != iProver_top
% 2.43/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_1057]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3178,plain,
% 2.43/1.01      ( k1_xboole_0 = X0
% 2.43/1.01      | k1_xboole_0 != k1_xboole_0
% 2.43/1.01      | v2_tex_2(X0,sK4) != iProver_top
% 2.43/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.43/1.01      inference(demodulation,[status(thm)],[c_3080,c_1840]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3187,plain,
% 2.43/1.01      ( k1_xboole_0 = X0
% 2.43/1.01      | v2_tex_2(X0,sK4) != iProver_top
% 2.43/1.01      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4))) != iProver_top ),
% 2.43/1.01      inference(equality_resolution_simp,[status(thm)],[c_3178]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4659,plain,
% 2.43/1.01      ( k1_tarski(sK1(sK2(sK4))) = k1_xboole_0
% 2.43/1.01      | v2_tex_2(k1_tarski(sK1(sK2(sK4))),sK4) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_4650,c_3187]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_21,plain,
% 2.43/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.43/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | ~ v2_pre_topc(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0) ),
% 2.43/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_295,plain,
% 2.43/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
% 2.43/1.01      | ~ m1_subset_1(X1,u1_struct_0(X0))
% 2.43/1.01      | v2_struct_0(X0)
% 2.43/1.01      | ~ l1_pre_topc(X0)
% 2.43/1.01      | sK4 != X0 ),
% 2.43/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_296,plain,
% 2.43/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4))
% 2.43/1.01      | v2_struct_0(sK4)
% 2.43/1.01      | ~ l1_pre_topc(sK4) ),
% 2.43/1.01      inference(unflattening,[status(thm)],[c_295]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_300,plain,
% 2.43/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4)
% 2.43/1.01      | ~ m1_subset_1(X0,u1_struct_0(sK4)) ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_296,c_27,c_25]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_1850,plain,
% 2.43/1.01      ( v2_tex_2(k6_domain_1(u1_struct_0(sK4),X0),sK4) = iProver_top
% 2.43/1.01      | m1_subset_1(X0,u1_struct_0(sK4)) != iProver_top ),
% 2.43/1.01      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_3865,plain,
% 2.43/1.01      ( v2_tex_2(k1_tarski(sK1(sK2(sK4))),sK4) = iProver_top
% 2.43/1.01      | m1_subset_1(sK1(sK2(sK4)),u1_struct_0(sK4)) != iProver_top ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_3861,c_1850]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5024,plain,
% 2.43/1.01      ( k1_tarski(sK1(sK2(sK4))) = k1_xboole_0 ),
% 2.43/1.01      inference(global_propositional_subsumption,
% 2.43/1.01                [status(thm)],
% 2.43/1.01                [c_4659,c_27,c_25,c_24,c_325,c_2020,c_2066,c_2194,c_2748,
% 2.43/1.01                 c_3435,c_3865]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2,plain,
% 2.43/1.01      ( k2_xboole_0(X0,k1_xboole_0) = X0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_4,plain,
% 2.43/1.01      ( k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
% 2.43/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_2360,plain,
% 2.43/1.01      ( k1_tarski(X0) != k1_xboole_0 ),
% 2.43/1.01      inference(superposition,[status(thm)],[c_2,c_4]) ).
% 2.43/1.01  
% 2.43/1.01  cnf(c_5027,plain,
% 2.43/1.01      ( $false ),
% 2.43/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_5024,c_2360]) ).
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.43/1.01  
% 2.43/1.01  ------                               Statistics
% 2.43/1.01  
% 2.43/1.01  ------ General
% 2.43/1.01  
% 2.43/1.01  abstr_ref_over_cycles:                  0
% 2.43/1.01  abstr_ref_under_cycles:                 0
% 2.43/1.01  gc_basic_clause_elim:                   0
% 2.43/1.01  forced_gc_time:                         0
% 2.43/1.01  parsing_time:                           0.017
% 2.43/1.01  unif_index_cands_time:                  0.
% 2.43/1.01  unif_index_add_time:                    0.
% 2.43/1.01  orderings_time:                         0.
% 2.43/1.01  out_proof_time:                         0.012
% 2.43/1.01  total_time:                             0.157
% 2.43/1.01  num_of_symbols:                         54
% 2.43/1.01  num_of_terms:                           2852
% 2.43/1.01  
% 2.43/1.01  ------ Preprocessing
% 2.43/1.01  
% 2.43/1.01  num_of_splits:                          3
% 2.43/1.01  num_of_split_atoms:                     1
% 2.43/1.01  num_of_reused_defs:                     2
% 2.43/1.01  num_eq_ax_congr_red:                    28
% 2.43/1.01  num_of_sem_filtered_clauses:            1
% 2.43/1.01  num_of_subtypes:                        0
% 2.43/1.01  monotx_restored_types:                  0
% 2.43/1.01  sat_num_of_epr_types:                   0
% 2.43/1.01  sat_num_of_non_cyclic_types:            0
% 2.43/1.01  sat_guarded_non_collapsed_types:        0
% 2.43/1.01  num_pure_diseq_elim:                    0
% 2.43/1.01  simp_replaced_by:                       0
% 2.43/1.01  res_preprocessed:                       121
% 2.43/1.01  prep_upred:                             0
% 2.43/1.01  prep_unflattend:                        75
% 2.43/1.01  smt_new_axioms:                         0
% 2.43/1.01  pred_elim_cands:                        4
% 2.43/1.01  pred_elim:                              5
% 2.43/1.01  pred_elim_cl:                           6
% 2.43/1.01  pred_elim_cycles:                       11
% 2.43/1.01  merged_defs:                            0
% 2.43/1.01  merged_defs_ncl:                        0
% 2.43/1.01  bin_hyper_res:                          0
% 2.43/1.01  prep_cycles:                            4
% 2.43/1.01  pred_elim_time:                         0.017
% 2.43/1.01  splitting_time:                         0.
% 2.43/1.01  sem_filter_time:                        0.
% 2.43/1.01  monotx_time:                            0.
% 2.43/1.01  subtype_inf_time:                       0.
% 2.43/1.01  
% 2.43/1.01  ------ Problem properties
% 2.43/1.01  
% 2.43/1.01  clauses:                                25
% 2.43/1.01  conjectures:                            2
% 2.43/1.01  epr:                                    3
% 2.43/1.01  horn:                                   19
% 2.43/1.01  ground:                                 8
% 2.43/1.01  unary:                                  8
% 2.43/1.01  binary:                                 4
% 2.43/1.01  lits:                                   59
% 2.43/1.01  lits_eq:                                14
% 2.43/1.01  fd_pure:                                0
% 2.43/1.01  fd_pseudo:                              0
% 2.43/1.01  fd_cond:                                7
% 2.43/1.01  fd_pseudo_cond:                         0
% 2.43/1.01  ac_symbols:                             0
% 2.43/1.01  
% 2.43/1.01  ------ Propositional Solver
% 2.43/1.01  
% 2.43/1.01  prop_solver_calls:                      27
% 2.43/1.01  prop_fast_solver_calls:                 997
% 2.43/1.01  smt_solver_calls:                       0
% 2.43/1.01  smt_fast_solver_calls:                  0
% 2.43/1.01  prop_num_of_clauses:                    1408
% 2.43/1.01  prop_preprocess_simplified:             5214
% 2.43/1.01  prop_fo_subsumed:                       38
% 2.43/1.01  prop_solver_time:                       0.
% 2.43/1.01  smt_solver_time:                        0.
% 2.43/1.01  smt_fast_solver_time:                   0.
% 2.43/1.01  prop_fast_solver_time:                  0.
% 2.43/1.01  prop_unsat_core_time:                   0.
% 2.43/1.01  
% 2.43/1.01  ------ QBF
% 2.43/1.01  
% 2.43/1.01  qbf_q_res:                              0
% 2.43/1.01  qbf_num_tautologies:                    0
% 2.43/1.01  qbf_prep_cycles:                        0
% 2.43/1.01  
% 2.43/1.01  ------ BMC1
% 2.43/1.01  
% 2.43/1.01  bmc1_current_bound:                     -1
% 2.43/1.01  bmc1_last_solved_bound:                 -1
% 2.43/1.01  bmc1_unsat_core_size:                   -1
% 2.43/1.01  bmc1_unsat_core_parents_size:           -1
% 2.43/1.01  bmc1_merge_next_fun:                    0
% 2.43/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.43/1.01  
% 2.43/1.01  ------ Instantiation
% 2.43/1.01  
% 2.43/1.01  inst_num_of_clauses:                    470
% 2.43/1.01  inst_num_in_passive:                    72
% 2.43/1.01  inst_num_in_active:                     249
% 2.43/1.01  inst_num_in_unprocessed:                149
% 2.43/1.01  inst_num_of_loops:                      300
% 2.43/1.01  inst_num_of_learning_restarts:          0
% 2.43/1.01  inst_num_moves_active_passive:          49
% 2.43/1.01  inst_lit_activity:                      0
% 2.43/1.01  inst_lit_activity_moves:                0
% 2.43/1.01  inst_num_tautologies:                   0
% 2.43/1.01  inst_num_prop_implied:                  0
% 2.43/1.01  inst_num_existing_simplified:           0
% 2.43/1.01  inst_num_eq_res_simplified:             0
% 2.43/1.01  inst_num_child_elim:                    0
% 2.43/1.01  inst_num_of_dismatching_blockings:      99
% 2.43/1.01  inst_num_of_non_proper_insts:           400
% 2.43/1.01  inst_num_of_duplicates:                 0
% 2.43/1.01  inst_inst_num_from_inst_to_res:         0
% 2.43/1.01  inst_dismatching_checking_time:         0.
% 2.43/1.01  
% 2.43/1.01  ------ Resolution
% 2.43/1.01  
% 2.43/1.01  res_num_of_clauses:                     0
% 2.43/1.01  res_num_in_passive:                     0
% 2.43/1.01  res_num_in_active:                      0
% 2.43/1.01  res_num_of_loops:                       125
% 2.43/1.01  res_forward_subset_subsumed:            44
% 2.43/1.01  res_backward_subset_subsumed:           0
% 2.43/1.01  res_forward_subsumed:                   0
% 2.43/1.01  res_backward_subsumed:                  0
% 2.43/1.01  res_forward_subsumption_resolution:     5
% 2.43/1.01  res_backward_subsumption_resolution:    2
% 2.43/1.01  res_clause_to_clause_subsumption:       174
% 2.43/1.01  res_orphan_elimination:                 0
% 2.43/1.01  res_tautology_del:                      40
% 2.43/1.01  res_num_eq_res_simplified:              1
% 2.43/1.01  res_num_sel_changes:                    0
% 2.43/1.01  res_moves_from_active_to_pass:          0
% 2.43/1.01  
% 2.43/1.01  ------ Superposition
% 2.43/1.01  
% 2.43/1.01  sup_time_total:                         0.
% 2.43/1.01  sup_time_generating:                    0.
% 2.43/1.01  sup_time_sim_full:                      0.
% 2.43/1.01  sup_time_sim_immed:                     0.
% 2.43/1.01  
% 2.43/1.01  sup_num_of_clauses:                     76
% 2.43/1.01  sup_num_in_active:                      50
% 2.43/1.01  sup_num_in_passive:                     26
% 2.43/1.01  sup_num_of_loops:                       59
% 2.43/1.01  sup_fw_superposition:                   47
% 2.43/1.01  sup_bw_superposition:                   30
% 2.43/1.01  sup_immediate_simplified:               6
% 2.43/1.01  sup_given_eliminated:                   1
% 2.43/1.01  comparisons_done:                       0
% 2.43/1.01  comparisons_avoided:                    18
% 2.43/1.01  
% 2.43/1.01  ------ Simplifications
% 2.43/1.01  
% 2.43/1.01  
% 2.43/1.01  sim_fw_subset_subsumed:                 3
% 2.43/1.01  sim_bw_subset_subsumed:                 5
% 2.43/1.01  sim_fw_subsumed:                        2
% 2.43/1.01  sim_bw_subsumed:                        0
% 2.43/1.01  sim_fw_subsumption_res:                 1
% 2.43/1.01  sim_bw_subsumption_res:                 0
% 2.43/1.01  sim_tautology_del:                      4
% 2.43/1.01  sim_eq_tautology_del:                   4
% 2.43/1.01  sim_eq_res_simp:                        1
% 2.43/1.01  sim_fw_demodulated:                     0
% 2.43/1.01  sim_bw_demodulated:                     6
% 2.43/1.01  sim_light_normalised:                   2
% 2.43/1.01  sim_joinable_taut:                      0
% 2.43/1.01  sim_joinable_simp:                      0
% 2.43/1.01  sim_ac_normalised:                      0
% 2.43/1.01  sim_smt_subsumption:                    0
% 2.43/1.01  
%------------------------------------------------------------------------------
