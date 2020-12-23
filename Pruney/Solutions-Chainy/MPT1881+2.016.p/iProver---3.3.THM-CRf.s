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
% DateTime   : Thu Dec  3 12:27:13 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 842 expanded)
%              Number of clauses        :   78 ( 233 expanded)
%              Number of leaves         :   18 ( 189 expanded)
%              Depth                    :   21
%              Number of atoms          :  565 (4827 expanded)
%              Number of equality atoms :  134 ( 331 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
            | ~ v3_tex_2(X1,X0) )
          & ( ~ v1_subset_1(X1,u1_struct_0(X0))
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( v1_subset_1(sK3,u1_struct_0(X0))
          | ~ v3_tex_2(sK3,X0) )
        & ( ~ v1_subset_1(sK3,u1_struct_0(X0))
          | v3_tex_2(sK3,X0) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( v1_subset_1(X1,u1_struct_0(X0))
              | ~ v3_tex_2(X1,X0) )
            & ( ~ v1_subset_1(X1,u1_struct_0(X0))
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(sK2))
            | ~ v3_tex_2(X1,sK2) )
          & ( ~ v1_subset_1(X1,u1_struct_0(sK2))
            | v3_tex_2(X1,sK2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v1_tdlat_3(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ( v1_subset_1(sK3,u1_struct_0(sK2))
      | ~ v3_tex_2(sK3,sK2) )
    & ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
      | v3_tex_2(sK3,sK2) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v1_tdlat_3(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).

fof(f77,plain,
    ( ~ v1_subset_1(sK3,u1_struct_0(sK2))
    | v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f18])).

fof(f35,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,X0) )
     => ( ~ r2_hidden(sK0(X0,X1,X2),X2)
        & r2_hidden(sK0(X0,X1,X2),X1)
        & m1_subset_1(sK0(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ( ~ r2_hidden(sK0(X0,X1,X2),X2)
            & r2_hidden(sK0(X0,X1,X2),X1)
            & m1_subset_1(sK0(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | r2_hidden(sK0(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r2_hidden(sK0(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f39,plain,(
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
    inference(flattening,[],[f39])).

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
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK1(X0,X1) != X1
        & r1_tarski(X1,sK1(X0,X1))
        & v2_tex_2(sK1(X0,X1),X0)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK1(X0,X1) != X1
                & r1_tarski(X1,sK1(X0,X1))
                & v2_tex_2(sK1(X0,X1),X0)
                & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f65,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f74,plain,(
    v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f72,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f73,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f78,plain,
    ( v1_subset_1(sK3,u1_struct_0(sK2))
    | ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_tops_1(X1,X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_13,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_24,negated_conjecture,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_222,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_24])).

cnf(c_496,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X1 = X0
    | u1_struct_0(sK2) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_222])).

cnf(c_497,plain,
    ( v3_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | u1_struct_0(sK2) = sK3 ),
    inference(unflattening,[status(thm)],[c_496])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_499,plain,
    ( v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_497,c_25])).

cnf(c_1805,plain,
    ( u1_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_8,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_7,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_384,plain,
    ( ~ l1_pre_topc(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_8,c_7])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_534,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_384,c_26])).

cnf(c_535,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_1828,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1805,c_535])).

cnf(c_1,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1813,plain,
    ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1825,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1813,c_0])).

cnf(c_4,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X2,X0,X1),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1810,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X2,X0,X1),X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1808,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1822,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1808,c_535])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1812,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2359,plain,
    ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_1812])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X2,X0,X1),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1811,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2801,plain,
    ( r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
    | r2_hidden(sK0(X1,X0,k2_struct_0(sK2)),sK3) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2359,c_1811])).

cnf(c_3547,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(X0)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1810,c_2801])).

cnf(c_3604,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_3547])).

cnf(c_3607,plain,
    ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3604,c_1822])).

cnf(c_19,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_553,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ r1_tarski(X2,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | X2 = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_554,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_21,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v1_tdlat_3(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_27,negated_conjecture,
    ( v1_tdlat_3(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_400,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_401,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_28,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_405,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_tex_2(X0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_401,c_29,c_28,c_26])).

cnf(c_406,plain,
    ( v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(renaming,[status(thm)],[c_405])).

cnf(c_558,plain,
    ( ~ v3_tex_2(X1,sK2)
    | ~ r1_tarski(X1,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | X1 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_29,c_28,c_26,c_401])).

cnf(c_559,plain,
    ( ~ v3_tex_2(X0,sK2)
    | ~ r1_tarski(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | X0 = X1 ),
    inference(renaming,[status(thm)],[c_558])).

cnf(c_1803,plain,
    ( X0 = X1
    | v3_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_559])).

cnf(c_1898,plain,
    ( X0 = X1
    | v3_tex_2(X1,sK2) != iProver_top
    | r1_tarski(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1803,c_535])).

cnf(c_2254,plain,
    ( k2_struct_0(sK2) = X0
    | v3_tex_2(X0,sK2) != iProver_top
    | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_1898])).

cnf(c_2618,plain,
    ( k2_struct_0(sK2) = sK3
    | v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1822,c_2254])).

cnf(c_6,plain,
    ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_23,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_224,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | v1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(prop_impl,[status(thm)],[c_23])).

cnf(c_484,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | u1_struct_0(sK2) != X0
    | k2_subset_1(X0) != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_224])).

cnf(c_485,plain,
    ( ~ v3_tex_2(sK3,sK2)
    | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
    inference(unflattening,[status(thm)],[c_484])).

cnf(c_1806,plain,
    ( k2_subset_1(u1_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_485])).

cnf(c_1833,plain,
    ( k2_subset_1(k2_struct_0(sK2)) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1806,c_535])).

cnf(c_1834,plain,
    ( k2_struct_0(sK2) != sK3
    | v3_tex_2(sK3,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1833,c_0])).

cnf(c_2656,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top
    | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_1834])).

cnf(c_3612,plain,
    ( v3_tex_2(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3607,c_2656])).

cnf(c_3994,plain,
    ( k2_struct_0(sK2) = sK3 ),
    inference(superposition,[status(thm)],[c_1828,c_3612])).

cnf(c_9,plain,
    ( ~ l1_pre_topc(X0)
    | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_539,plain,
    ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_26])).

cnf(c_540,plain,
    ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_539])).

cnf(c_11,plain,
    ( v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_421,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_28])).

cnf(c_422,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_426,plain,
    ( v3_tex_2(X0,sK2)
    | ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_422,c_29,c_28,c_26,c_401])).

cnf(c_447,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X2)
    | X0 != X1
    | k2_pre_topc(X2,X1) != u1_struct_0(X2)
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_426])).

cnf(c_448,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_452,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_tex_2(X0,sK2)
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_448,c_26])).

cnf(c_453,plain,
    ( v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
    inference(renaming,[status(thm)],[c_452])).

cnf(c_1807,plain,
    ( k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_453])).

cnf(c_1860,plain,
    ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1807,c_535])).

cnf(c_2014,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
    | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_540,c_1860])).

cnf(c_2255,plain,
    ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_2014])).

cnf(c_4014,plain,
    ( v3_tex_2(sK3,sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3994,c_2255])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4014,c_3604,c_2656,c_1822])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.73/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/0.99  
% 2.73/0.99  ------  iProver source info
% 2.73/0.99  
% 2.73/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.73/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/0.99  git: non_committed_changes: false
% 2.73/0.99  git: last_make_outside_of_git: false
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     num_symb
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       true
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  ------ Parsing...
% 2.73/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe:8:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/0.99  ------ Proving...
% 2.73/0.99  ------ Problem Properties 
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  clauses                                 18
% 2.73/0.99  conjectures                             1
% 2.73/0.99  EPR                                     0
% 2.73/0.99  Horn                                    13
% 2.73/0.99  unary                                   6
% 2.73/0.99  binary                                  2
% 2.73/0.99  lits                                    45
% 2.73/0.99  lits eq                                 10
% 2.73/0.99  fd_pure                                 0
% 2.73/0.99  fd_pseudo                               0
% 2.73/0.99  fd_cond                                 0
% 2.73/0.99  fd_pseudo_cond                          1
% 2.73/0.99  AC symbols                              0
% 2.73/0.99  
% 2.73/0.99  ------ Schedule dynamic 5 is on 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ 
% 2.73/0.99  Current options:
% 2.73/0.99  ------ 
% 2.73/0.99  
% 2.73/0.99  ------ Input Options
% 2.73/0.99  
% 2.73/0.99  --out_options                           all
% 2.73/0.99  --tptp_safe_out                         true
% 2.73/0.99  --problem_path                          ""
% 2.73/0.99  --include_path                          ""
% 2.73/0.99  --clausifier                            res/vclausify_rel
% 2.73/0.99  --clausifier_options                    --mode clausify
% 2.73/0.99  --stdin                                 false
% 2.73/0.99  --stats_out                             all
% 2.73/0.99  
% 2.73/0.99  ------ General Options
% 2.73/0.99  
% 2.73/0.99  --fof                                   false
% 2.73/0.99  --time_out_real                         305.
% 2.73/0.99  --time_out_virtual                      -1.
% 2.73/0.99  --symbol_type_check                     false
% 2.73/0.99  --clausify_out                          false
% 2.73/0.99  --sig_cnt_out                           false
% 2.73/0.99  --trig_cnt_out                          false
% 2.73/0.99  --trig_cnt_out_tolerance                1.
% 2.73/0.99  --trig_cnt_out_sk_spl                   false
% 2.73/0.99  --abstr_cl_out                          false
% 2.73/0.99  
% 2.73/0.99  ------ Global Options
% 2.73/0.99  
% 2.73/0.99  --schedule                              default
% 2.73/0.99  --add_important_lit                     false
% 2.73/0.99  --prop_solver_per_cl                    1000
% 2.73/0.99  --min_unsat_core                        false
% 2.73/0.99  --soft_assumptions                      false
% 2.73/0.99  --soft_lemma_size                       3
% 2.73/0.99  --prop_impl_unit_size                   0
% 2.73/0.99  --prop_impl_unit                        []
% 2.73/0.99  --share_sel_clauses                     true
% 2.73/0.99  --reset_solvers                         false
% 2.73/0.99  --bc_imp_inh                            [conj_cone]
% 2.73/0.99  --conj_cone_tolerance                   3.
% 2.73/0.99  --extra_neg_conj                        none
% 2.73/0.99  --large_theory_mode                     true
% 2.73/0.99  --prolific_symb_bound                   200
% 2.73/0.99  --lt_threshold                          2000
% 2.73/0.99  --clause_weak_htbl                      true
% 2.73/0.99  --gc_record_bc_elim                     false
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing Options
% 2.73/0.99  
% 2.73/0.99  --preprocessing_flag                    true
% 2.73/0.99  --time_out_prep_mult                    0.1
% 2.73/0.99  --splitting_mode                        input
% 2.73/0.99  --splitting_grd                         true
% 2.73/0.99  --splitting_cvd                         false
% 2.73/0.99  --splitting_cvd_svl                     false
% 2.73/0.99  --splitting_nvd                         32
% 2.73/0.99  --sub_typing                            true
% 2.73/0.99  --prep_gs_sim                           true
% 2.73/0.99  --prep_unflatten                        true
% 2.73/0.99  --prep_res_sim                          true
% 2.73/0.99  --prep_upred                            true
% 2.73/0.99  --prep_sem_filter                       exhaustive
% 2.73/0.99  --prep_sem_filter_out                   false
% 2.73/0.99  --pred_elim                             true
% 2.73/0.99  --res_sim_input                         true
% 2.73/0.99  --eq_ax_congr_red                       true
% 2.73/0.99  --pure_diseq_elim                       true
% 2.73/0.99  --brand_transform                       false
% 2.73/0.99  --non_eq_to_eq                          false
% 2.73/0.99  --prep_def_merge                        true
% 2.73/0.99  --prep_def_merge_prop_impl              false
% 2.73/0.99  --prep_def_merge_mbd                    true
% 2.73/0.99  --prep_def_merge_tr_red                 false
% 2.73/0.99  --prep_def_merge_tr_cl                  false
% 2.73/0.99  --smt_preprocessing                     true
% 2.73/0.99  --smt_ac_axioms                         fast
% 2.73/0.99  --preprocessed_out                      false
% 2.73/0.99  --preprocessed_stats                    false
% 2.73/0.99  
% 2.73/0.99  ------ Abstraction refinement Options
% 2.73/0.99  
% 2.73/0.99  --abstr_ref                             []
% 2.73/0.99  --abstr_ref_prep                        false
% 2.73/0.99  --abstr_ref_until_sat                   false
% 2.73/0.99  --abstr_ref_sig_restrict                funpre
% 2.73/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/0.99  --abstr_ref_under                       []
% 2.73/0.99  
% 2.73/0.99  ------ SAT Options
% 2.73/0.99  
% 2.73/0.99  --sat_mode                              false
% 2.73/0.99  --sat_fm_restart_options                ""
% 2.73/0.99  --sat_gr_def                            false
% 2.73/0.99  --sat_epr_types                         true
% 2.73/0.99  --sat_non_cyclic_types                  false
% 2.73/0.99  --sat_finite_models                     false
% 2.73/0.99  --sat_fm_lemmas                         false
% 2.73/0.99  --sat_fm_prep                           false
% 2.73/0.99  --sat_fm_uc_incr                        true
% 2.73/0.99  --sat_out_model                         small
% 2.73/0.99  --sat_out_clauses                       false
% 2.73/0.99  
% 2.73/0.99  ------ QBF Options
% 2.73/0.99  
% 2.73/0.99  --qbf_mode                              false
% 2.73/0.99  --qbf_elim_univ                         false
% 2.73/0.99  --qbf_dom_inst                          none
% 2.73/0.99  --qbf_dom_pre_inst                      false
% 2.73/0.99  --qbf_sk_in                             false
% 2.73/0.99  --qbf_pred_elim                         true
% 2.73/0.99  --qbf_split                             512
% 2.73/0.99  
% 2.73/0.99  ------ BMC1 Options
% 2.73/0.99  
% 2.73/0.99  --bmc1_incremental                      false
% 2.73/0.99  --bmc1_axioms                           reachable_all
% 2.73/0.99  --bmc1_min_bound                        0
% 2.73/0.99  --bmc1_max_bound                        -1
% 2.73/0.99  --bmc1_max_bound_default                -1
% 2.73/0.99  --bmc1_symbol_reachability              true
% 2.73/0.99  --bmc1_property_lemmas                  false
% 2.73/0.99  --bmc1_k_induction                      false
% 2.73/0.99  --bmc1_non_equiv_states                 false
% 2.73/0.99  --bmc1_deadlock                         false
% 2.73/0.99  --bmc1_ucm                              false
% 2.73/0.99  --bmc1_add_unsat_core                   none
% 2.73/0.99  --bmc1_unsat_core_children              false
% 2.73/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/0.99  --bmc1_out_stat                         full
% 2.73/0.99  --bmc1_ground_init                      false
% 2.73/0.99  --bmc1_pre_inst_next_state              false
% 2.73/0.99  --bmc1_pre_inst_state                   false
% 2.73/0.99  --bmc1_pre_inst_reach_state             false
% 2.73/0.99  --bmc1_out_unsat_core                   false
% 2.73/0.99  --bmc1_aig_witness_out                  false
% 2.73/0.99  --bmc1_verbose                          false
% 2.73/0.99  --bmc1_dump_clauses_tptp                false
% 2.73/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.73/0.99  --bmc1_dump_file                        -
% 2.73/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.73/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.73/0.99  --bmc1_ucm_extend_mode                  1
% 2.73/0.99  --bmc1_ucm_init_mode                    2
% 2.73/0.99  --bmc1_ucm_cone_mode                    none
% 2.73/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.73/0.99  --bmc1_ucm_relax_model                  4
% 2.73/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.73/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/0.99  --bmc1_ucm_layered_model                none
% 2.73/0.99  --bmc1_ucm_max_lemma_size               10
% 2.73/0.99  
% 2.73/0.99  ------ AIG Options
% 2.73/0.99  
% 2.73/0.99  --aig_mode                              false
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation Options
% 2.73/0.99  
% 2.73/0.99  --instantiation_flag                    true
% 2.73/0.99  --inst_sos_flag                         false
% 2.73/0.99  --inst_sos_phase                        true
% 2.73/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/0.99  --inst_lit_sel_side                     none
% 2.73/0.99  --inst_solver_per_active                1400
% 2.73/0.99  --inst_solver_calls_frac                1.
% 2.73/0.99  --inst_passive_queue_type               priority_queues
% 2.73/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/0.99  --inst_passive_queues_freq              [25;2]
% 2.73/0.99  --inst_dismatching                      true
% 2.73/0.99  --inst_eager_unprocessed_to_passive     true
% 2.73/0.99  --inst_prop_sim_given                   true
% 2.73/0.99  --inst_prop_sim_new                     false
% 2.73/0.99  --inst_subs_new                         false
% 2.73/0.99  --inst_eq_res_simp                      false
% 2.73/0.99  --inst_subs_given                       false
% 2.73/0.99  --inst_orphan_elimination               true
% 2.73/0.99  --inst_learning_loop_flag               true
% 2.73/0.99  --inst_learning_start                   3000
% 2.73/0.99  --inst_learning_factor                  2
% 2.73/0.99  --inst_start_prop_sim_after_learn       3
% 2.73/0.99  --inst_sel_renew                        solver
% 2.73/0.99  --inst_lit_activity_flag                true
% 2.73/0.99  --inst_restr_to_given                   false
% 2.73/0.99  --inst_activity_threshold               500
% 2.73/0.99  --inst_out_proof                        true
% 2.73/0.99  
% 2.73/0.99  ------ Resolution Options
% 2.73/0.99  
% 2.73/0.99  --resolution_flag                       false
% 2.73/0.99  --res_lit_sel                           adaptive
% 2.73/0.99  --res_lit_sel_side                      none
% 2.73/0.99  --res_ordering                          kbo
% 2.73/0.99  --res_to_prop_solver                    active
% 2.73/0.99  --res_prop_simpl_new                    false
% 2.73/0.99  --res_prop_simpl_given                  true
% 2.73/0.99  --res_passive_queue_type                priority_queues
% 2.73/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/0.99  --res_passive_queues_freq               [15;5]
% 2.73/0.99  --res_forward_subs                      full
% 2.73/0.99  --res_backward_subs                     full
% 2.73/0.99  --res_forward_subs_resolution           true
% 2.73/0.99  --res_backward_subs_resolution          true
% 2.73/0.99  --res_orphan_elimination                true
% 2.73/0.99  --res_time_limit                        2.
% 2.73/0.99  --res_out_proof                         true
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Options
% 2.73/0.99  
% 2.73/0.99  --superposition_flag                    true
% 2.73/0.99  --sup_passive_queue_type                priority_queues
% 2.73/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.73/0.99  --demod_completeness_check              fast
% 2.73/0.99  --demod_use_ground                      true
% 2.73/0.99  --sup_to_prop_solver                    passive
% 2.73/0.99  --sup_prop_simpl_new                    true
% 2.73/0.99  --sup_prop_simpl_given                  true
% 2.73/0.99  --sup_fun_splitting                     false
% 2.73/0.99  --sup_smt_interval                      50000
% 2.73/0.99  
% 2.73/0.99  ------ Superposition Simplification Setup
% 2.73/0.99  
% 2.73/0.99  --sup_indices_passive                   []
% 2.73/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_full_bw                           [BwDemod]
% 2.73/0.99  --sup_immed_triv                        [TrivRules]
% 2.73/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_immed_bw_main                     []
% 2.73/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/0.99  
% 2.73/0.99  ------ Combination Options
% 2.73/0.99  
% 2.73/0.99  --comb_res_mult                         3
% 2.73/0.99  --comb_sup_mult                         2
% 2.73/0.99  --comb_inst_mult                        10
% 2.73/0.99  
% 2.73/0.99  ------ Debug Options
% 2.73/0.99  
% 2.73/0.99  --dbg_backtrace                         false
% 2.73/0.99  --dbg_dump_prop_clauses                 false
% 2.73/0.99  --dbg_dump_prop_clauses_file            -
% 2.73/0.99  --dbg_out_stat                          false
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  ------ Proving...
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS status Theorem for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  fof(f11,axiom,(
% 2.73/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f26,plain,(
% 2.73/0.99    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f11])).
% 2.73/0.99  
% 2.73/0.99  fof(f38,plain,(
% 2.73/0.99    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(nnf_transformation,[],[f26])).
% 2.73/0.99  
% 2.73/0.99  fof(f63,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f38])).
% 2.73/0.99  
% 2.73/0.99  fof(f15,conjecture,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f16,negated_conjecture,(
% 2.73/0.99    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 2.73/0.99    inference(negated_conjecture,[],[f15])).
% 2.73/0.99  
% 2.73/0.99  fof(f33,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f16])).
% 2.73/0.99  
% 2.73/0.99  fof(f34,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f33])).
% 2.73/0.99  
% 2.73/0.99  fof(f44,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : (((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f34])).
% 2.73/0.99  
% 2.73/0.99  fof(f45,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f44])).
% 2.73/0.99  
% 2.73/0.99  fof(f47,plain,(
% 2.73/0.99    ( ! [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => ((v1_subset_1(sK3,u1_struct_0(X0)) | ~v3_tex_2(sK3,X0)) & (~v1_subset_1(sK3,u1_struct_0(X0)) | v3_tex_2(sK3,X0)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f46,plain,(
% 2.73/0.99    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) | ~v3_tex_2(X1,X0)) & (~v1_subset_1(X1,u1_struct_0(X0)) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((v1_subset_1(X1,u1_struct_0(sK2)) | ~v3_tex_2(X1,sK2)) & (~v1_subset_1(X1,u1_struct_0(sK2)) | v3_tex_2(X1,sK2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f48,plain,(
% 2.73/0.99    ((v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)) & (~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v1_tdlat_3(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f47,f46])).
% 2.73/0.99  
% 2.73/0.99  fof(f77,plain,(
% 2.73/0.99    ~v1_subset_1(sK3,u1_struct_0(sK2)) | v3_tex_2(sK3,sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f76,plain,(
% 2.73/0.99    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f7,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f21,plain,(
% 2.73/0.99    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f7])).
% 2.73/0.99  
% 2.73/0.99  fof(f57,plain,(
% 2.73/0.99    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f21])).
% 2.73/0.99  
% 2.73/0.99  fof(f6,axiom,(
% 2.73/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f20,plain,(
% 2.73/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f6])).
% 2.73/0.99  
% 2.73/0.99  fof(f56,plain,(
% 2.73/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f20])).
% 2.73/0.99  
% 2.73/0.99  fof(f75,plain,(
% 2.73/0.99    l1_pre_topc(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f2,axiom,(
% 2.73/0.99    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f50,plain,(
% 2.73/0.99    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f2])).
% 2.73/0.99  
% 2.73/0.99  fof(f1,axiom,(
% 2.73/0.99    ! [X0] : k2_subset_1(X0) = X0),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f49,plain,(
% 2.73/0.99    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.73/0.99    inference(cnf_transformation,[],[f1])).
% 2.73/0.99  
% 2.73/0.99  fof(f4,axiom,(
% 2.73/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f18,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f4])).
% 2.73/0.99  
% 2.73/0.99  fof(f19,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(flattening,[],[f18])).
% 2.73/0.99  
% 2.73/0.99  fof(f35,plain,(
% 2.73/0.99    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) => (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f36,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | (~r2_hidden(sK0(X0,X1,X2),X2) & r2_hidden(sK0(X0,X1,X2),X1) & m1_subset_1(sK0(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f19,f35])).
% 2.73/0.99  
% 2.73/0.99  fof(f53,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | r2_hidden(sK0(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f3,axiom,(
% 2.73/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f17,plain,(
% 2.73/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f3])).
% 2.73/0.99  
% 2.73/0.99  fof(f51,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f17])).
% 2.73/0.99  
% 2.73/0.99  fof(f54,plain,(
% 2.73/0.99    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r2_hidden(sK0(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.73/0.99    inference(cnf_transformation,[],[f36])).
% 2.73/0.99  
% 2.73/0.99  fof(f12,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f27,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f12])).
% 2.73/0.99  
% 2.73/0.99  fof(f28,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(flattening,[],[f27])).
% 2.73/0.99  
% 2.73/0.99  fof(f39,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f28])).
% 2.73/0.99  
% 2.73/0.99  fof(f40,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(flattening,[],[f39])).
% 2.73/0.99  
% 2.73/0.99  fof(f41,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(rectify,[],[f40])).
% 2.73/0.99  
% 2.73/0.99  fof(f42,plain,(
% 2.73/0.99    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.73/0.99    introduced(choice_axiom,[])).
% 2.73/0.99  
% 2.73/0.99  fof(f43,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK1(X0,X1) != X1 & r1_tarski(X1,sK1(X0,X1)) & v2_tex_2(sK1(X0,X1),X0) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 2.73/0.99  
% 2.73/0.99  fof(f65,plain,(
% 2.73/0.99    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f43])).
% 2.73/0.99  
% 2.73/0.99  fof(f13,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f29,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f13])).
% 2.73/0.99  
% 2.73/0.99  fof(f30,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f29])).
% 2.73/0.99  
% 2.73/0.99  fof(f70,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f30])).
% 2.73/0.99  
% 2.73/0.99  fof(f74,plain,(
% 2.73/0.99    v1_tdlat_3(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f72,plain,(
% 2.73/0.99    ~v2_struct_0(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f73,plain,(
% 2.73/0.99    v2_pre_topc(sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f5,axiom,(
% 2.73/0.99    ! [X0] : ~v1_subset_1(k2_subset_1(X0),X0)),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f55,plain,(
% 2.73/0.99    ( ! [X0] : (~v1_subset_1(k2_subset_1(X0),X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f5])).
% 2.73/0.99  
% 2.73/0.99  fof(f78,plain,(
% 2.73/0.99    v1_subset_1(sK3,u1_struct_0(sK2)) | ~v3_tex_2(sK3,sK2)),
% 2.73/0.99    inference(cnf_transformation,[],[f48])).
% 2.73/0.99  
% 2.73/0.99  fof(f8,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f22,plain,(
% 2.73/0.99    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f8])).
% 2.73/0.99  
% 2.73/0.99  fof(f58,plain,(
% 2.73/0.99    ( ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f22])).
% 2.73/0.99  
% 2.73/0.99  fof(f10,axiom,(
% 2.73/0.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f25,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(ennf_transformation,[],[f10])).
% 2.73/0.99  
% 2.73/0.99  fof(f37,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.73/0.99    inference(nnf_transformation,[],[f25])).
% 2.73/0.99  
% 2.73/0.99  fof(f61,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f37])).
% 2.73/0.99  
% 2.73/0.99  fof(f14,axiom,(
% 2.73/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 2.73/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.73/0.99  
% 2.73/0.99  fof(f31,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.73/0.99    inference(ennf_transformation,[],[f14])).
% 2.73/0.99  
% 2.73/0.99  fof(f32,plain,(
% 2.73/0.99    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.73/0.99    inference(flattening,[],[f31])).
% 2.73/0.99  
% 2.73/0.99  fof(f71,plain,(
% 2.73/0.99    ( ! [X0,X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.73/0.99    inference(cnf_transformation,[],[f32])).
% 2.73/0.99  
% 2.73/0.99  cnf(c_13,plain,
% 2.73/0.99      ( v1_subset_1(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.73/0.99      | X0 = X1 ),
% 2.73/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_24,negated_conjecture,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_222,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) | ~ v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.73/0.99      inference(prop_impl,[status(thm)],[c_24]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_496,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.73/0.99      | X1 = X0
% 2.73/0.99      | u1_struct_0(sK2) != X1
% 2.73/0.99      | sK3 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_222]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_497,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2)
% 2.73/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | u1_struct_0(sK2) = sK3 ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_496]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_25,negated_conjecture,
% 2.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.73/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_499,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) | u1_struct_0(sK2) = sK3 ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_497,c_25]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1805,plain,
% 2.73/0.99      ( u1_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_8,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_7,plain,
% 2.73/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_384,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.73/0.99      inference(resolution,[status(thm)],[c_8,c_7]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_26,negated_conjecture,
% 2.73/0.99      ( l1_pre_topc(sK2) ),
% 2.73/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_534,plain,
% 2.73/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_384,c_26]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_535,plain,
% 2.73/0.99      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_534]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1828,plain,
% 2.73/0.99      ( k2_struct_0(sK2) = sK3 | v3_tex_2(sK3,sK2) = iProver_top ),
% 2.73/0.99      inference(demodulation,[status(thm)],[c_1805,c_535]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1,plain,
% 2.73/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1813,plain,
% 2.73/0.99      ( m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_0,plain,
% 2.73/0.99      ( k2_subset_1(X0) = X0 ),
% 2.73/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1825,plain,
% 2.73/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1813,c_0]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4,plain,
% 2.73/0.99      ( r1_tarski(X0,X1)
% 2.73/0.99      | r2_hidden(sK0(X2,X0,X1),X0)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1810,plain,
% 2.73/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.73/0.99      | r2_hidden(sK0(X2,X0,X1),X0) = iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 2.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1808,plain,
% 2.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1822,plain,
% 2.73/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) = iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1808,c_535]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2,plain,
% 2.73/0.99      ( ~ r2_hidden(X0,X1)
% 2.73/0.99      | r2_hidden(X0,X2)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1812,plain,
% 2.73/0.99      ( r2_hidden(X0,X1) != iProver_top
% 2.73/0.99      | r2_hidden(X0,X2) = iProver_top
% 2.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2359,plain,
% 2.73/0.99      ( r2_hidden(X0,k2_struct_0(sK2)) = iProver_top
% 2.73/0.99      | r2_hidden(X0,sK3) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1822,c_1812]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3,plain,
% 2.73/0.99      ( r1_tarski(X0,X1)
% 2.73/0.99      | ~ r2_hidden(sK0(X2,X0,X1),X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1811,plain,
% 2.73/0.99      ( r1_tarski(X0,X1) = iProver_top
% 2.73/0.99      | r2_hidden(sK0(X2,X0,X1),X1) != iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(X2)) != iProver_top
% 2.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(X2)) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2801,plain,
% 2.73/0.99      ( r1_tarski(X0,k2_struct_0(sK2)) = iProver_top
% 2.73/0.99      | r2_hidden(sK0(X1,X0,k2_struct_0(sK2)),sK3) != iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.73/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(X1)) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_2359,c_1811]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3547,plain,
% 2.73/0.99      ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
% 2.73/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(X0)) != iProver_top
% 2.73/0.99      | m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1810,c_2801]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3604,plain,
% 2.73/0.99      ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top
% 2.73/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1825,c_3547]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3607,plain,
% 2.73/0.99      ( r1_tarski(sK3,k2_struct_0(sK2)) = iProver_top ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_3604,c_1822]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_19,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,X1)
% 2.73/0.99      | ~ v3_tex_2(X2,X1)
% 2.73/0.99      | ~ r1_tarski(X2,X0)
% 2.73/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | X0 = X2 ),
% 2.73/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_553,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,X1)
% 2.73/0.99      | ~ v3_tex_2(X2,X1)
% 2.73/0.99      | ~ r1_tarski(X2,X0)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | X2 = X0
% 2.73/0.99      | sK2 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_554,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.73/0.99      | ~ v3_tex_2(X1,sK2)
% 2.73/0.99      | ~ r1_tarski(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | X1 = X0 ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_553]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_21,plain,
% 2.73/0.99      ( v2_tex_2(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ v1_tdlat_3(X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_27,negated_conjecture,
% 2.73/0.99      ( v1_tdlat_3(sK2) ),
% 2.73/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_400,plain,
% 2.73/0.99      ( v2_tex_2(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK2 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_401,plain,
% 2.73/0.99      ( v2_tex_2(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | v2_struct_0(sK2)
% 2.73/0.99      | ~ v2_pre_topc(sK2)
% 2.73/0.99      | ~ l1_pre_topc(sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_400]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_29,negated_conjecture,
% 2.73/0.99      ( ~ v2_struct_0(sK2) ),
% 2.73/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_28,negated_conjecture,
% 2.73/0.99      ( v2_pre_topc(sK2) ),
% 2.73/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_405,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | v2_tex_2(X0,sK2) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_401,c_29,c_28,c_26]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_406,plain,
% 2.73/0.99      ( v2_tex_2(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_405]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_558,plain,
% 2.73/0.99      ( ~ v3_tex_2(X1,sK2)
% 2.73/0.99      | ~ r1_tarski(X1,X0)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | X1 = X0 ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_554,c_29,c_28,c_26,c_401]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_559,plain,
% 2.73/0.99      ( ~ v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ r1_tarski(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | X0 = X1 ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_558]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1803,plain,
% 2.73/0.99      ( X0 = X1
% 2.73/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.73/0.99      | r1_tarski(X0,X1) != iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 2.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_559]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1898,plain,
% 2.73/0.99      ( X0 = X1
% 2.73/0.99      | v3_tex_2(X1,sK2) != iProver_top
% 2.73/0.99      | r1_tarski(X1,X0) != iProver_top
% 2.73/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1803,c_535]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2254,plain,
% 2.73/0.99      ( k2_struct_0(sK2) = X0
% 2.73/0.99      | v3_tex_2(X0,sK2) != iProver_top
% 2.73/0.99      | r1_tarski(X0,k2_struct_0(sK2)) != iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1825,c_1898]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2618,plain,
% 2.73/0.99      ( k2_struct_0(sK2) = sK3
% 2.73/0.99      | v3_tex_2(sK3,sK2) != iProver_top
% 2.73/0.99      | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1822,c_2254]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_6,plain,
% 2.73/0.99      ( ~ v1_subset_1(k2_subset_1(X0),X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_23,negated_conjecture,
% 2.73/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.73/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_224,plain,
% 2.73/0.99      ( ~ v3_tex_2(sK3,sK2) | v1_subset_1(sK3,u1_struct_0(sK2)) ),
% 2.73/0.99      inference(prop_impl,[status(thm)],[c_23]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_484,plain,
% 2.73/0.99      ( ~ v3_tex_2(sK3,sK2)
% 2.73/0.99      | u1_struct_0(sK2) != X0
% 2.73/0.99      | k2_subset_1(X0) != sK3 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_224]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_485,plain,
% 2.73/0.99      ( ~ v3_tex_2(sK3,sK2) | k2_subset_1(u1_struct_0(sK2)) != sK3 ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_484]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1806,plain,
% 2.73/0.99      ( k2_subset_1(u1_struct_0(sK2)) != sK3
% 2.73/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_485]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1833,plain,
% 2.73/0.99      ( k2_subset_1(k2_struct_0(sK2)) != sK3
% 2.73/0.99      | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1806,c_535]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1834,plain,
% 2.73/0.99      ( k2_struct_0(sK2) != sK3 | v3_tex_2(sK3,sK2) != iProver_top ),
% 2.73/0.99      inference(demodulation,[status(thm)],[c_1833,c_0]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2656,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) != iProver_top
% 2.73/0.99      | r1_tarski(sK3,k2_struct_0(sK2)) != iProver_top ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_2618,c_1834]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3612,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_3607,c_2656]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_3994,plain,
% 2.73/0.99      ( k2_struct_0(sK2) = sK3 ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1828,c_3612]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_9,plain,
% 2.73/0.99      ( ~ l1_pre_topc(X0)
% 2.73/0.99      | k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) ),
% 2.73/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_539,plain,
% 2.73/0.99      ( k2_pre_topc(X0,k2_struct_0(X0)) = k2_struct_0(X0) | sK2 != X0 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_26]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_540,plain,
% 2.73/0.99      ( k2_pre_topc(sK2,k2_struct_0(sK2)) = k2_struct_0(sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_539]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_11,plain,
% 2.73/0.99      ( v1_tops_1(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | k2_pre_topc(X1,X0) != u1_struct_0(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_22,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,X1)
% 2.73/0.99      | v3_tex_2(X0,X1)
% 2.73/0.99      | ~ v1_tops_1(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ v2_pre_topc(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1) ),
% 2.73/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_421,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,X1)
% 2.73/0.99      | v3_tex_2(X0,X1)
% 2.73/0.99      | ~ v1_tops_1(X0,X1)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 2.73/0.99      | v2_struct_0(X1)
% 2.73/0.99      | ~ l1_pre_topc(X1)
% 2.73/0.99      | sK2 != X1 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_28]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_422,plain,
% 2.73/0.99      ( ~ v2_tex_2(X0,sK2)
% 2.73/0.99      | v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ v1_tops_1(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | v2_struct_0(sK2)
% 2.73/0.99      | ~ l1_pre_topc(sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_421]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_426,plain,
% 2.73/0.99      ( v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ v1_tops_1(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_422,c_29,c_28,c_26,c_401]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_447,plain,
% 2.73/0.99      ( v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | ~ l1_pre_topc(X2)
% 2.73/0.99      | X0 != X1
% 2.73/0.99      | k2_pre_topc(X2,X1) != u1_struct_0(X2)
% 2.73/0.99      | sK2 != X2 ),
% 2.73/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_426]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_448,plain,
% 2.73/0.99      ( v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | ~ l1_pre_topc(sK2)
% 2.73/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.73/0.99      inference(unflattening,[status(thm)],[c_447]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_452,plain,
% 2.73/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | v3_tex_2(X0,sK2)
% 2.73/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.73/0.99      inference(global_propositional_subsumption,
% 2.73/0.99                [status(thm)],
% 2.73/0.99                [c_448,c_26]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_453,plain,
% 2.73/0.99      ( v3_tex_2(X0,sK2)
% 2.73/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 2.73/0.99      | k2_pre_topc(sK2,X0) != u1_struct_0(sK2) ),
% 2.73/0.99      inference(renaming,[status(thm)],[c_452]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1807,plain,
% 2.73/0.99      ( k2_pre_topc(sK2,X0) != u1_struct_0(sK2)
% 2.73/0.99      | v3_tex_2(X0,sK2) = iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(predicate_to_equality,[status(thm)],[c_453]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_1860,plain,
% 2.73/0.99      ( k2_pre_topc(sK2,X0) != k2_struct_0(sK2)
% 2.73/0.99      | v3_tex_2(X0,sK2) = iProver_top
% 2.73/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(light_normalisation,[status(thm)],[c_1807,c_535]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2014,plain,
% 2.73/0.99      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top
% 2.73/0.99      | m1_subset_1(k2_struct_0(sK2),k1_zfmisc_1(k2_struct_0(sK2))) != iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_540,c_1860]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_2255,plain,
% 2.73/0.99      ( v3_tex_2(k2_struct_0(sK2),sK2) = iProver_top ),
% 2.73/0.99      inference(superposition,[status(thm)],[c_1825,c_2014]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(c_4014,plain,
% 2.73/0.99      ( v3_tex_2(sK3,sK2) = iProver_top ),
% 2.73/0.99      inference(demodulation,[status(thm)],[c_3994,c_2255]) ).
% 2.73/0.99  
% 2.73/0.99  cnf(contradiction,plain,
% 2.73/0.99      ( $false ),
% 2.73/0.99      inference(minisat,[status(thm)],[c_4014,c_3604,c_2656,c_1822]) ).
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/0.99  
% 2.73/0.99  ------                               Statistics
% 2.73/0.99  
% 2.73/0.99  ------ General
% 2.73/0.99  
% 2.73/0.99  abstr_ref_over_cycles:                  0
% 2.73/0.99  abstr_ref_under_cycles:                 0
% 2.73/0.99  gc_basic_clause_elim:                   0
% 2.73/0.99  forced_gc_time:                         0
% 2.73/0.99  parsing_time:                           0.013
% 2.73/0.99  unif_index_cands_time:                  0.
% 2.73/0.99  unif_index_add_time:                    0.
% 2.73/0.99  orderings_time:                         0.
% 2.73/0.99  out_proof_time:                         0.01
% 2.73/0.99  total_time:                             0.149
% 2.73/0.99  num_of_symbols:                         52
% 2.73/0.99  num_of_terms:                           2928
% 2.73/0.99  
% 2.73/0.99  ------ Preprocessing
% 2.73/0.99  
% 2.73/0.99  num_of_splits:                          0
% 2.73/0.99  num_of_split_atoms:                     0
% 2.73/0.99  num_of_reused_defs:                     0
% 2.73/0.99  num_eq_ax_congr_red:                    26
% 2.73/0.99  num_of_sem_filtered_clauses:            1
% 2.73/0.99  num_of_subtypes:                        0
% 2.73/0.99  monotx_restored_types:                  0
% 2.73/0.99  sat_num_of_epr_types:                   0
% 2.73/0.99  sat_num_of_non_cyclic_types:            0
% 2.73/0.99  sat_guarded_non_collapsed_types:        0
% 2.73/0.99  num_pure_diseq_elim:                    0
% 2.73/0.99  simp_replaced_by:                       0
% 2.73/0.99  res_preprocessed:                       109
% 2.73/0.99  prep_upred:                             0
% 2.73/0.99  prep_unflattend:                        43
% 2.73/0.99  smt_new_axioms:                         0
% 2.73/0.99  pred_elim_cands:                        4
% 2.73/0.99  pred_elim:                              8
% 2.73/0.99  pred_elim_cl:                           12
% 2.73/0.99  pred_elim_cycles:                       12
% 2.73/0.99  merged_defs:                            2
% 2.73/0.99  merged_defs_ncl:                        0
% 2.73/0.99  bin_hyper_res:                          2
% 2.73/0.99  prep_cycles:                            4
% 2.73/0.99  pred_elim_time:                         0.016
% 2.73/0.99  splitting_time:                         0.
% 2.73/0.99  sem_filter_time:                        0.
% 2.73/0.99  monotx_time:                            0.
% 2.73/0.99  subtype_inf_time:                       0.
% 2.73/0.99  
% 2.73/0.99  ------ Problem properties
% 2.73/0.99  
% 2.73/0.99  clauses:                                18
% 2.73/0.99  conjectures:                            1
% 2.73/0.99  epr:                                    0
% 2.73/0.99  horn:                                   13
% 2.73/0.99  ground:                                 6
% 2.73/0.99  unary:                                  6
% 2.73/0.99  binary:                                 2
% 2.73/0.99  lits:                                   45
% 2.73/0.99  lits_eq:                                10
% 2.73/0.99  fd_pure:                                0
% 2.73/0.99  fd_pseudo:                              0
% 2.73/0.99  fd_cond:                                0
% 2.73/0.99  fd_pseudo_cond:                         1
% 2.73/0.99  ac_symbols:                             0
% 2.73/0.99  
% 2.73/0.99  ------ Propositional Solver
% 2.73/0.99  
% 2.73/0.99  prop_solver_calls:                      28
% 2.73/0.99  prop_fast_solver_calls:                 1030
% 2.73/0.99  smt_solver_calls:                       0
% 2.73/0.99  smt_fast_solver_calls:                  0
% 2.73/0.99  prop_num_of_clauses:                    1203
% 2.73/0.99  prop_preprocess_simplified:             3991
% 2.73/0.99  prop_fo_subsumed:                       38
% 2.73/0.99  prop_solver_time:                       0.
% 2.73/0.99  smt_solver_time:                        0.
% 2.73/0.99  smt_fast_solver_time:                   0.
% 2.73/0.99  prop_fast_solver_time:                  0.
% 2.73/0.99  prop_unsat_core_time:                   0.
% 2.73/0.99  
% 2.73/0.99  ------ QBF
% 2.73/0.99  
% 2.73/0.99  qbf_q_res:                              0
% 2.73/0.99  qbf_num_tautologies:                    0
% 2.73/0.99  qbf_prep_cycles:                        0
% 2.73/0.99  
% 2.73/0.99  ------ BMC1
% 2.73/0.99  
% 2.73/0.99  bmc1_current_bound:                     -1
% 2.73/0.99  bmc1_last_solved_bound:                 -1
% 2.73/0.99  bmc1_unsat_core_size:                   -1
% 2.73/0.99  bmc1_unsat_core_parents_size:           -1
% 2.73/0.99  bmc1_merge_next_fun:                    0
% 2.73/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.73/0.99  
% 2.73/0.99  ------ Instantiation
% 2.73/0.99  
% 2.73/0.99  inst_num_of_clauses:                    327
% 2.73/0.99  inst_num_in_passive:                    81
% 2.73/0.99  inst_num_in_active:                     186
% 2.73/0.99  inst_num_in_unprocessed:                60
% 2.73/0.99  inst_num_of_loops:                      230
% 2.73/0.99  inst_num_of_learning_restarts:          0
% 2.73/0.99  inst_num_moves_active_passive:          41
% 2.73/0.99  inst_lit_activity:                      0
% 2.73/0.99  inst_lit_activity_moves:                0
% 2.73/0.99  inst_num_tautologies:                   0
% 2.73/0.99  inst_num_prop_implied:                  0
% 2.73/0.99  inst_num_existing_simplified:           0
% 2.73/0.99  inst_num_eq_res_simplified:             0
% 2.73/0.99  inst_num_child_elim:                    0
% 2.73/0.99  inst_num_of_dismatching_blockings:      74
% 2.73/0.99  inst_num_of_non_proper_insts:           318
% 2.73/0.99  inst_num_of_duplicates:                 0
% 2.73/0.99  inst_inst_num_from_inst_to_res:         0
% 2.73/0.99  inst_dismatching_checking_time:         0.
% 2.73/0.99  
% 2.73/0.99  ------ Resolution
% 2.73/0.99  
% 2.73/0.99  res_num_of_clauses:                     0
% 2.73/0.99  res_num_in_passive:                     0
% 2.73/0.99  res_num_in_active:                      0
% 2.73/0.99  res_num_of_loops:                       113
% 2.73/0.99  res_forward_subset_subsumed:            44
% 2.73/0.99  res_backward_subset_subsumed:           0
% 2.73/0.99  res_forward_subsumed:                   1
% 2.73/0.99  res_backward_subsumed:                  0
% 2.73/0.99  res_forward_subsumption_resolution:     0
% 2.73/0.99  res_backward_subsumption_resolution:    0
% 2.73/0.99  res_clause_to_clause_subsumption:       408
% 2.73/0.99  res_orphan_elimination:                 0
% 2.73/0.99  res_tautology_del:                      34
% 2.73/0.99  res_num_eq_res_simplified:              0
% 2.73/0.99  res_num_sel_changes:                    0
% 2.73/0.99  res_moves_from_active_to_pass:          0
% 2.73/0.99  
% 2.73/0.99  ------ Superposition
% 2.73/0.99  
% 2.73/0.99  sup_time_total:                         0.
% 2.73/0.99  sup_time_generating:                    0.
% 2.73/0.99  sup_time_sim_full:                      0.
% 2.73/0.99  sup_time_sim_immed:                     0.
% 2.73/0.99  
% 2.73/0.99  sup_num_of_clauses:                     24
% 2.73/0.99  sup_num_in_active:                      10
% 2.73/0.99  sup_num_in_passive:                     14
% 2.73/0.99  sup_num_of_loops:                       45
% 2.73/0.99  sup_fw_superposition:                   48
% 2.73/0.99  sup_bw_superposition:                   7
% 2.73/0.99  sup_immediate_simplified:               10
% 2.73/0.99  sup_given_eliminated:                   0
% 2.73/0.99  comparisons_done:                       0
% 2.73/0.99  comparisons_avoided:                    0
% 2.73/0.99  
% 2.73/0.99  ------ Simplifications
% 2.73/0.99  
% 2.73/0.99  
% 2.73/0.99  sim_fw_subset_subsumed:                 7
% 2.73/0.99  sim_bw_subset_subsumed:                 9
% 2.73/0.99  sim_fw_subsumed:                        4
% 2.73/0.99  sim_bw_subsumed:                        2
% 2.73/0.99  sim_fw_subsumption_res:                 0
% 2.73/0.99  sim_bw_subsumption_res:                 0
% 2.73/0.99  sim_tautology_del:                      3
% 2.73/0.99  sim_eq_tautology_del:                   3
% 2.73/0.99  sim_eq_res_simp:                        1
% 2.73/0.99  sim_fw_demodulated:                     2
% 2.73/0.99  sim_bw_demodulated:                     28
% 2.73/0.99  sim_light_normalised:                   9
% 2.73/0.99  sim_joinable_taut:                      0
% 2.73/0.99  sim_joinable_simp:                      0
% 2.73/0.99  sim_ac_normalised:                      0
% 2.73/0.99  sim_smt_subsumption:                    0
% 2.73/0.99  
%------------------------------------------------------------------------------
