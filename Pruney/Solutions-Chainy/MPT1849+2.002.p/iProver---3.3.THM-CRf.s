%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:25:29 EST 2020

% Result     : Theorem 6.82s
% Output     : CNFRefutation 6.82s
% Verified   : 
% Statistics : Number of formulae       :  225 (8352 expanded)
%              Number of clauses        :  146 (1985 expanded)
%              Number of leaves         :   21 (2001 expanded)
%              Depth                    :   28
%              Number of atoms          :  683 (35654 expanded)
%              Number of equality atoms :  324 (9038 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v1_subset_1(X2,u1_struct_0(X0))
                  | u1_struct_0(X1) != X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ? [X2] :
                  ( ~ v1_subset_1(X2,u1_struct_0(X0))
                  & u1_struct_0(X1) = X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v1_subset_1(X2,u1_struct_0(X0))
          & u1_struct_0(X1) = X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
        & u1_struct_0(X1) = sK0(X0,X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(X1,X0)
              | ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
                & u1_struct_0(X1) = sK0(X0,X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v1_subset_1(X3,u1_struct_0(X0))
                  | u1_struct_0(X1) != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tex_2(X1,X0) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
         => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v1_tex_2(X1,X0) )
           => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,X0)
          & ~ v1_tex_2(X1,X0) )
     => ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
        & m1_pre_topc(sK2,X0)
        & ~ v1_tex_2(sK2,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_pre_topc(X1,X0)
            & ~ v1_tex_2(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_pre_topc(X1,sK1)
          & ~ v1_tex_2(X1,sK1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_pre_topc(sK2,sK1)
    & ~ v1_tex_2(sK2,sK1)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f52,f51])).

fof(f83,plain,(
    ~ v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | u1_struct_0(X1) = sK0(X0,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f81,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_tex_2(X1,X0)
      | ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( k1_pre_topc(X0,X1) = X2
                  | k2_struct_0(X2) != X1 )
                & ( k2_struct_0(X2) = X1
                  | k1_pre_topc(X0,X1) != X2 ) )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k1_pre_topc(X0,X1) = X2
      | k2_struct_0(X2) != X1
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X0] :
      ( k1_pre_topc(X0,k2_struct_0(X2)) = X2
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_pre_topc(X2)
      | ~ m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f57,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_24,plain,
    ( v1_tex_2(X0,X1)
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_30,negated_conjecture,
    ( ~ v1_tex_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_523,plain,
    ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_30])).

cnf(c_524,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_526,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_524,c_31,c_29])).

cnf(c_3087,plain,
    ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_526])).

cnf(c_23,plain,
    ( v1_tex_2(X0,X1)
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_534,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) = u1_struct_0(X0)
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_535,plain,
    ( ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1)
    | sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_537,plain,
    ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_31,c_29])).

cnf(c_3123,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3087,c_537])).

cnf(c_26,plain,
    ( v1_subset_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | X0 = X1 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3097,plain,
    ( X0 = X1
    | v1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4180,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3123,c_3097])).

cnf(c_22,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | v1_tex_2(X1,X0)
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_512,plain,
    ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
    | ~ m1_pre_topc(X1,X0)
    | ~ l1_pre_topc(X0)
    | sK2 != X1
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_513,plain,
    ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
    | ~ m1_pre_topc(sK2,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_515,plain,
    ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_31,c_29])).

cnf(c_3088,plain,
    ( v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_3126,plain,
    ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3088,c_537])).

cnf(c_4479,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4180,c_3126])).

cnf(c_11,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3106,plain,
    ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | l1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3109,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3792,plain,
    ( l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_3109])).

cnf(c_4508,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3792])).

cnf(c_32,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3095,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3107,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3939,plain,
    ( l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3095,c_3107])).

cnf(c_5331,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4508,c_32,c_3939])).

cnf(c_9,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( ~ l1_struct_0(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_355,plain,
    ( ~ l1_pre_topc(X0)
    | k2_struct_0(X0) = u1_struct_0(X0) ),
    inference(resolution,[status(thm)],[c_9,c_6])).

cnf(c_3092,plain,
    ( k2_struct_0(X0) = u1_struct_0(X0)
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_5337,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    inference(superposition,[status(thm)],[c_5331,c_3092])).

cnf(c_4,plain,
    ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X0)
    | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3111,plain,
    ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
    | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8331,plain,
    ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_3111])).

cnf(c_8332,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8331,c_5337])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | v1_pre_topc(g1_pre_topc(X1,X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3108,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
    | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3690,plain,
    ( l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_3108])).

cnf(c_4509,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3690])).

cnf(c_27973,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8332,c_32,c_3939,c_4509])).

cnf(c_27974,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_27973])).

cnf(c_16,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_192,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16,c_10])).

cnf(c_193,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(renaming,[status(thm)],[c_192])).

cnf(c_3093,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_193])).

cnf(c_5834,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3093])).

cnf(c_6545,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5834,c_32,c_3939])).

cnf(c_6546,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6545])).

cnf(c_21,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3098,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4506,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3098])).

cnf(c_4513,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3098])).

cnf(c_5653,plain,
    ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4513,c_32,c_3939])).

cnf(c_5654,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5653])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3114,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5662,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5654,c_3114])).

cnf(c_8672,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4506,c_5662])).

cnf(c_5639,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(sK2,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4506,c_3114])).

cnf(c_6554,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6546,c_3107])).

cnf(c_8967,plain,
    ( m1_pre_topc(sK2,X0) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | u1_struct_0(X0) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8672,c_32,c_3939,c_4508,c_4513,c_5639,c_6554])).

cnf(c_8968,plain,
    ( u1_struct_0(X0) = u1_struct_0(sK1)
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8967])).

cnf(c_8977,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2) != iProver_top
    | m1_pre_topc(sK2,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6546,c_8968])).

cnf(c_3944,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3939])).

cnf(c_4584,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4508])).

cnf(c_20,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_3099,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_14,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_3103,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_5857,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3103])).

cnf(c_6582,plain,
    ( m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5857,c_32,c_3939])).

cnf(c_6583,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top ),
    inference(renaming,[status(thm)],[c_6582])).

cnf(c_6591,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2) = iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_6583])).

cnf(c_6613,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6591])).

cnf(c_8995,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2)
    | ~ m1_pre_topc(sK2,sK2)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8977])).

cnf(c_9939,plain,
    ( m1_pre_topc(sK2,sK2)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_12515,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8977,c_31,c_3944,c_4584,c_6613,c_8995,c_9939])).

cnf(c_27979,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27974,c_12515])).

cnf(c_19,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3100,plain,
    ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_12557,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12515,c_3100])).

cnf(c_27984,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_27979,c_12557])).

cnf(c_27986,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_27984])).

cnf(c_17,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3102,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3094,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3930,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3792,c_3092])).

cnf(c_6853,plain,
    ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(superposition,[status(thm)],[c_3094,c_3930])).

cnf(c_6871,plain,
    ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6853,c_3111])).

cnf(c_6872,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6871,c_6853])).

cnf(c_56,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_58,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_18,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_62,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_64,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_6978,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6872,c_32,c_58,c_64])).

cnf(c_6979,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6978])).

cnf(c_6988,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6979,c_3100])).

cnf(c_6993,plain,
    ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3102,c_6988])).

cnf(c_3,plain,
    ( ~ l1_pre_topc(X0)
    | ~ v1_pre_topc(X0)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3112,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4200,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3792,c_3112])).

cnf(c_3346,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3347,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
    | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3346])).

cnf(c_9071,plain,
    ( l1_pre_topc(X0) != iProver_top
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4200,c_3347,c_3690,c_3792])).

cnf(c_9072,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9071])).

cnf(c_9079,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(superposition,[status(thm)],[c_3094,c_9072])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
    | X2 = X1
    | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3104,plain,
    ( X0 = X1
    | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_9105,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
    | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_9079,c_3104])).

cnf(c_9683,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
    | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_9105])).

cnf(c_57,plain,
    ( m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_78,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_625,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != X2
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_18])).

cnf(c_626,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_628,plain,
    ( ~ m1_pre_topc(sK1,sK1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_3336,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3338,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(instantiation,[status(thm)],[c_3336])).

cnf(c_3819,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | X2 = u1_struct_0(X1)
    | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_4761,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | X1 = u1_struct_0(X0)
    | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
    inference(instantiation,[status(thm)],[c_3819])).

cnf(c_7726,plain,
    ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
    | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
    inference(instantiation,[status(thm)],[c_4761])).

cnf(c_7728,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_7726])).

cnf(c_10028,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9683,c_31,c_57,c_78,c_628,c_3338,c_7728])).

cnf(c_12123,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_pre_topc(sK1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6993,c_10028])).

cnf(c_12131,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3099,c_12123])).

cnf(c_65,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_67,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
    | m1_pre_topc(sK1,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_10035,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10028,c_6988])).

cnf(c_10069,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_10035])).

cnf(c_13299,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12131,c_32,c_58,c_67,c_10069])).

cnf(c_28,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4487,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(demodulation,[status(thm)],[c_4479,c_28])).

cnf(c_13314,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != k1_pre_topc(sK1,u1_struct_0(sK1)) ),
    inference(demodulation,[status(thm)],[c_13299,c_4487])).

cnf(c_5206,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) = iProver_top
    | m1_pre_topc(sK2,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4479,c_3102])).

cnf(c_5228,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) = iProver_top
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5206])).

cnf(c_34,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_27986,c_13314,c_5228,c_34,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 6.82/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.82/1.50  
% 6.82/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.82/1.50  
% 6.82/1.50  ------  iProver source info
% 6.82/1.50  
% 6.82/1.50  git: date: 2020-06-30 10:37:57 +0100
% 6.82/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.82/1.50  git: non_committed_changes: false
% 6.82/1.50  git: last_make_outside_of_git: false
% 6.82/1.50  
% 6.82/1.50  ------ 
% 6.82/1.50  
% 6.82/1.50  ------ Input Options
% 6.82/1.50  
% 6.82/1.50  --out_options                           all
% 6.82/1.50  --tptp_safe_out                         true
% 6.82/1.50  --problem_path                          ""
% 6.82/1.50  --include_path                          ""
% 6.82/1.50  --clausifier                            res/vclausify_rel
% 6.82/1.50  --clausifier_options                    --mode clausify
% 6.82/1.50  --stdin                                 false
% 6.82/1.50  --stats_out                             all
% 6.82/1.50  
% 6.82/1.50  ------ General Options
% 6.82/1.50  
% 6.82/1.50  --fof                                   false
% 6.82/1.50  --time_out_real                         305.
% 6.82/1.50  --time_out_virtual                      -1.
% 6.82/1.50  --symbol_type_check                     false
% 6.82/1.50  --clausify_out                          false
% 6.82/1.50  --sig_cnt_out                           false
% 6.82/1.50  --trig_cnt_out                          false
% 6.82/1.50  --trig_cnt_out_tolerance                1.
% 6.82/1.50  --trig_cnt_out_sk_spl                   false
% 6.82/1.50  --abstr_cl_out                          false
% 6.82/1.50  
% 6.82/1.50  ------ Global Options
% 6.82/1.50  
% 6.82/1.50  --schedule                              default
% 6.82/1.50  --add_important_lit                     false
% 6.82/1.50  --prop_solver_per_cl                    1000
% 6.82/1.50  --min_unsat_core                        false
% 6.82/1.50  --soft_assumptions                      false
% 6.82/1.50  --soft_lemma_size                       3
% 6.82/1.50  --prop_impl_unit_size                   0
% 6.82/1.50  --prop_impl_unit                        []
% 6.82/1.50  --share_sel_clauses                     true
% 6.82/1.50  --reset_solvers                         false
% 6.82/1.50  --bc_imp_inh                            [conj_cone]
% 6.82/1.50  --conj_cone_tolerance                   3.
% 6.82/1.50  --extra_neg_conj                        none
% 6.82/1.50  --large_theory_mode                     true
% 6.82/1.50  --prolific_symb_bound                   200
% 6.82/1.50  --lt_threshold                          2000
% 6.82/1.50  --clause_weak_htbl                      true
% 6.82/1.50  --gc_record_bc_elim                     false
% 6.82/1.50  
% 6.82/1.50  ------ Preprocessing Options
% 6.82/1.50  
% 6.82/1.50  --preprocessing_flag                    true
% 6.82/1.50  --time_out_prep_mult                    0.1
% 6.82/1.50  --splitting_mode                        input
% 6.82/1.50  --splitting_grd                         true
% 6.82/1.50  --splitting_cvd                         false
% 6.82/1.50  --splitting_cvd_svl                     false
% 6.82/1.50  --splitting_nvd                         32
% 6.82/1.50  --sub_typing                            true
% 6.82/1.50  --prep_gs_sim                           true
% 6.82/1.50  --prep_unflatten                        true
% 6.82/1.50  --prep_res_sim                          true
% 6.82/1.50  --prep_upred                            true
% 6.82/1.50  --prep_sem_filter                       exhaustive
% 6.82/1.50  --prep_sem_filter_out                   false
% 6.82/1.50  --pred_elim                             true
% 6.82/1.50  --res_sim_input                         true
% 6.82/1.50  --eq_ax_congr_red                       true
% 6.82/1.50  --pure_diseq_elim                       true
% 6.82/1.50  --brand_transform                       false
% 6.82/1.50  --non_eq_to_eq                          false
% 6.82/1.50  --prep_def_merge                        true
% 6.82/1.50  --prep_def_merge_prop_impl              false
% 6.82/1.51  --prep_def_merge_mbd                    true
% 6.82/1.51  --prep_def_merge_tr_red                 false
% 6.82/1.51  --prep_def_merge_tr_cl                  false
% 6.82/1.51  --smt_preprocessing                     true
% 6.82/1.51  --smt_ac_axioms                         fast
% 6.82/1.51  --preprocessed_out                      false
% 6.82/1.51  --preprocessed_stats                    false
% 6.82/1.51  
% 6.82/1.51  ------ Abstraction refinement Options
% 6.82/1.51  
% 6.82/1.51  --abstr_ref                             []
% 6.82/1.51  --abstr_ref_prep                        false
% 6.82/1.51  --abstr_ref_until_sat                   false
% 6.82/1.51  --abstr_ref_sig_restrict                funpre
% 6.82/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.82/1.51  --abstr_ref_under                       []
% 6.82/1.51  
% 6.82/1.51  ------ SAT Options
% 6.82/1.51  
% 6.82/1.51  --sat_mode                              false
% 6.82/1.51  --sat_fm_restart_options                ""
% 6.82/1.51  --sat_gr_def                            false
% 6.82/1.51  --sat_epr_types                         true
% 6.82/1.51  --sat_non_cyclic_types                  false
% 6.82/1.51  --sat_finite_models                     false
% 6.82/1.51  --sat_fm_lemmas                         false
% 6.82/1.51  --sat_fm_prep                           false
% 6.82/1.51  --sat_fm_uc_incr                        true
% 6.82/1.51  --sat_out_model                         small
% 6.82/1.51  --sat_out_clauses                       false
% 6.82/1.51  
% 6.82/1.51  ------ QBF Options
% 6.82/1.51  
% 6.82/1.51  --qbf_mode                              false
% 6.82/1.51  --qbf_elim_univ                         false
% 6.82/1.51  --qbf_dom_inst                          none
% 6.82/1.51  --qbf_dom_pre_inst                      false
% 6.82/1.51  --qbf_sk_in                             false
% 6.82/1.51  --qbf_pred_elim                         true
% 6.82/1.51  --qbf_split                             512
% 6.82/1.51  
% 6.82/1.51  ------ BMC1 Options
% 6.82/1.51  
% 6.82/1.51  --bmc1_incremental                      false
% 6.82/1.51  --bmc1_axioms                           reachable_all
% 6.82/1.51  --bmc1_min_bound                        0
% 6.82/1.51  --bmc1_max_bound                        -1
% 6.82/1.51  --bmc1_max_bound_default                -1
% 6.82/1.51  --bmc1_symbol_reachability              true
% 6.82/1.51  --bmc1_property_lemmas                  false
% 6.82/1.51  --bmc1_k_induction                      false
% 6.82/1.51  --bmc1_non_equiv_states                 false
% 6.82/1.51  --bmc1_deadlock                         false
% 6.82/1.51  --bmc1_ucm                              false
% 6.82/1.51  --bmc1_add_unsat_core                   none
% 6.82/1.51  --bmc1_unsat_core_children              false
% 6.82/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.82/1.51  --bmc1_out_stat                         full
% 6.82/1.51  --bmc1_ground_init                      false
% 6.82/1.51  --bmc1_pre_inst_next_state              false
% 6.82/1.51  --bmc1_pre_inst_state                   false
% 6.82/1.51  --bmc1_pre_inst_reach_state             false
% 6.82/1.51  --bmc1_out_unsat_core                   false
% 6.82/1.51  --bmc1_aig_witness_out                  false
% 6.82/1.51  --bmc1_verbose                          false
% 6.82/1.51  --bmc1_dump_clauses_tptp                false
% 6.82/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.82/1.51  --bmc1_dump_file                        -
% 6.82/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.82/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.82/1.51  --bmc1_ucm_extend_mode                  1
% 6.82/1.51  --bmc1_ucm_init_mode                    2
% 6.82/1.51  --bmc1_ucm_cone_mode                    none
% 6.82/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.82/1.51  --bmc1_ucm_relax_model                  4
% 6.82/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.82/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.82/1.51  --bmc1_ucm_layered_model                none
% 6.82/1.51  --bmc1_ucm_max_lemma_size               10
% 6.82/1.51  
% 6.82/1.51  ------ AIG Options
% 6.82/1.51  
% 6.82/1.51  --aig_mode                              false
% 6.82/1.51  
% 6.82/1.51  ------ Instantiation Options
% 6.82/1.51  
% 6.82/1.51  --instantiation_flag                    true
% 6.82/1.51  --inst_sos_flag                         false
% 6.82/1.51  --inst_sos_phase                        true
% 6.82/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.82/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.82/1.51  --inst_lit_sel_side                     num_symb
% 6.82/1.51  --inst_solver_per_active                1400
% 6.82/1.51  --inst_solver_calls_frac                1.
% 6.82/1.51  --inst_passive_queue_type               priority_queues
% 6.82/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.82/1.51  --inst_passive_queues_freq              [25;2]
% 6.82/1.51  --inst_dismatching                      true
% 6.82/1.51  --inst_eager_unprocessed_to_passive     true
% 6.82/1.51  --inst_prop_sim_given                   true
% 6.82/1.51  --inst_prop_sim_new                     false
% 6.82/1.51  --inst_subs_new                         false
% 6.82/1.51  --inst_eq_res_simp                      false
% 6.82/1.51  --inst_subs_given                       false
% 6.82/1.51  --inst_orphan_elimination               true
% 6.82/1.51  --inst_learning_loop_flag               true
% 6.82/1.51  --inst_learning_start                   3000
% 6.82/1.51  --inst_learning_factor                  2
% 6.82/1.51  --inst_start_prop_sim_after_learn       3
% 6.82/1.51  --inst_sel_renew                        solver
% 6.82/1.51  --inst_lit_activity_flag                true
% 6.82/1.51  --inst_restr_to_given                   false
% 6.82/1.51  --inst_activity_threshold               500
% 6.82/1.51  --inst_out_proof                        true
% 6.82/1.51  
% 6.82/1.51  ------ Resolution Options
% 6.82/1.51  
% 6.82/1.51  --resolution_flag                       true
% 6.82/1.51  --res_lit_sel                           adaptive
% 6.82/1.51  --res_lit_sel_side                      none
% 6.82/1.51  --res_ordering                          kbo
% 6.82/1.51  --res_to_prop_solver                    active
% 6.82/1.51  --res_prop_simpl_new                    false
% 6.82/1.51  --res_prop_simpl_given                  true
% 6.82/1.51  --res_passive_queue_type                priority_queues
% 6.82/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.82/1.51  --res_passive_queues_freq               [15;5]
% 6.82/1.51  --res_forward_subs                      full
% 6.82/1.51  --res_backward_subs                     full
% 6.82/1.51  --res_forward_subs_resolution           true
% 6.82/1.51  --res_backward_subs_resolution          true
% 6.82/1.51  --res_orphan_elimination                true
% 6.82/1.51  --res_time_limit                        2.
% 6.82/1.51  --res_out_proof                         true
% 6.82/1.51  
% 6.82/1.51  ------ Superposition Options
% 6.82/1.51  
% 6.82/1.51  --superposition_flag                    true
% 6.82/1.51  --sup_passive_queue_type                priority_queues
% 6.82/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.82/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.82/1.51  --demod_completeness_check              fast
% 6.82/1.51  --demod_use_ground                      true
% 6.82/1.51  --sup_to_prop_solver                    passive
% 6.82/1.51  --sup_prop_simpl_new                    true
% 6.82/1.51  --sup_prop_simpl_given                  true
% 6.82/1.51  --sup_fun_splitting                     false
% 6.82/1.51  --sup_smt_interval                      50000
% 6.82/1.51  
% 6.82/1.51  ------ Superposition Simplification Setup
% 6.82/1.51  
% 6.82/1.51  --sup_indices_passive                   []
% 6.82/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.82/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_full_bw                           [BwDemod]
% 6.82/1.51  --sup_immed_triv                        [TrivRules]
% 6.82/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.82/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_immed_bw_main                     []
% 6.82/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.82/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.82/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.82/1.51  
% 6.82/1.51  ------ Combination Options
% 6.82/1.51  
% 6.82/1.51  --comb_res_mult                         3
% 6.82/1.51  --comb_sup_mult                         2
% 6.82/1.51  --comb_inst_mult                        10
% 6.82/1.51  
% 6.82/1.51  ------ Debug Options
% 6.82/1.51  
% 6.82/1.51  --dbg_backtrace                         false
% 6.82/1.51  --dbg_dump_prop_clauses                 false
% 6.82/1.51  --dbg_dump_prop_clauses_file            -
% 6.82/1.51  --dbg_out_stat                          false
% 6.82/1.51  ------ Parsing...
% 6.82/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.82/1.51  
% 6.82/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 6.82/1.51  
% 6.82/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.82/1.51  
% 6.82/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.82/1.51  ------ Proving...
% 6.82/1.51  ------ Problem Properties 
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  clauses                                 30
% 6.82/1.51  conjectures                             3
% 6.82/1.51  EPR                                     6
% 6.82/1.51  Horn                                    27
% 6.82/1.51  unary                                   7
% 6.82/1.51  binary                                  6
% 6.82/1.51  lits                                    77
% 6.82/1.51  lits eq                                 13
% 6.82/1.51  fd_pure                                 0
% 6.82/1.51  fd_pseudo                               0
% 6.82/1.51  fd_cond                                 0
% 6.82/1.51  fd_pseudo_cond                          4
% 6.82/1.51  AC symbols                              0
% 6.82/1.51  
% 6.82/1.51  ------ Schedule dynamic 5 is on 
% 6.82/1.51  
% 6.82/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  ------ 
% 6.82/1.51  Current options:
% 6.82/1.51  ------ 
% 6.82/1.51  
% 6.82/1.51  ------ Input Options
% 6.82/1.51  
% 6.82/1.51  --out_options                           all
% 6.82/1.51  --tptp_safe_out                         true
% 6.82/1.51  --problem_path                          ""
% 6.82/1.51  --include_path                          ""
% 6.82/1.51  --clausifier                            res/vclausify_rel
% 6.82/1.51  --clausifier_options                    --mode clausify
% 6.82/1.51  --stdin                                 false
% 6.82/1.51  --stats_out                             all
% 6.82/1.51  
% 6.82/1.51  ------ General Options
% 6.82/1.51  
% 6.82/1.51  --fof                                   false
% 6.82/1.51  --time_out_real                         305.
% 6.82/1.51  --time_out_virtual                      -1.
% 6.82/1.51  --symbol_type_check                     false
% 6.82/1.51  --clausify_out                          false
% 6.82/1.51  --sig_cnt_out                           false
% 6.82/1.51  --trig_cnt_out                          false
% 6.82/1.51  --trig_cnt_out_tolerance                1.
% 6.82/1.51  --trig_cnt_out_sk_spl                   false
% 6.82/1.51  --abstr_cl_out                          false
% 6.82/1.51  
% 6.82/1.51  ------ Global Options
% 6.82/1.51  
% 6.82/1.51  --schedule                              default
% 6.82/1.51  --add_important_lit                     false
% 6.82/1.51  --prop_solver_per_cl                    1000
% 6.82/1.51  --min_unsat_core                        false
% 6.82/1.51  --soft_assumptions                      false
% 6.82/1.51  --soft_lemma_size                       3
% 6.82/1.51  --prop_impl_unit_size                   0
% 6.82/1.51  --prop_impl_unit                        []
% 6.82/1.51  --share_sel_clauses                     true
% 6.82/1.51  --reset_solvers                         false
% 6.82/1.51  --bc_imp_inh                            [conj_cone]
% 6.82/1.51  --conj_cone_tolerance                   3.
% 6.82/1.51  --extra_neg_conj                        none
% 6.82/1.51  --large_theory_mode                     true
% 6.82/1.51  --prolific_symb_bound                   200
% 6.82/1.51  --lt_threshold                          2000
% 6.82/1.51  --clause_weak_htbl                      true
% 6.82/1.51  --gc_record_bc_elim                     false
% 6.82/1.51  
% 6.82/1.51  ------ Preprocessing Options
% 6.82/1.51  
% 6.82/1.51  --preprocessing_flag                    true
% 6.82/1.51  --time_out_prep_mult                    0.1
% 6.82/1.51  --splitting_mode                        input
% 6.82/1.51  --splitting_grd                         true
% 6.82/1.51  --splitting_cvd                         false
% 6.82/1.51  --splitting_cvd_svl                     false
% 6.82/1.51  --splitting_nvd                         32
% 6.82/1.51  --sub_typing                            true
% 6.82/1.51  --prep_gs_sim                           true
% 6.82/1.51  --prep_unflatten                        true
% 6.82/1.51  --prep_res_sim                          true
% 6.82/1.51  --prep_upred                            true
% 6.82/1.51  --prep_sem_filter                       exhaustive
% 6.82/1.51  --prep_sem_filter_out                   false
% 6.82/1.51  --pred_elim                             true
% 6.82/1.51  --res_sim_input                         true
% 6.82/1.51  --eq_ax_congr_red                       true
% 6.82/1.51  --pure_diseq_elim                       true
% 6.82/1.51  --brand_transform                       false
% 6.82/1.51  --non_eq_to_eq                          false
% 6.82/1.51  --prep_def_merge                        true
% 6.82/1.51  --prep_def_merge_prop_impl              false
% 6.82/1.51  --prep_def_merge_mbd                    true
% 6.82/1.51  --prep_def_merge_tr_red                 false
% 6.82/1.51  --prep_def_merge_tr_cl                  false
% 6.82/1.51  --smt_preprocessing                     true
% 6.82/1.51  --smt_ac_axioms                         fast
% 6.82/1.51  --preprocessed_out                      false
% 6.82/1.51  --preprocessed_stats                    false
% 6.82/1.51  
% 6.82/1.51  ------ Abstraction refinement Options
% 6.82/1.51  
% 6.82/1.51  --abstr_ref                             []
% 6.82/1.51  --abstr_ref_prep                        false
% 6.82/1.51  --abstr_ref_until_sat                   false
% 6.82/1.51  --abstr_ref_sig_restrict                funpre
% 6.82/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 6.82/1.51  --abstr_ref_under                       []
% 6.82/1.51  
% 6.82/1.51  ------ SAT Options
% 6.82/1.51  
% 6.82/1.51  --sat_mode                              false
% 6.82/1.51  --sat_fm_restart_options                ""
% 6.82/1.51  --sat_gr_def                            false
% 6.82/1.51  --sat_epr_types                         true
% 6.82/1.51  --sat_non_cyclic_types                  false
% 6.82/1.51  --sat_finite_models                     false
% 6.82/1.51  --sat_fm_lemmas                         false
% 6.82/1.51  --sat_fm_prep                           false
% 6.82/1.51  --sat_fm_uc_incr                        true
% 6.82/1.51  --sat_out_model                         small
% 6.82/1.51  --sat_out_clauses                       false
% 6.82/1.51  
% 6.82/1.51  ------ QBF Options
% 6.82/1.51  
% 6.82/1.51  --qbf_mode                              false
% 6.82/1.51  --qbf_elim_univ                         false
% 6.82/1.51  --qbf_dom_inst                          none
% 6.82/1.51  --qbf_dom_pre_inst                      false
% 6.82/1.51  --qbf_sk_in                             false
% 6.82/1.51  --qbf_pred_elim                         true
% 6.82/1.51  --qbf_split                             512
% 6.82/1.51  
% 6.82/1.51  ------ BMC1 Options
% 6.82/1.51  
% 6.82/1.51  --bmc1_incremental                      false
% 6.82/1.51  --bmc1_axioms                           reachable_all
% 6.82/1.51  --bmc1_min_bound                        0
% 6.82/1.51  --bmc1_max_bound                        -1
% 6.82/1.51  --bmc1_max_bound_default                -1
% 6.82/1.51  --bmc1_symbol_reachability              true
% 6.82/1.51  --bmc1_property_lemmas                  false
% 6.82/1.51  --bmc1_k_induction                      false
% 6.82/1.51  --bmc1_non_equiv_states                 false
% 6.82/1.51  --bmc1_deadlock                         false
% 6.82/1.51  --bmc1_ucm                              false
% 6.82/1.51  --bmc1_add_unsat_core                   none
% 6.82/1.51  --bmc1_unsat_core_children              false
% 6.82/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 6.82/1.51  --bmc1_out_stat                         full
% 6.82/1.51  --bmc1_ground_init                      false
% 6.82/1.51  --bmc1_pre_inst_next_state              false
% 6.82/1.51  --bmc1_pre_inst_state                   false
% 6.82/1.51  --bmc1_pre_inst_reach_state             false
% 6.82/1.51  --bmc1_out_unsat_core                   false
% 6.82/1.51  --bmc1_aig_witness_out                  false
% 6.82/1.51  --bmc1_verbose                          false
% 6.82/1.51  --bmc1_dump_clauses_tptp                false
% 6.82/1.51  --bmc1_dump_unsat_core_tptp             false
% 6.82/1.51  --bmc1_dump_file                        -
% 6.82/1.51  --bmc1_ucm_expand_uc_limit              128
% 6.82/1.51  --bmc1_ucm_n_expand_iterations          6
% 6.82/1.51  --bmc1_ucm_extend_mode                  1
% 6.82/1.51  --bmc1_ucm_init_mode                    2
% 6.82/1.51  --bmc1_ucm_cone_mode                    none
% 6.82/1.51  --bmc1_ucm_reduced_relation_type        0
% 6.82/1.51  --bmc1_ucm_relax_model                  4
% 6.82/1.51  --bmc1_ucm_full_tr_after_sat            true
% 6.82/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 6.82/1.51  --bmc1_ucm_layered_model                none
% 6.82/1.51  --bmc1_ucm_max_lemma_size               10
% 6.82/1.51  
% 6.82/1.51  ------ AIG Options
% 6.82/1.51  
% 6.82/1.51  --aig_mode                              false
% 6.82/1.51  
% 6.82/1.51  ------ Instantiation Options
% 6.82/1.51  
% 6.82/1.51  --instantiation_flag                    true
% 6.82/1.51  --inst_sos_flag                         false
% 6.82/1.51  --inst_sos_phase                        true
% 6.82/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.82/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.82/1.51  --inst_lit_sel_side                     none
% 6.82/1.51  --inst_solver_per_active                1400
% 6.82/1.51  --inst_solver_calls_frac                1.
% 6.82/1.51  --inst_passive_queue_type               priority_queues
% 6.82/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.82/1.51  --inst_passive_queues_freq              [25;2]
% 6.82/1.51  --inst_dismatching                      true
% 6.82/1.51  --inst_eager_unprocessed_to_passive     true
% 6.82/1.51  --inst_prop_sim_given                   true
% 6.82/1.51  --inst_prop_sim_new                     false
% 6.82/1.51  --inst_subs_new                         false
% 6.82/1.51  --inst_eq_res_simp                      false
% 6.82/1.51  --inst_subs_given                       false
% 6.82/1.51  --inst_orphan_elimination               true
% 6.82/1.51  --inst_learning_loop_flag               true
% 6.82/1.51  --inst_learning_start                   3000
% 6.82/1.51  --inst_learning_factor                  2
% 6.82/1.51  --inst_start_prop_sim_after_learn       3
% 6.82/1.51  --inst_sel_renew                        solver
% 6.82/1.51  --inst_lit_activity_flag                true
% 6.82/1.51  --inst_restr_to_given                   false
% 6.82/1.51  --inst_activity_threshold               500
% 6.82/1.51  --inst_out_proof                        true
% 6.82/1.51  
% 6.82/1.51  ------ Resolution Options
% 6.82/1.51  
% 6.82/1.51  --resolution_flag                       false
% 6.82/1.51  --res_lit_sel                           adaptive
% 6.82/1.51  --res_lit_sel_side                      none
% 6.82/1.51  --res_ordering                          kbo
% 6.82/1.51  --res_to_prop_solver                    active
% 6.82/1.51  --res_prop_simpl_new                    false
% 6.82/1.51  --res_prop_simpl_given                  true
% 6.82/1.51  --res_passive_queue_type                priority_queues
% 6.82/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.82/1.51  --res_passive_queues_freq               [15;5]
% 6.82/1.51  --res_forward_subs                      full
% 6.82/1.51  --res_backward_subs                     full
% 6.82/1.51  --res_forward_subs_resolution           true
% 6.82/1.51  --res_backward_subs_resolution          true
% 6.82/1.51  --res_orphan_elimination                true
% 6.82/1.51  --res_time_limit                        2.
% 6.82/1.51  --res_out_proof                         true
% 6.82/1.51  
% 6.82/1.51  ------ Superposition Options
% 6.82/1.51  
% 6.82/1.51  --superposition_flag                    true
% 6.82/1.51  --sup_passive_queue_type                priority_queues
% 6.82/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.82/1.51  --sup_passive_queues_freq               [8;1;4]
% 6.82/1.51  --demod_completeness_check              fast
% 6.82/1.51  --demod_use_ground                      true
% 6.82/1.51  --sup_to_prop_solver                    passive
% 6.82/1.51  --sup_prop_simpl_new                    true
% 6.82/1.51  --sup_prop_simpl_given                  true
% 6.82/1.51  --sup_fun_splitting                     false
% 6.82/1.51  --sup_smt_interval                      50000
% 6.82/1.51  
% 6.82/1.51  ------ Superposition Simplification Setup
% 6.82/1.51  
% 6.82/1.51  --sup_indices_passive                   []
% 6.82/1.51  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.82/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 6.82/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_full_bw                           [BwDemod]
% 6.82/1.51  --sup_immed_triv                        [TrivRules]
% 6.82/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.82/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_immed_bw_main                     []
% 6.82/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.82/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 6.82/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.82/1.51  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.82/1.51  
% 6.82/1.51  ------ Combination Options
% 6.82/1.51  
% 6.82/1.51  --comb_res_mult                         3
% 6.82/1.51  --comb_sup_mult                         2
% 6.82/1.51  --comb_inst_mult                        10
% 6.82/1.51  
% 6.82/1.51  ------ Debug Options
% 6.82/1.51  
% 6.82/1.51  --dbg_backtrace                         false
% 6.82/1.51  --dbg_dump_prop_clauses                 false
% 6.82/1.51  --dbg_dump_prop_clauses_file            -
% 6.82/1.51  --dbg_out_stat                          false
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  ------ Proving...
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  % SZS status Theorem for theBenchmark.p
% 6.82/1.51  
% 6.82/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 6.82/1.51  
% 6.82/1.51  fof(f16,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f37,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f16])).
% 6.82/1.51  
% 6.82/1.51  fof(f38,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(flattening,[],[f37])).
% 6.82/1.51  
% 6.82/1.51  fof(f46,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(nnf_transformation,[],[f38])).
% 6.82/1.51  
% 6.82/1.51  fof(f47,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | ? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(rectify,[],[f46])).
% 6.82/1.51  
% 6.82/1.51  fof(f48,plain,(
% 6.82/1.51    ! [X1,X0] : (? [X2] : (~v1_subset_1(X2,u1_struct_0(X0)) & u1_struct_0(X1) = X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.82/1.51    introduced(choice_axiom,[])).
% 6.82/1.51  
% 6.82/1.51  fof(f49,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (((v1_tex_2(X1,X0) | (~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) & u1_struct_0(X1) = sK0(X0,X1) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (v1_subset_1(X3,u1_struct_0(X0)) | u1_struct_0(X1) != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tex_2(X1,X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f47,f48])).
% 6.82/1.51  
% 6.82/1.51  fof(f77,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f49])).
% 6.82/1.51  
% 6.82/1.51  fof(f18,conjecture,(
% 6.82/1.51    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f19,negated_conjecture,(
% 6.82/1.51    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 6.82/1.51    inference(negated_conjecture,[],[f18])).
% 6.82/1.51  
% 6.82/1.51  fof(f20,plain,(
% 6.82/1.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 6.82/1.51    inference(pure_predicate_removal,[],[f19])).
% 6.82/1.51  
% 6.82/1.51  fof(f40,plain,(
% 6.82/1.51    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & (m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0))) & l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f20])).
% 6.82/1.51  
% 6.82/1.51  fof(f41,plain,(
% 6.82/1.51    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0))),
% 6.82/1.51    inference(flattening,[],[f40])).
% 6.82/1.51  
% 6.82/1.51  fof(f52,plain,(
% 6.82/1.51    ( ! [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) => (g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_pre_topc(sK2,X0) & ~v1_tex_2(sK2,X0))) )),
% 6.82/1.51    introduced(choice_axiom,[])).
% 6.82/1.51  
% 6.82/1.51  fof(f51,plain,(
% 6.82/1.51    ? [X0] : (? [X1] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,X0) & ~v1_tex_2(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_pre_topc(X1,sK1) & ~v1_tex_2(X1,sK1)) & l1_pre_topc(sK1))),
% 6.82/1.51    introduced(choice_axiom,[])).
% 6.82/1.51  
% 6.82/1.51  fof(f53,plain,(
% 6.82/1.51    (g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_pre_topc(sK2,sK1) & ~v1_tex_2(sK2,sK1)) & l1_pre_topc(sK1)),
% 6.82/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f41,f52,f51])).
% 6.82/1.51  
% 6.82/1.51  fof(f83,plain,(
% 6.82/1.51    ~v1_tex_2(sK2,sK1)),
% 6.82/1.51    inference(cnf_transformation,[],[f53])).
% 6.82/1.51  
% 6.82/1.51  fof(f82,plain,(
% 6.82/1.51    l1_pre_topc(sK1)),
% 6.82/1.51    inference(cnf_transformation,[],[f53])).
% 6.82/1.51  
% 6.82/1.51  fof(f84,plain,(
% 6.82/1.51    m1_pre_topc(sK2,sK1)),
% 6.82/1.51    inference(cnf_transformation,[],[f53])).
% 6.82/1.51  
% 6.82/1.51  fof(f78,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_tex_2(X1,X0) | u1_struct_0(X1) = sK0(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f49])).
% 6.82/1.51  
% 6.82/1.51  fof(f17,axiom,(
% 6.82/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f39,plain,(
% 6.82/1.51    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.82/1.51    inference(ennf_transformation,[],[f17])).
% 6.82/1.51  
% 6.82/1.51  fof(f50,plain,(
% 6.82/1.51    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.82/1.51    inference(nnf_transformation,[],[f39])).
% 6.82/1.51  
% 6.82/1.51  fof(f81,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_subset_1(X1,X0) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.82/1.51    inference(cnf_transformation,[],[f50])).
% 6.82/1.51  
% 6.82/1.51  fof(f79,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_tex_2(X1,X0) | ~v1_subset_1(sK0(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f49])).
% 6.82/1.51  
% 6.82/1.51  fof(f8,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f29,plain,(
% 6.82/1.51    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f8])).
% 6.82/1.51  
% 6.82/1.51  fof(f65,plain,(
% 6.82/1.51    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f29])).
% 6.82/1.51  
% 6.82/1.51  fof(f5,axiom,(
% 6.82/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f26,plain,(
% 6.82/1.51    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 6.82/1.51    inference(ennf_transformation,[],[f5])).
% 6.82/1.51  
% 6.82/1.51  fof(f62,plain,(
% 6.82/1.51    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 6.82/1.51    inference(cnf_transformation,[],[f26])).
% 6.82/1.51  
% 6.82/1.51  fof(f7,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f28,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f7])).
% 6.82/1.51  
% 6.82/1.51  fof(f64,plain,(
% 6.82/1.51    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f28])).
% 6.82/1.51  
% 6.82/1.51  fof(f6,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f27,plain,(
% 6.82/1.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f6])).
% 6.82/1.51  
% 6.82/1.51  fof(f63,plain,(
% 6.82/1.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f27])).
% 6.82/1.51  
% 6.82/1.51  fof(f4,axiom,(
% 6.82/1.51    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f25,plain,(
% 6.82/1.51    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f4])).
% 6.82/1.51  
% 6.82/1.51  fof(f60,plain,(
% 6.82/1.51    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f25])).
% 6.82/1.51  
% 6.82/1.51  fof(f3,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f23,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f3])).
% 6.82/1.51  
% 6.82/1.51  fof(f24,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(flattening,[],[f23])).
% 6.82/1.51  
% 6.82/1.51  fof(f44,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (! [X2] : (((k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1) & (k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2)) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(nnf_transformation,[],[f24])).
% 6.82/1.51  
% 6.82/1.51  fof(f59,plain,(
% 6.82/1.51    ( ! [X2,X0,X1] : (k1_pre_topc(X0,X1) = X2 | k2_struct_0(X2) != X1 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f44])).
% 6.82/1.51  
% 6.82/1.51  fof(f88,plain,(
% 6.82/1.51    ( ! [X2,X0] : (k1_pre_topc(X0,k2_struct_0(X2)) = X2 | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2) | ~m1_subset_1(k2_struct_0(X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(equality_resolution,[],[f59])).
% 6.82/1.51  
% 6.82/1.51  fof(f61,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 6.82/1.51    inference(cnf_transformation,[],[f26])).
% 6.82/1.51  
% 6.82/1.51  fof(f11,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f32,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f11])).
% 6.82/1.51  
% 6.82/1.51  fof(f45,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(nnf_transformation,[],[f32])).
% 6.82/1.51  
% 6.82/1.51  fof(f69,plain,(
% 6.82/1.51    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f45])).
% 6.82/1.51  
% 6.82/1.51  fof(f15,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f36,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f15])).
% 6.82/1.51  
% 6.82/1.51  fof(f75,plain,(
% 6.82/1.51    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f36])).
% 6.82/1.51  
% 6.82/1.51  fof(f1,axiom,(
% 6.82/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f42,plain,(
% 6.82/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.82/1.51    inference(nnf_transformation,[],[f1])).
% 6.82/1.51  
% 6.82/1.51  fof(f43,plain,(
% 6.82/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.82/1.51    inference(flattening,[],[f42])).
% 6.82/1.51  
% 6.82/1.51  fof(f56,plain,(
% 6.82/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f43])).
% 6.82/1.51  
% 6.82/1.51  fof(f14,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f35,plain,(
% 6.82/1.51    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f14])).
% 6.82/1.51  
% 6.82/1.51  fof(f74,plain,(
% 6.82/1.51    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f35])).
% 6.82/1.51  
% 6.82/1.51  fof(f10,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f31,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f10])).
% 6.82/1.51  
% 6.82/1.51  fof(f68,plain,(
% 6.82/1.51    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f31])).
% 6.82/1.51  
% 6.82/1.51  fof(f13,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f34,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f13])).
% 6.82/1.51  
% 6.82/1.51  fof(f73,plain,(
% 6.82/1.51    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f34])).
% 6.82/1.51  
% 6.82/1.51  fof(f12,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f33,plain,(
% 6.82/1.51    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f12])).
% 6.82/1.51  
% 6.82/1.51  fof(f72,plain,(
% 6.82/1.51    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f33])).
% 6.82/1.51  
% 6.82/1.51  fof(f71,plain,(
% 6.82/1.51    ( ! [X0,X1] : (v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f33])).
% 6.82/1.51  
% 6.82/1.51  fof(f2,axiom,(
% 6.82/1.51    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f21,plain,(
% 6.82/1.51    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(ennf_transformation,[],[f2])).
% 6.82/1.51  
% 6.82/1.51  fof(f22,plain,(
% 6.82/1.51    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 6.82/1.51    inference(flattening,[],[f21])).
% 6.82/1.51  
% 6.82/1.51  fof(f57,plain,(
% 6.82/1.51    ( ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0)) )),
% 6.82/1.51    inference(cnf_transformation,[],[f22])).
% 6.82/1.51  
% 6.82/1.51  fof(f9,axiom,(
% 6.82/1.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 6.82/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.82/1.51  
% 6.82/1.51  fof(f30,plain,(
% 6.82/1.51    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 6.82/1.51    inference(ennf_transformation,[],[f9])).
% 6.82/1.51  
% 6.82/1.51  fof(f66,plain,(
% 6.82/1.51    ( ! [X2,X0,X3,X1] : (X0 = X2 | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 6.82/1.51    inference(cnf_transformation,[],[f30])).
% 6.82/1.51  
% 6.82/1.51  fof(f85,plain,(
% 6.82/1.51    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 6.82/1.51    inference(cnf_transformation,[],[f53])).
% 6.82/1.51  
% 6.82/1.51  cnf(c_24,plain,
% 6.82/1.51      ( v1_tex_2(X0,X1)
% 6.82/1.51      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.82/1.51      | ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f77]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_30,negated_conjecture,
% 6.82/1.51      ( ~ v1_tex_2(sK2,sK1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f83]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_523,plain,
% 6.82/1.51      ( m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
% 6.82/1.51      | ~ m1_pre_topc(X1,X0)
% 6.82/1.51      | ~ l1_pre_topc(X0)
% 6.82/1.51      | sK2 != X1
% 6.82/1.51      | sK1 != X0 ),
% 6.82/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_30]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_524,plain,
% 6.82/1.51      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
% 6.82/1.51      | ~ m1_pre_topc(sK2,sK1)
% 6.82/1.51      | ~ l1_pre_topc(sK1) ),
% 6.82/1.51      inference(unflattening,[status(thm)],[c_523]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_31,negated_conjecture,
% 6.82/1.51      ( l1_pre_topc(sK1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f82]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_29,negated_conjecture,
% 6.82/1.51      ( m1_pre_topc(sK2,sK1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f84]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_526,plain,
% 6.82/1.51      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_524,c_31,c_29]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3087,plain,
% 6.82/1.51      ( m1_subset_1(sK0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_526]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_23,plain,
% 6.82/1.51      ( v1_tex_2(X0,X1)
% 6.82/1.51      | ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | sK0(X1,X0) = u1_struct_0(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f78]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_534,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | sK0(X1,X0) = u1_struct_0(X0)
% 6.82/1.51      | sK2 != X0
% 6.82/1.51      | sK1 != X1 ),
% 6.82/1.51      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_535,plain,
% 6.82/1.51      ( ~ m1_pre_topc(sK2,sK1)
% 6.82/1.51      | ~ l1_pre_topc(sK1)
% 6.82/1.51      | sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 6.82/1.51      inference(unflattening,[status(thm)],[c_534]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_537,plain,
% 6.82/1.51      ( sK0(sK1,sK2) = u1_struct_0(sK2) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_535,c_31,c_29]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3123,plain,
% 6.82/1.51      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_3087,c_537]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_26,plain,
% 6.82/1.51      ( v1_subset_1(X0,X1)
% 6.82/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 6.82/1.51      | X0 = X1 ),
% 6.82/1.51      inference(cnf_transformation,[],[f81]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3097,plain,
% 6.82/1.51      ( X0 = X1
% 6.82/1.51      | v1_subset_1(X0,X1) = iProver_top
% 6.82/1.51      | m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4180,plain,
% 6.82/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 6.82/1.51      | v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) = iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3123,c_3097]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_22,plain,
% 6.82/1.51      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 6.82/1.51      | v1_tex_2(X1,X0)
% 6.82/1.51      | ~ m1_pre_topc(X1,X0)
% 6.82/1.51      | ~ l1_pre_topc(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f79]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_512,plain,
% 6.82/1.51      ( ~ v1_subset_1(sK0(X0,X1),u1_struct_0(X0))
% 6.82/1.51      | ~ m1_pre_topc(X1,X0)
% 6.82/1.51      | ~ l1_pre_topc(X0)
% 6.82/1.51      | sK2 != X1
% 6.82/1.51      | sK1 != X0 ),
% 6.82/1.51      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_513,plain,
% 6.82/1.51      ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1))
% 6.82/1.51      | ~ m1_pre_topc(sK2,sK1)
% 6.82/1.51      | ~ l1_pre_topc(sK1) ),
% 6.82/1.51      inference(unflattening,[status(thm)],[c_512]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_515,plain,
% 6.82/1.51      ( ~ v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_513,c_31,c_29]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3088,plain,
% 6.82/1.51      ( v1_subset_1(sK0(sK1,sK2),u1_struct_0(sK1)) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3126,plain,
% 6.82/1.51      ( v1_subset_1(u1_struct_0(sK2),u1_struct_0(sK1)) != iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_3088,c_537]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4479,plain,
% 6.82/1.51      ( u1_struct_0(sK2) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_4180,c_3126]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_11,plain,
% 6.82/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.82/1.51      | ~ l1_pre_topc(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f65]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3106,plain,
% 6.82/1.51      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) = iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_7,plain,
% 6.82/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(X1,X0)) ),
% 6.82/1.51      inference(cnf_transformation,[],[f62]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3109,plain,
% 6.82/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3792,plain,
% 6.82/1.51      ( l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3106,c_3109]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4508,plain,
% 6.82/1.51      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
% 6.82/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3792]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_32,plain,
% 6.82/1.51      ( l1_pre_topc(sK1) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3095,plain,
% 6.82/1.51      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_10,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f64]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3107,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3939,plain,
% 6.82/1.51      ( l1_pre_topc(sK2) = iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3095,c_3107]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5331,plain,
% 6.82/1.51      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_4508,c_32,c_3939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9,plain,
% 6.82/1.51      ( l1_struct_0(X0) | ~ l1_pre_topc(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f63]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6,plain,
% 6.82/1.51      ( ~ l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f60]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_355,plain,
% 6.82/1.51      ( ~ l1_pre_topc(X0) | k2_struct_0(X0) = u1_struct_0(X0) ),
% 6.82/1.51      inference(resolution,[status(thm)],[c_9,c_6]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3092,plain,
% 6.82/1.51      ( k2_struct_0(X0) = u1_struct_0(X0)
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5337,plain,
% 6.82/1.51      ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_5331,c_3092]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4,plain,
% 6.82/1.51      ( ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.82/1.51      | ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | ~ v1_pre_topc(X0)
% 6.82/1.51      | k1_pre_topc(X1,k2_struct_0(X0)) = X0 ),
% 6.82/1.51      inference(cnf_transformation,[],[f88]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3111,plain,
% 6.82/1.51      ( k1_pre_topc(X0,k2_struct_0(X1)) = X1
% 6.82/1.51      | m1_subset_1(k2_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(X1,X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8331,plain,
% 6.82/1.51      ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_5337,c_3111]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8332,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_8331,c_5337]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8,plain,
% 6.82/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(X1,X0)) ),
% 6.82/1.51      inference(cnf_transformation,[],[f61]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3108,plain,
% 6.82/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(X1,X0)) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3690,plain,
% 6.82/1.51      ( l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3106,c_3108]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4509,plain,
% 6.82/1.51      ( l1_pre_topc(sK2) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3690]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_27973,plain,
% 6.82/1.51      ( l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_8332,c_32,c_3939,c_4509]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_27974,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_27973]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_16,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 6.82/1.51      | ~ l1_pre_topc(X0)
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f69]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_192,plain,
% 6.82/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 6.82/1.51      | ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_16,c_10]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_193,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_192]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3093,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_193]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5834,plain,
% 6.82/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3093]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6545,plain,
% 6.82/1.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_5834,c_32,c_3939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6546,plain,
% 6.82/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_6545]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_21,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f75]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3098,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4506,plain,
% 6.82/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) = iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3098]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4513,plain,
% 6.82/1.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 6.82/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3098]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5653,plain,
% 6.82/1.51      ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_4513,c_32,c_3939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5654,plain,
% 6.82/1.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) = iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_5653]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_0,plain,
% 6.82/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 6.82/1.51      inference(cnf_transformation,[],[f56]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3114,plain,
% 6.82/1.51      ( X0 = X1
% 6.82/1.51      | r1_tarski(X0,X1) != iProver_top
% 6.82/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5662,plain,
% 6.82/1.51      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(sK1),u1_struct_0(X0)) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_5654,c_3114]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8672,plain,
% 6.82/1.51      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4506,c_5662]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5639,plain,
% 6.82/1.51      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 6.82/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 6.82/1.51      | r1_tarski(u1_struct_0(X0),u1_struct_0(sK1)) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4506,c_3114]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6554,plain,
% 6.82/1.51      ( m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) = iProver_top
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_6546,c_3107]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8967,plain,
% 6.82/1.51      ( m1_pre_topc(sK2,X0) != iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | u1_struct_0(X0) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_8672,c_32,c_3939,c_4508,c_4513,c_5639,c_6554]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8968,plain,
% 6.82/1.51      ( u1_struct_0(X0) = u1_struct_0(sK1)
% 6.82/1.51      | m1_pre_topc(X0,sK2) != iProver_top
% 6.82/1.51      | m1_pre_topc(sK2,X0) != iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_8967]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8977,plain,
% 6.82/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1)
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2) != iProver_top
% 6.82/1.51      | m1_pre_topc(sK2,sK2) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_6546,c_8968]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3944,plain,
% 6.82/1.51      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK1) ),
% 6.82/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_3939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4584,plain,
% 6.82/1.51      ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)))
% 6.82/1.51      | ~ l1_pre_topc(sK2) ),
% 6.82/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_4508]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_20,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f74]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3099,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X0) = iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_14,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f68]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3103,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5857,plain,
% 6.82/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) = iProver_top
% 6.82/1.51      | l1_pre_topc(sK2) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3103]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6582,plain,
% 6.82/1.51      ( m1_pre_topc(X0,sK2) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_5857,c_32,c_3939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6583,plain,
% 6.82/1.51      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top
% 6.82/1.51      | m1_pre_topc(X0,sK2) = iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_6582]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6591,plain,
% 6.82/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2) = iProver_top
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3099,c_6583]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6613,plain,
% 6.82/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2)
% 6.82/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) ),
% 6.82/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_6591]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_8995,plain,
% 6.82/1.51      ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK2)
% 6.82/1.51      | ~ m1_pre_topc(sK2,sK2)
% 6.82/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(predicate_to_equality_rev,[status(thm)],[c_8977]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9939,plain,
% 6.82/1.51      ( m1_pre_topc(sK2,sK2) | ~ l1_pre_topc(sK2) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_12515,plain,
% 6.82/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_8977,c_31,c_3944,c_4584,c_6613,c_8995,c_9939]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_27979,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 6.82/1.51      | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_27974,c_12515]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_19,plain,
% 6.82/1.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 6.82/1.51      | ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f73]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3100,plain,
% 6.82/1.51      ( m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 6.82/1.51      | m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_12557,plain,
% 6.82/1.51      ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(X0))) = iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_12515,c_3100]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_27984,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(forward_subsumption_resolution,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_27979,c_12557]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_27986,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_27984]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_17,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 6.82/1.51      | ~ l1_pre_topc(X1) ),
% 6.82/1.51      inference(cnf_transformation,[],[f72]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3102,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3094,plain,
% 6.82/1.51      ( l1_pre_topc(sK1) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3930,plain,
% 6.82/1.51      ( k2_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3792,c_3092]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6853,plain,
% 6.82/1.51      ( k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3094,c_3930]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6871,plain,
% 6.82/1.51      ( k1_pre_topc(X0,k2_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_6853,c_3111]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6872,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) != iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_6871,c_6853]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_56,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X0) = iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_58,plain,
% 6.82/1.51      ( m1_pre_topc(sK1,sK1) = iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_56]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_18,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 6.82/1.51      inference(cnf_transformation,[],[f71]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_62,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_64,plain,
% 6.82/1.51      ( m1_pre_topc(sK1,sK1) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_62]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6978,plain,
% 6.82/1.51      ( l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_6872,c_32,c_58,c_64]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6979,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_6978]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6988,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(forward_subsumption_resolution,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_6979,c_3100]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_6993,plain,
% 6.82/1.51      ( k1_pre_topc(X0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | m1_pre_topc(sK1,X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3102,c_6988]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3,plain,
% 6.82/1.51      ( ~ l1_pre_topc(X0)
% 6.82/1.51      | ~ v1_pre_topc(X0)
% 6.82/1.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ),
% 6.82/1.51      inference(cnf_transformation,[],[f57]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3112,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4200,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3792,c_3112]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3346,plain,
% 6.82/1.51      ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 6.82/1.51      | ~ v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_3]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3347,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top
% 6.82/1.51      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_3346]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9071,plain,
% 6.82/1.51      ( l1_pre_topc(X0) != iProver_top
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_4200,c_3347,c_3690,c_3792]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9072,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(renaming,[status(thm)],[c_9071]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9079,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3094,c_9072]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_13,plain,
% 6.82/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(X1)))
% 6.82/1.51      | X2 = X1
% 6.82/1.51      | g1_pre_topc(X2,X3) != g1_pre_topc(X1,X0) ),
% 6.82/1.51      inference(cnf_transformation,[],[f66]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3104,plain,
% 6.82/1.51      ( X0 = X1
% 6.82/1.51      | g1_pre_topc(X0,X2) != g1_pre_topc(X1,X3)
% 6.82/1.51      | m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9105,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(X0,X1)
% 6.82/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X0
% 6.82/1.51      | m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_9079,c_3104]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_9683,plain,
% 6.82/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1)
% 6.82/1.51      | m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) != iProver_top ),
% 6.82/1.51      inference(equality_resolution,[status(thm)],[c_9105]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_57,plain,
% 6.82/1.51      ( m1_pre_topc(sK1,sK1) | ~ l1_pre_topc(sK1) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_20]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_78,plain,
% 6.82/1.51      ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 6.82/1.51      | ~ l1_pre_topc(sK1) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_11]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_625,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X2)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != X2
% 6.82/1.51      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X2 ),
% 6.82/1.51      inference(resolution_lifted,[status(thm)],[c_3,c_18]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_626,plain,
% 6.82/1.51      ( ~ m1_pre_topc(X0,X1)
% 6.82/1.51      | ~ l1_pre_topc(X1)
% 6.82/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 6.82/1.51      inference(unflattening,[status(thm)],[c_625]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_628,plain,
% 6.82/1.51      ( ~ m1_pre_topc(sK1,sK1)
% 6.82/1.51      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
% 6.82/1.51      | ~ l1_pre_topc(sK1)
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_626]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3336,plain,
% 6.82/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_7]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3338,plain,
% 6.82/1.51      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 6.82/1.51      | l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_3336]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_3819,plain,
% 6.82/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
% 6.82/1.51      | X2 = u1_struct_0(X1)
% 6.82/1.51      | g1_pre_topc(X2,X3) != g1_pre_topc(u1_struct_0(X1),X0) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_13]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4761,plain,
% 6.82/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.82/1.51      | X1 = u1_struct_0(X0)
% 6.82/1.51      | g1_pre_topc(X1,X2) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_3819]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_7726,plain,
% 6.82/1.51      ( ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) != g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
% 6.82/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) = u1_struct_0(X0) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_4761]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_7728,plain,
% 6.82/1.51      ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
% 6.82/1.51      | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 6.82/1.51      | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_7726]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_10028,plain,
% 6.82/1.51      ( u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = u1_struct_0(sK1) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_9683,c_31,c_57,c_78,c_628,c_3338,c_7728]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_12123,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 6.82/1.51      | m1_pre_topc(sK1,X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(light_normalisation,[status(thm)],[c_6993,c_10028]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_12131,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_3099,c_12123]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_65,plain,
% 6.82/1.51      ( m1_pre_topc(X0,X1) != iProver_top
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) = iProver_top
% 6.82/1.51      | l1_pre_topc(X1) != iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_67,plain,
% 6.82/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) = iProver_top
% 6.82/1.51      | m1_pre_topc(sK1,sK1) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_65]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_10035,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(X0,u1_struct_0(sK1))
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(demodulation,[status(thm)],[c_10028,c_6988]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_10069,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1))
% 6.82/1.51      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK1) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_10035]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_13299,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 6.82/1.51      inference(global_propositional_subsumption,
% 6.82/1.51                [status(thm)],
% 6.82/1.51                [c_12131,c_32,c_58,c_67,c_10069]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_28,negated_conjecture,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 6.82/1.51      inference(cnf_transformation,[],[f85]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_4487,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
% 6.82/1.51      inference(demodulation,[status(thm)],[c_4479,c_28]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_13314,plain,
% 6.82/1.51      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != k1_pre_topc(sK1,u1_struct_0(sK1)) ),
% 6.82/1.51      inference(demodulation,[status(thm)],[c_13299,c_4487]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5206,plain,
% 6.82/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),X0) = iProver_top
% 6.82/1.51      | m1_pre_topc(sK2,X0) != iProver_top
% 6.82/1.51      | l1_pre_topc(X0) != iProver_top ),
% 6.82/1.51      inference(superposition,[status(thm)],[c_4479,c_3102]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_5228,plain,
% 6.82/1.51      ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)),sK1) = iProver_top
% 6.82/1.51      | m1_pre_topc(sK2,sK1) != iProver_top
% 6.82/1.51      | l1_pre_topc(sK1) != iProver_top ),
% 6.82/1.51      inference(instantiation,[status(thm)],[c_5206]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(c_34,plain,
% 6.82/1.51      ( m1_pre_topc(sK2,sK1) = iProver_top ),
% 6.82/1.51      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 6.82/1.51  
% 6.82/1.51  cnf(contradiction,plain,
% 6.82/1.51      ( $false ),
% 6.82/1.51      inference(minisat,[status(thm)],[c_27986,c_13314,c_5228,c_34,c_32]) ).
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 6.82/1.51  
% 6.82/1.51  ------                               Statistics
% 6.82/1.51  
% 6.82/1.51  ------ General
% 6.82/1.51  
% 6.82/1.51  abstr_ref_over_cycles:                  0
% 6.82/1.51  abstr_ref_under_cycles:                 0
% 6.82/1.51  gc_basic_clause_elim:                   0
% 6.82/1.51  forced_gc_time:                         0
% 6.82/1.51  parsing_time:                           0.012
% 6.82/1.51  unif_index_cands_time:                  0.
% 6.82/1.51  unif_index_add_time:                    0.
% 6.82/1.51  orderings_time:                         0.
% 6.82/1.51  out_proof_time:                         0.015
% 6.82/1.51  total_time:                             0.688
% 6.82/1.51  num_of_symbols:                         48
% 6.82/1.51  num_of_terms:                           15296
% 6.82/1.51  
% 6.82/1.51  ------ Preprocessing
% 6.82/1.51  
% 6.82/1.51  num_of_splits:                          0
% 6.82/1.51  num_of_split_atoms:                     0
% 6.82/1.51  num_of_reused_defs:                     0
% 6.82/1.51  num_eq_ax_congr_red:                    6
% 6.82/1.51  num_of_sem_filtered_clauses:            1
% 6.82/1.51  num_of_subtypes:                        0
% 6.82/1.51  monotx_restored_types:                  0
% 6.82/1.51  sat_num_of_epr_types:                   0
% 6.82/1.51  sat_num_of_non_cyclic_types:            0
% 6.82/1.51  sat_guarded_non_collapsed_types:        0
% 6.82/1.51  num_pure_diseq_elim:                    0
% 6.82/1.51  simp_replaced_by:                       0
% 6.82/1.51  res_preprocessed:                       151
% 6.82/1.51  prep_upred:                             0
% 6.82/1.51  prep_unflattend:                        77
% 6.82/1.51  smt_new_axioms:                         0
% 6.82/1.51  pred_elim_cands:                        6
% 6.82/1.51  pred_elim:                              2
% 6.82/1.51  pred_elim_cl:                           0
% 6.82/1.51  pred_elim_cycles:                       7
% 6.82/1.51  merged_defs:                            0
% 6.82/1.51  merged_defs_ncl:                        0
% 6.82/1.51  bin_hyper_res:                          0
% 6.82/1.51  prep_cycles:                            4
% 6.82/1.51  pred_elim_time:                         0.041
% 6.82/1.51  splitting_time:                         0.
% 6.82/1.51  sem_filter_time:                        0.
% 6.82/1.51  monotx_time:                            0.001
% 6.82/1.51  subtype_inf_time:                       0.
% 6.82/1.51  
% 6.82/1.51  ------ Problem properties
% 6.82/1.51  
% 6.82/1.51  clauses:                                30
% 6.82/1.51  conjectures:                            3
% 6.82/1.51  epr:                                    6
% 6.82/1.51  horn:                                   27
% 6.82/1.51  ground:                                 6
% 6.82/1.51  unary:                                  7
% 6.82/1.51  binary:                                 6
% 6.82/1.51  lits:                                   77
% 6.82/1.51  lits_eq:                                13
% 6.82/1.51  fd_pure:                                0
% 6.82/1.51  fd_pseudo:                              0
% 6.82/1.51  fd_cond:                                0
% 6.82/1.51  fd_pseudo_cond:                         4
% 6.82/1.51  ac_symbols:                             0
% 6.82/1.51  
% 6.82/1.51  ------ Propositional Solver
% 6.82/1.51  
% 6.82/1.51  prop_solver_calls:                      30
% 6.82/1.51  prop_fast_solver_calls:                 2254
% 6.82/1.51  smt_solver_calls:                       0
% 6.82/1.51  smt_fast_solver_calls:                  0
% 6.82/1.51  prop_num_of_clauses:                    7011
% 6.82/1.51  prop_preprocess_simplified:             17885
% 6.82/1.51  prop_fo_subsumed:                       159
% 6.82/1.51  prop_solver_time:                       0.
% 6.82/1.51  smt_solver_time:                        0.
% 6.82/1.51  smt_fast_solver_time:                   0.
% 6.82/1.51  prop_fast_solver_time:                  0.
% 6.82/1.51  prop_unsat_core_time:                   0.
% 6.82/1.51  
% 6.82/1.51  ------ QBF
% 6.82/1.51  
% 6.82/1.51  qbf_q_res:                              0
% 6.82/1.51  qbf_num_tautologies:                    0
% 6.82/1.51  qbf_prep_cycles:                        0
% 6.82/1.51  
% 6.82/1.51  ------ BMC1
% 6.82/1.51  
% 6.82/1.51  bmc1_current_bound:                     -1
% 6.82/1.51  bmc1_last_solved_bound:                 -1
% 6.82/1.51  bmc1_unsat_core_size:                   -1
% 6.82/1.51  bmc1_unsat_core_parents_size:           -1
% 6.82/1.51  bmc1_merge_next_fun:                    0
% 6.82/1.51  bmc1_unsat_core_clauses_time:           0.
% 6.82/1.51  
% 6.82/1.51  ------ Instantiation
% 6.82/1.51  
% 6.82/1.51  inst_num_of_clauses:                    2189
% 6.82/1.51  inst_num_in_passive:                    426
% 6.82/1.51  inst_num_in_active:                     1081
% 6.82/1.51  inst_num_in_unprocessed:                682
% 6.82/1.51  inst_num_of_loops:                      1110
% 6.82/1.51  inst_num_of_learning_restarts:          0
% 6.82/1.51  inst_num_moves_active_passive:          26
% 6.82/1.51  inst_lit_activity:                      0
% 6.82/1.51  inst_lit_activity_moves:                0
% 6.82/1.51  inst_num_tautologies:                   0
% 6.82/1.51  inst_num_prop_implied:                  0
% 6.82/1.51  inst_num_existing_simplified:           0
% 6.82/1.51  inst_num_eq_res_simplified:             0
% 6.82/1.51  inst_num_child_elim:                    0
% 6.82/1.51  inst_num_of_dismatching_blockings:      3400
% 6.82/1.51  inst_num_of_non_proper_insts:           4497
% 6.82/1.51  inst_num_of_duplicates:                 0
% 6.82/1.51  inst_inst_num_from_inst_to_res:         0
% 6.82/1.51  inst_dismatching_checking_time:         0.
% 6.82/1.51  
% 6.82/1.51  ------ Resolution
% 6.82/1.51  
% 6.82/1.51  res_num_of_clauses:                     0
% 6.82/1.51  res_num_in_passive:                     0
% 6.82/1.51  res_num_in_active:                      0
% 6.82/1.51  res_num_of_loops:                       155
% 6.82/1.51  res_forward_subset_subsumed:            702
% 6.82/1.51  res_backward_subset_subsumed:           0
% 6.82/1.51  res_forward_subsumed:                   0
% 6.82/1.51  res_backward_subsumed:                  0
% 6.82/1.51  res_forward_subsumption_resolution:     0
% 6.82/1.51  res_backward_subsumption_resolution:    0
% 6.82/1.51  res_clause_to_clause_subsumption:       2742
% 6.82/1.51  res_orphan_elimination:                 0
% 6.82/1.51  res_tautology_del:                      332
% 6.82/1.51  res_num_eq_res_simplified:              0
% 6.82/1.51  res_num_sel_changes:                    0
% 6.82/1.51  res_moves_from_active_to_pass:          0
% 6.82/1.51  
% 6.82/1.51  ------ Superposition
% 6.82/1.51  
% 6.82/1.51  sup_time_total:                         0.
% 6.82/1.51  sup_time_generating:                    0.
% 6.82/1.51  sup_time_sim_full:                      0.
% 6.82/1.51  sup_time_sim_immed:                     0.
% 6.82/1.51  
% 6.82/1.51  sup_num_of_clauses:                     445
% 6.82/1.51  sup_num_in_active:                      182
% 6.82/1.51  sup_num_in_passive:                     263
% 6.82/1.51  sup_num_of_loops:                       221
% 6.82/1.51  sup_fw_superposition:                   504
% 6.82/1.51  sup_bw_superposition:                   505
% 6.82/1.51  sup_immediate_simplified:               486
% 6.82/1.51  sup_given_eliminated:                   0
% 6.82/1.51  comparisons_done:                       0
% 6.82/1.51  comparisons_avoided:                    0
% 6.82/1.51  
% 6.82/1.51  ------ Simplifications
% 6.82/1.51  
% 6.82/1.51  
% 6.82/1.51  sim_fw_subset_subsumed:                 132
% 6.82/1.51  sim_bw_subset_subsumed:                 48
% 6.82/1.51  sim_fw_subsumed:                        115
% 6.82/1.51  sim_bw_subsumed:                        7
% 6.82/1.51  sim_fw_subsumption_res:                 5
% 6.82/1.51  sim_bw_subsumption_res:                 0
% 6.82/1.51  sim_tautology_del:                      31
% 6.82/1.51  sim_eq_tautology_del:                   72
% 6.82/1.51  sim_eq_res_simp:                        0
% 6.82/1.51  sim_fw_demodulated:                     26
% 6.82/1.51  sim_bw_demodulated:                     36
% 6.82/1.51  sim_light_normalised:                   331
% 6.82/1.51  sim_joinable_taut:                      0
% 6.82/1.51  sim_joinable_simp:                      0
% 6.82/1.51  sim_ac_normalised:                      0
% 6.82/1.51  sim_smt_subsumption:                    0
% 6.82/1.51  
%------------------------------------------------------------------------------
