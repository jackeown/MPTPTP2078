%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:09 EST 2020

% Result     : Theorem 7.27s
% Output     : CNFRefutation 7.27s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 569 expanded)
%              Number of clauses        :   81 ( 144 expanded)
%              Number of leaves         :   12 ( 144 expanded)
%              Depth                    :   20
%              Number of atoms          :  558 (3607 expanded)
%              Number of equality atoms :  160 ( 300 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_tex_2(sK3,X0)
        & v2_tex_2(sK3,X0)
        & v1_tops_1(sK3,X0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v3_tex_2(X1,X0)
            & v2_tex_2(X1,X0)
            & v1_tops_1(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v3_tex_2(X1,sK2)
          & v2_tex_2(X1,sK2)
          & v1_tops_1(X1,sK2)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33,f32])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f6,axiom,(
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

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f26,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK0(X0,X1) != X1
        & r1_tarski(X1,sK0(X0,X1))
        & v2_tex_2(sK0(X0,X1),X0)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK0(X0,X1) != X1
                & r1_tarski(X1,sK0(X0,X1))
                & v2_tex_2(sK0(X0,X1),X0)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f54,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(ennf_transformation,[],[f7])).

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

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1)
        & r1_tarski(sK1(X0,X1),X1)
        & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3
      | ~ r1_tarski(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f57,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f56,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2013,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_21,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_473,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_474,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_2005,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_22,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_326,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_22])).

cnf(c_327,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_326])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_331,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_327,c_23,c_21])).

cnf(c_2011,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_3155,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_2011])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_491,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_21])).

cnf(c_492,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_493,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_21111,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3155,c_493])).

cnf(c_21112,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_21111])).

cnf(c_21118,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_21112])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_18,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_29,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_614,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_492])).

cnf(c_615,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_616,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_625,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_474])).

cnf(c_626,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_625])).

cnf(c_627,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_2138,plain,
    ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK0(sK2,sK3))
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_2151,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2138])).

cnf(c_21229,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21118,c_27,c_29,c_616,c_627,c_2151])).

cnf(c_21236,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_21229])).

cnf(c_6,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_19,negated_conjecture,
    ( v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_317,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_19])).

cnf(c_318,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_320,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_318,c_21,c_20])).

cnf(c_21241,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21236,c_320])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_21])).

cnf(c_546,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_2001,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_546])).

cnf(c_2234,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_320,c_2001])).

cnf(c_2237,plain,
    ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_27])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2016,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2476,plain,
    ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2237,c_2016])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_224,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_185])).

cnf(c_2012,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_224])).

cnf(c_3724,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
    inference(superposition,[status(thm)],[c_2476,c_2012])).

cnf(c_3150,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2005,c_2016])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | k3_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_2018,plain,
    ( k3_xboole_0(X0,X1) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6113,plain,
    ( k3_xboole_0(sK0(sK2,X0),u1_struct_0(sK2)) = sK0(sK2,X0)
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3150,c_2018])).

cnf(c_6979,plain,
    ( k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3)
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2013,c_6113])).

cnf(c_2204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2573,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_2204])).

cnf(c_3247,plain,
    ( ~ r1_tarski(sK0(sK2,sK3),X0)
    | k3_xboole_0(sK0(sK2,sK3),X0) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5106,plain,
    ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
    | k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_6999,plain,
    ( k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6979,c_20,c_18,c_626,c_2573,c_5106])).

cnf(c_21242,plain,
    ( sK0(sK2,sK3) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_21241,c_3724,c_6999])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_509,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_510,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_509])).

cnf(c_603,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_510])).

cnf(c_604,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,sK0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_603])).

cnf(c_605,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_7,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_527,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_21])).

cnf(c_528,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_527])).

cnf(c_595,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_528])).

cnf(c_596,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_21242,c_605,c_596,c_29,c_18,c_27,c_20])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 7.27/1.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.27/1.50  
% 7.27/1.50  ------  iProver source info
% 7.27/1.50  
% 7.27/1.50  git: date: 2020-06-30 10:37:57 +0100
% 7.27/1.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.27/1.50  git: non_committed_changes: false
% 7.27/1.50  git: last_make_outside_of_git: false
% 7.27/1.50  
% 7.27/1.50  ------ 
% 7.27/1.50  
% 7.27/1.50  ------ Input Options
% 7.27/1.50  
% 7.27/1.50  --out_options                           all
% 7.27/1.50  --tptp_safe_out                         true
% 7.27/1.50  --problem_path                          ""
% 7.27/1.50  --include_path                          ""
% 7.27/1.50  --clausifier                            res/vclausify_rel
% 7.27/1.50  --clausifier_options                    ""
% 7.27/1.50  --stdin                                 false
% 7.27/1.50  --stats_out                             all
% 7.27/1.50  
% 7.27/1.50  ------ General Options
% 7.27/1.50  
% 7.27/1.50  --fof                                   false
% 7.27/1.50  --time_out_real                         305.
% 7.27/1.50  --time_out_virtual                      -1.
% 7.27/1.50  --symbol_type_check                     false
% 7.27/1.50  --clausify_out                          false
% 7.27/1.50  --sig_cnt_out                           false
% 7.27/1.50  --trig_cnt_out                          false
% 7.27/1.50  --trig_cnt_out_tolerance                1.
% 7.27/1.50  --trig_cnt_out_sk_spl                   false
% 7.27/1.50  --abstr_cl_out                          false
% 7.27/1.50  
% 7.27/1.50  ------ Global Options
% 7.27/1.50  
% 7.27/1.50  --schedule                              default
% 7.27/1.50  --add_important_lit                     false
% 7.27/1.50  --prop_solver_per_cl                    1000
% 7.27/1.50  --min_unsat_core                        false
% 7.27/1.50  --soft_assumptions                      false
% 7.27/1.50  --soft_lemma_size                       3
% 7.27/1.50  --prop_impl_unit_size                   0
% 7.27/1.50  --prop_impl_unit                        []
% 7.27/1.50  --share_sel_clauses                     true
% 7.27/1.50  --reset_solvers                         false
% 7.27/1.50  --bc_imp_inh                            [conj_cone]
% 7.27/1.50  --conj_cone_tolerance                   3.
% 7.27/1.50  --extra_neg_conj                        none
% 7.27/1.50  --large_theory_mode                     true
% 7.27/1.50  --prolific_symb_bound                   200
% 7.27/1.50  --lt_threshold                          2000
% 7.27/1.50  --clause_weak_htbl                      true
% 7.27/1.50  --gc_record_bc_elim                     false
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing Options
% 7.27/1.50  
% 7.27/1.50  --preprocessing_flag                    true
% 7.27/1.50  --time_out_prep_mult                    0.1
% 7.27/1.50  --splitting_mode                        input
% 7.27/1.50  --splitting_grd                         true
% 7.27/1.50  --splitting_cvd                         false
% 7.27/1.50  --splitting_cvd_svl                     false
% 7.27/1.50  --splitting_nvd                         32
% 7.27/1.50  --sub_typing                            true
% 7.27/1.50  --prep_gs_sim                           true
% 7.27/1.50  --prep_unflatten                        true
% 7.27/1.50  --prep_res_sim                          true
% 7.27/1.50  --prep_upred                            true
% 7.27/1.50  --prep_sem_filter                       exhaustive
% 7.27/1.50  --prep_sem_filter_out                   false
% 7.27/1.50  --pred_elim                             true
% 7.27/1.50  --res_sim_input                         true
% 7.27/1.50  --eq_ax_congr_red                       true
% 7.27/1.50  --pure_diseq_elim                       true
% 7.27/1.50  --brand_transform                       false
% 7.27/1.50  --non_eq_to_eq                          false
% 7.27/1.50  --prep_def_merge                        true
% 7.27/1.50  --prep_def_merge_prop_impl              false
% 7.27/1.50  --prep_def_merge_mbd                    true
% 7.27/1.50  --prep_def_merge_tr_red                 false
% 7.27/1.50  --prep_def_merge_tr_cl                  false
% 7.27/1.50  --smt_preprocessing                     true
% 7.27/1.50  --smt_ac_axioms                         fast
% 7.27/1.50  --preprocessed_out                      false
% 7.27/1.50  --preprocessed_stats                    false
% 7.27/1.50  
% 7.27/1.50  ------ Abstraction refinement Options
% 7.27/1.50  
% 7.27/1.50  --abstr_ref                             []
% 7.27/1.50  --abstr_ref_prep                        false
% 7.27/1.50  --abstr_ref_until_sat                   false
% 7.27/1.50  --abstr_ref_sig_restrict                funpre
% 7.27/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.50  --abstr_ref_under                       []
% 7.27/1.50  
% 7.27/1.50  ------ SAT Options
% 7.27/1.50  
% 7.27/1.50  --sat_mode                              false
% 7.27/1.50  --sat_fm_restart_options                ""
% 7.27/1.50  --sat_gr_def                            false
% 7.27/1.50  --sat_epr_types                         true
% 7.27/1.50  --sat_non_cyclic_types                  false
% 7.27/1.50  --sat_finite_models                     false
% 7.27/1.50  --sat_fm_lemmas                         false
% 7.27/1.50  --sat_fm_prep                           false
% 7.27/1.50  --sat_fm_uc_incr                        true
% 7.27/1.50  --sat_out_model                         small
% 7.27/1.50  --sat_out_clauses                       false
% 7.27/1.50  
% 7.27/1.50  ------ QBF Options
% 7.27/1.50  
% 7.27/1.50  --qbf_mode                              false
% 7.27/1.50  --qbf_elim_univ                         false
% 7.27/1.50  --qbf_dom_inst                          none
% 7.27/1.50  --qbf_dom_pre_inst                      false
% 7.27/1.50  --qbf_sk_in                             false
% 7.27/1.50  --qbf_pred_elim                         true
% 7.27/1.50  --qbf_split                             512
% 7.27/1.50  
% 7.27/1.50  ------ BMC1 Options
% 7.27/1.50  
% 7.27/1.50  --bmc1_incremental                      false
% 7.27/1.50  --bmc1_axioms                           reachable_all
% 7.27/1.50  --bmc1_min_bound                        0
% 7.27/1.50  --bmc1_max_bound                        -1
% 7.27/1.50  --bmc1_max_bound_default                -1
% 7.27/1.50  --bmc1_symbol_reachability              true
% 7.27/1.50  --bmc1_property_lemmas                  false
% 7.27/1.50  --bmc1_k_induction                      false
% 7.27/1.50  --bmc1_non_equiv_states                 false
% 7.27/1.50  --bmc1_deadlock                         false
% 7.27/1.50  --bmc1_ucm                              false
% 7.27/1.50  --bmc1_add_unsat_core                   none
% 7.27/1.50  --bmc1_unsat_core_children              false
% 7.27/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.50  --bmc1_out_stat                         full
% 7.27/1.50  --bmc1_ground_init                      false
% 7.27/1.50  --bmc1_pre_inst_next_state              false
% 7.27/1.50  --bmc1_pre_inst_state                   false
% 7.27/1.50  --bmc1_pre_inst_reach_state             false
% 7.27/1.50  --bmc1_out_unsat_core                   false
% 7.27/1.50  --bmc1_aig_witness_out                  false
% 7.27/1.50  --bmc1_verbose                          false
% 7.27/1.50  --bmc1_dump_clauses_tptp                false
% 7.27/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.50  --bmc1_dump_file                        -
% 7.27/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.50  --bmc1_ucm_extend_mode                  1
% 7.27/1.50  --bmc1_ucm_init_mode                    2
% 7.27/1.50  --bmc1_ucm_cone_mode                    none
% 7.27/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.50  --bmc1_ucm_relax_model                  4
% 7.27/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.50  --bmc1_ucm_layered_model                none
% 7.27/1.50  --bmc1_ucm_max_lemma_size               10
% 7.27/1.50  
% 7.27/1.50  ------ AIG Options
% 7.27/1.50  
% 7.27/1.50  --aig_mode                              false
% 7.27/1.50  
% 7.27/1.50  ------ Instantiation Options
% 7.27/1.50  
% 7.27/1.50  --instantiation_flag                    true
% 7.27/1.50  --inst_sos_flag                         true
% 7.27/1.50  --inst_sos_phase                        true
% 7.27/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.50  --inst_lit_sel_side                     num_symb
% 7.27/1.50  --inst_solver_per_active                1400
% 7.27/1.50  --inst_solver_calls_frac                1.
% 7.27/1.50  --inst_passive_queue_type               priority_queues
% 7.27/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.50  --inst_passive_queues_freq              [25;2]
% 7.27/1.50  --inst_dismatching                      true
% 7.27/1.50  --inst_eager_unprocessed_to_passive     true
% 7.27/1.50  --inst_prop_sim_given                   true
% 7.27/1.50  --inst_prop_sim_new                     false
% 7.27/1.50  --inst_subs_new                         false
% 7.27/1.50  --inst_eq_res_simp                      false
% 7.27/1.50  --inst_subs_given                       false
% 7.27/1.50  --inst_orphan_elimination               true
% 7.27/1.50  --inst_learning_loop_flag               true
% 7.27/1.50  --inst_learning_start                   3000
% 7.27/1.50  --inst_learning_factor                  2
% 7.27/1.50  --inst_start_prop_sim_after_learn       3
% 7.27/1.50  --inst_sel_renew                        solver
% 7.27/1.50  --inst_lit_activity_flag                true
% 7.27/1.50  --inst_restr_to_given                   false
% 7.27/1.50  --inst_activity_threshold               500
% 7.27/1.50  --inst_out_proof                        true
% 7.27/1.50  
% 7.27/1.50  ------ Resolution Options
% 7.27/1.50  
% 7.27/1.50  --resolution_flag                       true
% 7.27/1.50  --res_lit_sel                           adaptive
% 7.27/1.50  --res_lit_sel_side                      none
% 7.27/1.50  --res_ordering                          kbo
% 7.27/1.50  --res_to_prop_solver                    active
% 7.27/1.50  --res_prop_simpl_new                    false
% 7.27/1.50  --res_prop_simpl_given                  true
% 7.27/1.50  --res_passive_queue_type                priority_queues
% 7.27/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.50  --res_passive_queues_freq               [15;5]
% 7.27/1.50  --res_forward_subs                      full
% 7.27/1.50  --res_backward_subs                     full
% 7.27/1.50  --res_forward_subs_resolution           true
% 7.27/1.50  --res_backward_subs_resolution          true
% 7.27/1.50  --res_orphan_elimination                true
% 7.27/1.50  --res_time_limit                        2.
% 7.27/1.50  --res_out_proof                         true
% 7.27/1.50  
% 7.27/1.50  ------ Superposition Options
% 7.27/1.50  
% 7.27/1.50  --superposition_flag                    true
% 7.27/1.50  --sup_passive_queue_type                priority_queues
% 7.27/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.50  --demod_completeness_check              fast
% 7.27/1.50  --demod_use_ground                      true
% 7.27/1.50  --sup_to_prop_solver                    passive
% 7.27/1.50  --sup_prop_simpl_new                    true
% 7.27/1.50  --sup_prop_simpl_given                  true
% 7.27/1.50  --sup_fun_splitting                     true
% 7.27/1.50  --sup_smt_interval                      50000
% 7.27/1.50  
% 7.27/1.50  ------ Superposition Simplification Setup
% 7.27/1.50  
% 7.27/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.27/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.27/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.27/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.27/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.27/1.50  --sup_immed_triv                        [TrivRules]
% 7.27/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_immed_bw_main                     []
% 7.27/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.27/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_input_bw                          []
% 7.27/1.50  
% 7.27/1.50  ------ Combination Options
% 7.27/1.50  
% 7.27/1.50  --comb_res_mult                         3
% 7.27/1.50  --comb_sup_mult                         2
% 7.27/1.50  --comb_inst_mult                        10
% 7.27/1.50  
% 7.27/1.50  ------ Debug Options
% 7.27/1.50  
% 7.27/1.50  --dbg_backtrace                         false
% 7.27/1.50  --dbg_dump_prop_clauses                 false
% 7.27/1.50  --dbg_dump_prop_clauses_file            -
% 7.27/1.50  --dbg_out_stat                          false
% 7.27/1.50  ------ Parsing...
% 7.27/1.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.27/1.50  ------ Proving...
% 7.27/1.50  ------ Problem Properties 
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  clauses                                 19
% 7.27/1.50  conjectures                             3
% 7.27/1.50  EPR                                     2
% 7.27/1.50  Horn                                    14
% 7.27/1.50  unary                                   4
% 7.27/1.50  binary                                  5
% 7.27/1.50  lits                                    53
% 7.27/1.50  lits eq                                 7
% 7.27/1.50  fd_pure                                 0
% 7.27/1.50  fd_pseudo                               0
% 7.27/1.50  fd_cond                                 0
% 7.27/1.50  fd_pseudo_cond                          1
% 7.27/1.50  AC symbols                              0
% 7.27/1.50  
% 7.27/1.50  ------ Schedule dynamic 5 is on 
% 7.27/1.50  
% 7.27/1.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  ------ 
% 7.27/1.50  Current options:
% 7.27/1.50  ------ 
% 7.27/1.50  
% 7.27/1.50  ------ Input Options
% 7.27/1.50  
% 7.27/1.50  --out_options                           all
% 7.27/1.50  --tptp_safe_out                         true
% 7.27/1.50  --problem_path                          ""
% 7.27/1.50  --include_path                          ""
% 7.27/1.50  --clausifier                            res/vclausify_rel
% 7.27/1.50  --clausifier_options                    ""
% 7.27/1.50  --stdin                                 false
% 7.27/1.50  --stats_out                             all
% 7.27/1.50  
% 7.27/1.50  ------ General Options
% 7.27/1.50  
% 7.27/1.50  --fof                                   false
% 7.27/1.50  --time_out_real                         305.
% 7.27/1.50  --time_out_virtual                      -1.
% 7.27/1.50  --symbol_type_check                     false
% 7.27/1.50  --clausify_out                          false
% 7.27/1.50  --sig_cnt_out                           false
% 7.27/1.50  --trig_cnt_out                          false
% 7.27/1.50  --trig_cnt_out_tolerance                1.
% 7.27/1.50  --trig_cnt_out_sk_spl                   false
% 7.27/1.50  --abstr_cl_out                          false
% 7.27/1.50  
% 7.27/1.50  ------ Global Options
% 7.27/1.50  
% 7.27/1.50  --schedule                              default
% 7.27/1.50  --add_important_lit                     false
% 7.27/1.50  --prop_solver_per_cl                    1000
% 7.27/1.50  --min_unsat_core                        false
% 7.27/1.50  --soft_assumptions                      false
% 7.27/1.50  --soft_lemma_size                       3
% 7.27/1.50  --prop_impl_unit_size                   0
% 7.27/1.50  --prop_impl_unit                        []
% 7.27/1.50  --share_sel_clauses                     true
% 7.27/1.50  --reset_solvers                         false
% 7.27/1.50  --bc_imp_inh                            [conj_cone]
% 7.27/1.50  --conj_cone_tolerance                   3.
% 7.27/1.50  --extra_neg_conj                        none
% 7.27/1.50  --large_theory_mode                     true
% 7.27/1.50  --prolific_symb_bound                   200
% 7.27/1.50  --lt_threshold                          2000
% 7.27/1.50  --clause_weak_htbl                      true
% 7.27/1.50  --gc_record_bc_elim                     false
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing Options
% 7.27/1.50  
% 7.27/1.50  --preprocessing_flag                    true
% 7.27/1.50  --time_out_prep_mult                    0.1
% 7.27/1.50  --splitting_mode                        input
% 7.27/1.50  --splitting_grd                         true
% 7.27/1.50  --splitting_cvd                         false
% 7.27/1.50  --splitting_cvd_svl                     false
% 7.27/1.50  --splitting_nvd                         32
% 7.27/1.50  --sub_typing                            true
% 7.27/1.50  --prep_gs_sim                           true
% 7.27/1.50  --prep_unflatten                        true
% 7.27/1.50  --prep_res_sim                          true
% 7.27/1.50  --prep_upred                            true
% 7.27/1.50  --prep_sem_filter                       exhaustive
% 7.27/1.50  --prep_sem_filter_out                   false
% 7.27/1.50  --pred_elim                             true
% 7.27/1.50  --res_sim_input                         true
% 7.27/1.50  --eq_ax_congr_red                       true
% 7.27/1.50  --pure_diseq_elim                       true
% 7.27/1.50  --brand_transform                       false
% 7.27/1.50  --non_eq_to_eq                          false
% 7.27/1.50  --prep_def_merge                        true
% 7.27/1.50  --prep_def_merge_prop_impl              false
% 7.27/1.50  --prep_def_merge_mbd                    true
% 7.27/1.50  --prep_def_merge_tr_red                 false
% 7.27/1.50  --prep_def_merge_tr_cl                  false
% 7.27/1.50  --smt_preprocessing                     true
% 7.27/1.50  --smt_ac_axioms                         fast
% 7.27/1.50  --preprocessed_out                      false
% 7.27/1.50  --preprocessed_stats                    false
% 7.27/1.50  
% 7.27/1.50  ------ Abstraction refinement Options
% 7.27/1.50  
% 7.27/1.50  --abstr_ref                             []
% 7.27/1.50  --abstr_ref_prep                        false
% 7.27/1.50  --abstr_ref_until_sat                   false
% 7.27/1.50  --abstr_ref_sig_restrict                funpre
% 7.27/1.50  --abstr_ref_af_restrict_to_split_sk     false
% 7.27/1.50  --abstr_ref_under                       []
% 7.27/1.50  
% 7.27/1.50  ------ SAT Options
% 7.27/1.50  
% 7.27/1.50  --sat_mode                              false
% 7.27/1.50  --sat_fm_restart_options                ""
% 7.27/1.50  --sat_gr_def                            false
% 7.27/1.50  --sat_epr_types                         true
% 7.27/1.50  --sat_non_cyclic_types                  false
% 7.27/1.50  --sat_finite_models                     false
% 7.27/1.50  --sat_fm_lemmas                         false
% 7.27/1.50  --sat_fm_prep                           false
% 7.27/1.50  --sat_fm_uc_incr                        true
% 7.27/1.50  --sat_out_model                         small
% 7.27/1.50  --sat_out_clauses                       false
% 7.27/1.50  
% 7.27/1.50  ------ QBF Options
% 7.27/1.50  
% 7.27/1.50  --qbf_mode                              false
% 7.27/1.50  --qbf_elim_univ                         false
% 7.27/1.50  --qbf_dom_inst                          none
% 7.27/1.50  --qbf_dom_pre_inst                      false
% 7.27/1.50  --qbf_sk_in                             false
% 7.27/1.50  --qbf_pred_elim                         true
% 7.27/1.50  --qbf_split                             512
% 7.27/1.50  
% 7.27/1.50  ------ BMC1 Options
% 7.27/1.50  
% 7.27/1.50  --bmc1_incremental                      false
% 7.27/1.50  --bmc1_axioms                           reachable_all
% 7.27/1.50  --bmc1_min_bound                        0
% 7.27/1.50  --bmc1_max_bound                        -1
% 7.27/1.50  --bmc1_max_bound_default                -1
% 7.27/1.50  --bmc1_symbol_reachability              true
% 7.27/1.50  --bmc1_property_lemmas                  false
% 7.27/1.50  --bmc1_k_induction                      false
% 7.27/1.50  --bmc1_non_equiv_states                 false
% 7.27/1.50  --bmc1_deadlock                         false
% 7.27/1.50  --bmc1_ucm                              false
% 7.27/1.50  --bmc1_add_unsat_core                   none
% 7.27/1.50  --bmc1_unsat_core_children              false
% 7.27/1.50  --bmc1_unsat_core_extrapolate_axioms    false
% 7.27/1.50  --bmc1_out_stat                         full
% 7.27/1.50  --bmc1_ground_init                      false
% 7.27/1.50  --bmc1_pre_inst_next_state              false
% 7.27/1.50  --bmc1_pre_inst_state                   false
% 7.27/1.50  --bmc1_pre_inst_reach_state             false
% 7.27/1.50  --bmc1_out_unsat_core                   false
% 7.27/1.50  --bmc1_aig_witness_out                  false
% 7.27/1.50  --bmc1_verbose                          false
% 7.27/1.50  --bmc1_dump_clauses_tptp                false
% 7.27/1.50  --bmc1_dump_unsat_core_tptp             false
% 7.27/1.50  --bmc1_dump_file                        -
% 7.27/1.50  --bmc1_ucm_expand_uc_limit              128
% 7.27/1.50  --bmc1_ucm_n_expand_iterations          6
% 7.27/1.50  --bmc1_ucm_extend_mode                  1
% 7.27/1.50  --bmc1_ucm_init_mode                    2
% 7.27/1.50  --bmc1_ucm_cone_mode                    none
% 7.27/1.50  --bmc1_ucm_reduced_relation_type        0
% 7.27/1.50  --bmc1_ucm_relax_model                  4
% 7.27/1.50  --bmc1_ucm_full_tr_after_sat            true
% 7.27/1.50  --bmc1_ucm_expand_neg_assumptions       false
% 7.27/1.50  --bmc1_ucm_layered_model                none
% 7.27/1.50  --bmc1_ucm_max_lemma_size               10
% 7.27/1.50  
% 7.27/1.50  ------ AIG Options
% 7.27/1.50  
% 7.27/1.50  --aig_mode                              false
% 7.27/1.50  
% 7.27/1.50  ------ Instantiation Options
% 7.27/1.50  
% 7.27/1.50  --instantiation_flag                    true
% 7.27/1.50  --inst_sos_flag                         true
% 7.27/1.50  --inst_sos_phase                        true
% 7.27/1.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.27/1.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.27/1.50  --inst_lit_sel_side                     none
% 7.27/1.50  --inst_solver_per_active                1400
% 7.27/1.50  --inst_solver_calls_frac                1.
% 7.27/1.50  --inst_passive_queue_type               priority_queues
% 7.27/1.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.27/1.50  --inst_passive_queues_freq              [25;2]
% 7.27/1.50  --inst_dismatching                      true
% 7.27/1.50  --inst_eager_unprocessed_to_passive     true
% 7.27/1.50  --inst_prop_sim_given                   true
% 7.27/1.50  --inst_prop_sim_new                     false
% 7.27/1.50  --inst_subs_new                         false
% 7.27/1.50  --inst_eq_res_simp                      false
% 7.27/1.50  --inst_subs_given                       false
% 7.27/1.50  --inst_orphan_elimination               true
% 7.27/1.50  --inst_learning_loop_flag               true
% 7.27/1.50  --inst_learning_start                   3000
% 7.27/1.50  --inst_learning_factor                  2
% 7.27/1.50  --inst_start_prop_sim_after_learn       3
% 7.27/1.50  --inst_sel_renew                        solver
% 7.27/1.50  --inst_lit_activity_flag                true
% 7.27/1.50  --inst_restr_to_given                   false
% 7.27/1.50  --inst_activity_threshold               500
% 7.27/1.50  --inst_out_proof                        true
% 7.27/1.50  
% 7.27/1.50  ------ Resolution Options
% 7.27/1.50  
% 7.27/1.50  --resolution_flag                       false
% 7.27/1.50  --res_lit_sel                           adaptive
% 7.27/1.50  --res_lit_sel_side                      none
% 7.27/1.50  --res_ordering                          kbo
% 7.27/1.50  --res_to_prop_solver                    active
% 7.27/1.50  --res_prop_simpl_new                    false
% 7.27/1.50  --res_prop_simpl_given                  true
% 7.27/1.50  --res_passive_queue_type                priority_queues
% 7.27/1.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.27/1.50  --res_passive_queues_freq               [15;5]
% 7.27/1.50  --res_forward_subs                      full
% 7.27/1.50  --res_backward_subs                     full
% 7.27/1.50  --res_forward_subs_resolution           true
% 7.27/1.50  --res_backward_subs_resolution          true
% 7.27/1.50  --res_orphan_elimination                true
% 7.27/1.50  --res_time_limit                        2.
% 7.27/1.50  --res_out_proof                         true
% 7.27/1.50  
% 7.27/1.50  ------ Superposition Options
% 7.27/1.50  
% 7.27/1.50  --superposition_flag                    true
% 7.27/1.50  --sup_passive_queue_type                priority_queues
% 7.27/1.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.27/1.50  --sup_passive_queues_freq               [8;1;4]
% 7.27/1.50  --demod_completeness_check              fast
% 7.27/1.50  --demod_use_ground                      true
% 7.27/1.50  --sup_to_prop_solver                    passive
% 7.27/1.50  --sup_prop_simpl_new                    true
% 7.27/1.50  --sup_prop_simpl_given                  true
% 7.27/1.50  --sup_fun_splitting                     true
% 7.27/1.50  --sup_smt_interval                      50000
% 7.27/1.50  
% 7.27/1.50  ------ Superposition Simplification Setup
% 7.27/1.50  
% 7.27/1.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.27/1.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.27/1.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.27/1.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.27/1.50  --sup_full_triv                         [TrivRules;PropSubs]
% 7.27/1.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.27/1.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.27/1.50  --sup_immed_triv                        [TrivRules]
% 7.27/1.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_immed_bw_main                     []
% 7.27/1.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.27/1.50  --sup_input_triv                        [Unflattening;TrivRules]
% 7.27/1.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.27/1.50  --sup_input_bw                          []
% 7.27/1.50  
% 7.27/1.50  ------ Combination Options
% 7.27/1.50  
% 7.27/1.50  --comb_res_mult                         3
% 7.27/1.50  --comb_sup_mult                         2
% 7.27/1.50  --comb_inst_mult                        10
% 7.27/1.50  
% 7.27/1.50  ------ Debug Options
% 7.27/1.50  
% 7.27/1.50  --dbg_backtrace                         false
% 7.27/1.50  --dbg_dump_prop_clauses                 false
% 7.27/1.50  --dbg_dump_prop_clauses_file            -
% 7.27/1.50  --dbg_out_stat                          false
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  ------ Proving...
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  % SZS status Theorem for theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  % SZS output start CNFRefutation for theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  fof(f8,conjecture,(
% 7.27/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f9,negated_conjecture,(
% 7.27/1.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 7.27/1.50    inference(negated_conjecture,[],[f8])).
% 7.27/1.50  
% 7.27/1.50  fof(f19,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f9])).
% 7.27/1.50  
% 7.27/1.50  fof(f20,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f19])).
% 7.27/1.50  
% 7.27/1.50  fof(f33,plain,(
% 7.27/1.50    ( ! [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3,X0) & v2_tex_2(sK3,X0) & v1_tops_1(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f32,plain,(
% 7.27/1.50    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f34,plain,(
% 7.27/1.50    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 7.27/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f33,f32])).
% 7.27/1.50  
% 7.27/1.50  fof(f55,plain,(
% 7.27/1.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f6,axiom,(
% 7.27/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f15,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(ennf_transformation,[],[f6])).
% 7.27/1.50  
% 7.27/1.50  fof(f16,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f15])).
% 7.27/1.50  
% 7.27/1.50  fof(f23,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(nnf_transformation,[],[f16])).
% 7.27/1.50  
% 7.27/1.50  fof(f24,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f23])).
% 7.27/1.50  
% 7.27/1.50  fof(f25,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(rectify,[],[f24])).
% 7.27/1.50  
% 7.27/1.50  fof(f26,plain,(
% 7.27/1.50    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f27,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f26])).
% 7.27/1.50  
% 7.27/1.50  fof(f44,plain,(
% 7.27/1.50    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f27])).
% 7.27/1.50  
% 7.27/1.50  fof(f54,plain,(
% 7.27/1.50    l1_pre_topc(sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f7,axiom,(
% 7.27/1.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f17,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f7])).
% 7.27/1.50  
% 7.27/1.50  fof(f18,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(flattening,[],[f17])).
% 7.27/1.50  
% 7.27/1.50  fof(f28,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(nnf_transformation,[],[f18])).
% 7.27/1.50  
% 7.27/1.50  fof(f29,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(rectify,[],[f28])).
% 7.27/1.50  
% 7.27/1.50  fof(f30,plain,(
% 7.27/1.50    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 7.27/1.50    introduced(choice_axiom,[])).
% 7.27/1.50  
% 7.27/1.50  fof(f31,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 7.27/1.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f29,f30])).
% 7.27/1.50  
% 7.27/1.50  fof(f48,plain,(
% 7.27/1.50    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f31])).
% 7.27/1.50  
% 7.27/1.50  fof(f53,plain,(
% 7.27/1.50    v2_pre_topc(sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f52,plain,(
% 7.27/1.50    ~v2_struct_0(sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f45,plain,(
% 7.27/1.50    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f27])).
% 7.27/1.50  
% 7.27/1.50  fof(f57,plain,(
% 7.27/1.50    v2_tex_2(sK3,sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f58,plain,(
% 7.27/1.50    ~v3_tex_2(sK3,sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f5,axiom,(
% 7.27/1.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f14,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(ennf_transformation,[],[f5])).
% 7.27/1.50  
% 7.27/1.50  fof(f22,plain,(
% 7.27/1.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(nnf_transformation,[],[f14])).
% 7.27/1.50  
% 7.27/1.50  fof(f40,plain,(
% 7.27/1.50    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f22])).
% 7.27/1.50  
% 7.27/1.50  fof(f56,plain,(
% 7.27/1.50    v1_tops_1(sK3,sK2)),
% 7.27/1.50    inference(cnf_transformation,[],[f34])).
% 7.27/1.50  
% 7.27/1.50  fof(f4,axiom,(
% 7.27/1.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f12,plain,(
% 7.27/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f4])).
% 7.27/1.50  
% 7.27/1.50  fof(f13,plain,(
% 7.27/1.50    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 7.27/1.50    inference(flattening,[],[f12])).
% 7.27/1.50  
% 7.27/1.50  fof(f39,plain,(
% 7.27/1.50    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f13])).
% 7.27/1.50  
% 7.27/1.50  fof(f3,axiom,(
% 7.27/1.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f21,plain,(
% 7.27/1.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.27/1.50    inference(nnf_transformation,[],[f3])).
% 7.27/1.50  
% 7.27/1.50  fof(f37,plain,(
% 7.27/1.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.27/1.50    inference(cnf_transformation,[],[f21])).
% 7.27/1.50  
% 7.27/1.50  fof(f2,axiom,(
% 7.27/1.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f11,plain,(
% 7.27/1.50    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 7.27/1.50    inference(ennf_transformation,[],[f2])).
% 7.27/1.50  
% 7.27/1.50  fof(f36,plain,(
% 7.27/1.50    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 7.27/1.50    inference(cnf_transformation,[],[f11])).
% 7.27/1.50  
% 7.27/1.50  fof(f38,plain,(
% 7.27/1.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f21])).
% 7.27/1.50  
% 7.27/1.50  fof(f1,axiom,(
% 7.27/1.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 7.27/1.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.27/1.50  
% 7.27/1.50  fof(f10,plain,(
% 7.27/1.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 7.27/1.50    inference(ennf_transformation,[],[f1])).
% 7.27/1.50  
% 7.27/1.50  fof(f35,plain,(
% 7.27/1.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f10])).
% 7.27/1.50  
% 7.27/1.50  fof(f46,plain,(
% 7.27/1.50    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f27])).
% 7.27/1.50  
% 7.27/1.50  fof(f47,plain,(
% 7.27/1.50    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 7.27/1.50    inference(cnf_transformation,[],[f27])).
% 7.27/1.50  
% 7.27/1.50  cnf(c_20,negated_conjecture,
% 7.27/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(cnf_transformation,[],[f55]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2013,plain,
% 7.27/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_10,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f44]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21,negated_conjecture,
% 7.27/1.50      ( l1_pre_topc(sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f54]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_473,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_474,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | v3_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_473]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2005,plain,
% 7.27/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_474]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_16,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X2,X0)
% 7.27/1.50      | v2_struct_0(X1)
% 7.27/1.50      | ~ v2_pre_topc(X1)
% 7.27/1.50      | ~ l1_pre_topc(X1)
% 7.27/1.50      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 7.27/1.50      inference(cnf_transformation,[],[f48]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_22,negated_conjecture,
% 7.27/1.50      ( v2_pre_topc(sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f53]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_326,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ r1_tarski(X2,X0)
% 7.27/1.50      | v2_struct_0(X1)
% 7.27/1.50      | ~ l1_pre_topc(X1)
% 7.27/1.50      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_16,c_22]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_327,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | v2_struct_0(sK2)
% 7.27/1.50      | ~ l1_pre_topc(sK2)
% 7.27/1.50      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_326]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_23,negated_conjecture,
% 7.27/1.50      ( ~ v2_struct_0(sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f52]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_331,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ r1_tarski(X1,X0)
% 7.27/1.50      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_327,c_23,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2011,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 7.27/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,X0) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3155,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 7.27/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2005,c_2011]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_9,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v2_tex_2(sK0(X1,X0),X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f45]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_491,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v2_tex_2(sK0(X1,X0),X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_9,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_492,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | v2_tex_2(sK0(sK2,X0),sK2)
% 7.27/1.50      | v3_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_491]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_493,plain,
% 7.27/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21111,plain,
% 7.27/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_3155,c_493]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21112,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 7.27/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 7.27/1.50      inference(renaming,[status(thm)],[c_21111]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21118,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 7.27/1.50      | v2_tex_2(sK3,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(sK3,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2013,c_21112]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_27,plain,
% 7.27/1.50      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_18,negated_conjecture,
% 7.27/1.50      ( v2_tex_2(sK3,sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f57]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_29,plain,
% 7.27/1.50      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_17,negated_conjecture,
% 7.27/1.50      ( ~ v3_tex_2(sK3,sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f58]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_614,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | v2_tex_2(sK0(sK2,X0),sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | sK2 != sK2
% 7.27/1.50      | sK3 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_492]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_615,plain,
% 7.27/1.50      ( v2_tex_2(sK0(sK2,sK3),sK2)
% 7.27/1.50      | ~ v2_tex_2(sK3,sK2)
% 7.27/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_614]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_616,plain,
% 7.27/1.50      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
% 7.27/1.50      | v2_tex_2(sK3,sK2) != iProver_top
% 7.27/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_625,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | sK2 != sK2
% 7.27/1.50      | sK3 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_474]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_626,plain,
% 7.27/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.27/1.50      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_625]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_627,plain,
% 7.27/1.50      ( v2_tex_2(sK3,sK2) != iProver_top
% 7.27/1.50      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.27/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2138,plain,
% 7.27/1.50      ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ r1_tarski(X0,sK0(sK2,sK3))
% 7.27/1.50      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_331]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2151,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 7.27/1.50      | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_2138]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21229,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_21118,c_27,c_29,c_616,c_627,c_2151]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21236,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
% 7.27/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2013,c_21229]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6,plain,
% 7.27/1.50      ( ~ v1_tops_1(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1)
% 7.27/1.50      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f40]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_19,negated_conjecture,
% 7.27/1.50      ( v1_tops_1(sK3,sK2) ),
% 7.27/1.50      inference(cnf_transformation,[],[f56]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_317,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1)
% 7.27/1.50      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 7.27/1.50      | sK2 != X1
% 7.27/1.50      | sK3 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_6,c_19]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_318,plain,
% 7.27/1.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | ~ l1_pre_topc(sK2)
% 7.27/1.50      | k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_317]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_320,plain,
% 7.27/1.50      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_318,c_21,c_20]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21241,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 7.27/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(light_normalisation,[status(thm)],[c_21236,c_320]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_4,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f39]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_545,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | m1_subset_1(k2_pre_topc(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_4,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_546,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_545]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2001,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | m1_subset_1(k2_pre_topc(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_546]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2234,plain,
% 7.27/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 7.27/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_320,c_2001]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2237,plain,
% 7.27/1.50      ( m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_2234,c_27]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f37]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2016,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.27/1.50      | r1_tarski(X0,X1) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2476,plain,
% 7.27/1.50      ( r1_tarski(u1_struct_0(sK2),u1_struct_0(sK2)) = iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2237,c_2016]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_1,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 7.27/1.50      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.27/1.50      inference(cnf_transformation,[],[f36]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f38]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_184,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 7.27/1.50      inference(prop_impl,[status(thm)],[c_2]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_185,plain,
% 7.27/1.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.27/1.50      inference(renaming,[status(thm)],[c_184]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_224,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 7.27/1.50      inference(bin_hyper_res,[status(thm)],[c_1,c_185]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2012,plain,
% 7.27/1.50      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 7.27/1.50      | r1_tarski(X2,X0) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_224]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3724,plain,
% 7.27/1.50      ( k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)) = k3_xboole_0(X0,u1_struct_0(sK2)) ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2476,c_2012]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3150,plain,
% 7.27/1.50      ( v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2005,c_2016]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_0,plain,
% 7.27/1.50      ( ~ r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0 ),
% 7.27/1.50      inference(cnf_transformation,[],[f35]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2018,plain,
% 7.27/1.50      ( k3_xboole_0(X0,X1) = X0 | r1_tarski(X0,X1) != iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6113,plain,
% 7.27/1.50      ( k3_xboole_0(sK0(sK2,X0),u1_struct_0(sK2)) = sK0(sK2,X0)
% 7.27/1.50      | v2_tex_2(X0,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(X0,sK2) = iProver_top
% 7.27/1.50      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_3150,c_2018]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6979,plain,
% 7.27/1.50      ( k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3)
% 7.27/1.50      | v2_tex_2(sK3,sK2) != iProver_top
% 7.27/1.50      | v3_tex_2(sK3,sK2) = iProver_top ),
% 7.27/1.50      inference(superposition,[status(thm)],[c_2013,c_6113]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2204,plain,
% 7.27/1.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_3]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_2573,plain,
% 7.27/1.50      ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_2204]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_3247,plain,
% 7.27/1.50      ( ~ r1_tarski(sK0(sK2,sK3),X0)
% 7.27/1.50      | k3_xboole_0(sK0(sK2,sK3),X0) = sK0(sK2,sK3) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_0]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_5106,plain,
% 7.27/1.50      ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
% 7.27/1.50      | k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
% 7.27/1.50      inference(instantiation,[status(thm)],[c_3247]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_6999,plain,
% 7.27/1.50      ( k3_xboole_0(sK0(sK2,sK3),u1_struct_0(sK2)) = sK0(sK2,sK3) ),
% 7.27/1.50      inference(global_propositional_subsumption,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_6979,c_20,c_18,c_626,c_2573,c_5106]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_21242,plain,
% 7.27/1.50      ( sK0(sK2,sK3) = sK3 | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 7.27/1.50      inference(demodulation,[status(thm)],[c_21241,c_3724,c_6999]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_8,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | r1_tarski(X0,sK0(X1,X0))
% 7.27/1.50      | ~ l1_pre_topc(X1) ),
% 7.27/1.50      inference(cnf_transformation,[],[f46]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_509,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | r1_tarski(X0,sK0(X1,X0))
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_510,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | v3_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | r1_tarski(X0,sK0(sK2,X0)) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_509]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_603,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | r1_tarski(X0,sK0(sK2,X0))
% 7.27/1.50      | sK2 != sK2
% 7.27/1.50      | sK3 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_510]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_604,plain,
% 7.27/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.27/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_603]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_605,plain,
% 7.27/1.50      ( v2_tex_2(sK3,sK2) != iProver_top
% 7.27/1.50      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 7.27/1.50      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 7.27/1.50      inference(predicate_to_equality,[status(thm)],[c_604]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_7,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | ~ l1_pre_topc(X1)
% 7.27/1.50      | sK0(X1,X0) != X0 ),
% 7.27/1.50      inference(cnf_transformation,[],[f47]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_527,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,X1)
% 7.27/1.50      | v3_tex_2(X0,X1)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 7.27/1.50      | sK0(X1,X0) != X0
% 7.27/1.50      | sK2 != X1 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_7,c_21]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_528,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | v3_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | sK0(sK2,X0) != X0 ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_527]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_595,plain,
% 7.27/1.50      ( ~ v2_tex_2(X0,sK2)
% 7.27/1.50      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | sK0(sK2,X0) != X0
% 7.27/1.50      | sK2 != sK2
% 7.27/1.50      | sK3 != X0 ),
% 7.27/1.50      inference(resolution_lifted,[status(thm)],[c_17,c_528]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(c_596,plain,
% 7.27/1.50      ( ~ v2_tex_2(sK3,sK2)
% 7.27/1.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 7.27/1.50      | sK0(sK2,sK3) != sK3 ),
% 7.27/1.50      inference(unflattening,[status(thm)],[c_595]) ).
% 7.27/1.50  
% 7.27/1.50  cnf(contradiction,plain,
% 7.27/1.50      ( $false ),
% 7.27/1.50      inference(minisat,
% 7.27/1.50                [status(thm)],
% 7.27/1.50                [c_21242,c_605,c_596,c_29,c_18,c_27,c_20]) ).
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  % SZS output end CNFRefutation for theBenchmark.p
% 7.27/1.50  
% 7.27/1.50  ------                               Statistics
% 7.27/1.50  
% 7.27/1.50  ------ General
% 7.27/1.50  
% 7.27/1.50  abstr_ref_over_cycles:                  0
% 7.27/1.50  abstr_ref_under_cycles:                 0
% 7.27/1.50  gc_basic_clause_elim:                   0
% 7.27/1.50  forced_gc_time:                         0
% 7.27/1.50  parsing_time:                           0.008
% 7.27/1.50  unif_index_cands_time:                  0.
% 7.27/1.50  unif_index_add_time:                    0.
% 7.27/1.50  orderings_time:                         0.
% 7.27/1.50  out_proof_time:                         0.014
% 7.27/1.50  total_time:                             0.879
% 7.27/1.50  num_of_symbols:                         48
% 7.27/1.50  num_of_terms:                           15820
% 7.27/1.50  
% 7.27/1.50  ------ Preprocessing
% 7.27/1.50  
% 7.27/1.50  num_of_splits:                          0
% 7.27/1.50  num_of_split_atoms:                     0
% 7.27/1.50  num_of_reused_defs:                     0
% 7.27/1.50  num_eq_ax_congr_red:                    18
% 7.27/1.50  num_of_sem_filtered_clauses:            1
% 7.27/1.50  num_of_subtypes:                        0
% 7.27/1.50  monotx_restored_types:                  0
% 7.27/1.50  sat_num_of_epr_types:                   0
% 7.27/1.50  sat_num_of_non_cyclic_types:            0
% 7.27/1.50  sat_guarded_non_collapsed_types:        0
% 7.27/1.50  num_pure_diseq_elim:                    0
% 7.27/1.50  simp_replaced_by:                       0
% 7.27/1.50  res_preprocessed:                       106
% 7.27/1.50  prep_upred:                             0
% 7.27/1.50  prep_unflattend:                        77
% 7.27/1.50  smt_new_axioms:                         0
% 7.27/1.50  pred_elim_cands:                        4
% 7.27/1.50  pred_elim:                              4
% 7.27/1.50  pred_elim_cl:                           5
% 7.27/1.50  pred_elim_cycles:                       8
% 7.27/1.50  merged_defs:                            8
% 7.27/1.50  merged_defs_ncl:                        0
% 7.27/1.50  bin_hyper_res:                          9
% 7.27/1.50  prep_cycles:                            4
% 7.27/1.50  pred_elim_time:                         0.021
% 7.27/1.50  splitting_time:                         0.
% 7.27/1.50  sem_filter_time:                        0.
% 7.27/1.50  monotx_time:                            0.
% 7.27/1.50  subtype_inf_time:                       0.
% 7.27/1.50  
% 7.27/1.50  ------ Problem properties
% 7.27/1.50  
% 7.27/1.50  clauses:                                19
% 7.27/1.50  conjectures:                            3
% 7.27/1.50  epr:                                    2
% 7.27/1.50  horn:                                   14
% 7.27/1.50  ground:                                 4
% 7.27/1.50  unary:                                  4
% 7.27/1.50  binary:                                 5
% 7.27/1.50  lits:                                   53
% 7.27/1.50  lits_eq:                                7
% 7.27/1.50  fd_pure:                                0
% 7.27/1.50  fd_pseudo:                              0
% 7.27/1.50  fd_cond:                                0
% 7.27/1.50  fd_pseudo_cond:                         1
% 7.27/1.50  ac_symbols:                             0
% 7.27/1.50  
% 7.27/1.50  ------ Propositional Solver
% 7.27/1.50  
% 7.27/1.50  prop_solver_calls:                      33
% 7.27/1.50  prop_fast_solver_calls:                 1696
% 7.27/1.50  smt_solver_calls:                       0
% 7.27/1.50  smt_fast_solver_calls:                  0
% 7.27/1.50  prop_num_of_clauses:                    8882
% 7.27/1.50  prop_preprocess_simplified:             19998
% 7.27/1.50  prop_fo_subsumed:                       59
% 7.27/1.50  prop_solver_time:                       0.
% 7.27/1.50  smt_solver_time:                        0.
% 7.27/1.50  smt_fast_solver_time:                   0.
% 7.27/1.50  prop_fast_solver_time:                  0.
% 7.27/1.50  prop_unsat_core_time:                   0.001
% 7.27/1.50  
% 7.27/1.50  ------ QBF
% 7.27/1.50  
% 7.27/1.50  qbf_q_res:                              0
% 7.27/1.50  qbf_num_tautologies:                    0
% 7.27/1.50  qbf_prep_cycles:                        0
% 7.27/1.50  
% 7.27/1.50  ------ BMC1
% 7.27/1.50  
% 7.27/1.50  bmc1_current_bound:                     -1
% 7.27/1.50  bmc1_last_solved_bound:                 -1
% 7.27/1.50  bmc1_unsat_core_size:                   -1
% 7.27/1.50  bmc1_unsat_core_parents_size:           -1
% 7.27/1.50  bmc1_merge_next_fun:                    0
% 7.27/1.50  bmc1_unsat_core_clauses_time:           0.
% 7.27/1.50  
% 7.27/1.50  ------ Instantiation
% 7.27/1.50  
% 7.27/1.50  inst_num_of_clauses:                    2986
% 7.27/1.50  inst_num_in_passive:                    1307
% 7.27/1.50  inst_num_in_active:                     1125
% 7.27/1.50  inst_num_in_unprocessed:                554
% 7.27/1.50  inst_num_of_loops:                      1410
% 7.27/1.50  inst_num_of_learning_restarts:          0
% 7.27/1.50  inst_num_moves_active_passive:          282
% 7.27/1.50  inst_lit_activity:                      0
% 7.27/1.50  inst_lit_activity_moves:                1
% 7.27/1.50  inst_num_tautologies:                   0
% 7.27/1.50  inst_num_prop_implied:                  0
% 7.27/1.50  inst_num_existing_simplified:           0
% 7.27/1.50  inst_num_eq_res_simplified:             0
% 7.27/1.50  inst_num_child_elim:                    0
% 7.27/1.50  inst_num_of_dismatching_blockings:      881
% 7.27/1.50  inst_num_of_non_proper_insts:           3176
% 7.27/1.50  inst_num_of_duplicates:                 0
% 7.27/1.50  inst_inst_num_from_inst_to_res:         0
% 7.27/1.50  inst_dismatching_checking_time:         0.
% 7.27/1.50  
% 7.27/1.50  ------ Resolution
% 7.27/1.50  
% 7.27/1.50  res_num_of_clauses:                     0
% 7.27/1.50  res_num_in_passive:                     0
% 7.27/1.50  res_num_in_active:                      0
% 7.27/1.50  res_num_of_loops:                       110
% 7.27/1.50  res_forward_subset_subsumed:            101
% 7.27/1.50  res_backward_subset_subsumed:           0
% 7.27/1.50  res_forward_subsumed:                   0
% 7.27/1.50  res_backward_subsumed:                  0
% 7.27/1.50  res_forward_subsumption_resolution:     0
% 7.27/1.50  res_backward_subsumption_resolution:    0
% 7.27/1.50  res_clause_to_clause_subsumption:       10279
% 7.27/1.50  res_orphan_elimination:                 0
% 7.27/1.50  res_tautology_del:                      221
% 7.27/1.50  res_num_eq_res_simplified:              0
% 7.27/1.50  res_num_sel_changes:                    0
% 7.27/1.50  res_moves_from_active_to_pass:          0
% 7.27/1.50  
% 7.27/1.50  ------ Superposition
% 7.27/1.50  
% 7.27/1.50  sup_time_total:                         0.
% 7.27/1.50  sup_time_generating:                    0.
% 7.27/1.50  sup_time_sim_full:                      0.
% 7.27/1.50  sup_time_sim_immed:                     0.
% 7.27/1.50  
% 7.27/1.50  sup_num_of_clauses:                     577
% 7.27/1.50  sup_num_in_active:                      281
% 7.27/1.50  sup_num_in_passive:                     296
% 7.27/1.50  sup_num_of_loops:                       280
% 7.27/1.50  sup_fw_superposition:                   898
% 7.27/1.50  sup_bw_superposition:                   75
% 7.27/1.50  sup_immediate_simplified:               161
% 7.27/1.50  sup_given_eliminated:                   0
% 7.27/1.50  comparisons_done:                       0
% 7.27/1.50  comparisons_avoided:                    0
% 7.27/1.50  
% 7.27/1.50  ------ Simplifications
% 7.27/1.50  
% 7.27/1.50  
% 7.27/1.50  sim_fw_subset_subsumed:                 61
% 7.27/1.50  sim_bw_subset_subsumed:                 14
% 7.27/1.50  sim_fw_subsumed:                        28
% 7.27/1.50  sim_bw_subsumed:                        0
% 7.27/1.50  sim_fw_subsumption_res:                 0
% 7.27/1.50  sim_bw_subsumption_res:                 0
% 7.27/1.50  sim_tautology_del:                      5
% 7.27/1.50  sim_eq_tautology_del:                   61
% 7.27/1.50  sim_eq_res_simp:                        0
% 7.27/1.50  sim_fw_demodulated:                     11
% 7.27/1.50  sim_bw_demodulated:                     0
% 7.27/1.50  sim_light_normalised:                   93
% 7.27/1.50  sim_joinable_taut:                      0
% 7.27/1.50  sim_joinable_simp:                      0
% 7.27/1.50  sim_ac_normalised:                      0
% 7.27/1.50  sim_smt_subsumption:                    0
% 7.27/1.50  
%------------------------------------------------------------------------------
