%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:27:09 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  161 (1672 expanded)
%              Number of clauses        :  107 ( 442 expanded)
%              Number of leaves         :   13 ( 413 expanded)
%              Depth                    :   22
%              Number of atoms          :  658 (10739 expanded)
%              Number of equality atoms :  226 ( 938 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v2_tex_2(X1,X0)
                & v1_tops_1(X1,X0) )
             => v3_tex_2(X1,X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tex_2(X1,X0)
          & v2_tex_2(X1,X0)
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f34,plain,(
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

fof(f33,plain,
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

fof(f35,plain,
    ( ~ v3_tex_2(sK3,sK2)
    & v2_tex_2(sK3,sK2)
    & v1_tops_1(sK3,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f34,f33])).

fof(f57,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

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
    inference(nnf_transformation,[],[f17])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f27,plain,(
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

fof(f28,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

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
    inference(ennf_transformation,[],[f8])).

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
    inference(flattening,[],[f18])).

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
    inference(nnf_transformation,[],[f19])).

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

fof(f50,plain,(
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

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(X2,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(X2,X0)
              | ~ r1_tarski(X1,X2)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(X2,X0)
      | ~ r1_tarski(X1,X2)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f58,plain,(
    v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | u1_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_0,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_190,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_191,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_190])).

cnf(c_232,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X2) = X2 ),
    inference(bin_hyper_res,[status(thm)],[c_1,c_191])).

cnf(c_889,plain,
    ( X0 != X1
    | k9_subset_1(X0,X2,X2) = X2
    | k3_xboole_0(X1,X3) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_232])).

cnf(c_890,plain,
    ( k9_subset_1(X0,X1,X1) = X1 ),
    inference(unflattening,[status(thm)],[c_889])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3460,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_22,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_477,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_22])).

cnf(c_478,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_3447,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_478])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3464,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4248,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3464])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_233,plain,
    ( ~ r1_tarski(X0,X1)
    | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
    inference(bin_hyper_res,[status(thm)],[c_2,c_191])).

cnf(c_3459,plain,
    ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
    | r1_tarski(X2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_233])).

cnf(c_4948,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,X1)) = k3_xboole_0(X0,sK0(sK2,X1))
    | v2_tex_2(X1,sK2) != iProver_top
    | v3_tex_2(X1,sK2) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4248,c_3459])).

cnf(c_10756,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3))
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_4948])).

cnf(c_19,negated_conjecture,
    ( v2_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_18,negated_conjecture,
    ( ~ v3_tex_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_677,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_478])).

cnf(c_678,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_677])).

cnf(c_3989,plain,
    ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_4841,plain,
    ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
    | k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_233])).

cnf(c_10822,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10756,c_21,c_19,c_678,c_3989,c_4841])).

cnf(c_10826,plain,
    ( k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3)) = sK0(sK2,sK3) ),
    inference(superposition,[status(thm)],[c_890,c_10822])).

cnf(c_3466,plain,
    ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3465,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_23,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_330,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_331,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK2)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_335,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X1,X0)
    | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_24,c_22])).

cnf(c_3453,plain,
    ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_4254,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3453])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_495,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_496,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_495])).

cnf(c_497,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_7425,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4254,c_497])).

cnf(c_7426,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7425])).

cnf(c_7438,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_7426])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_30,plain,
    ( v2_tex_2(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_666,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v2_tex_2(sK0(sK2,X0),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_496])).

cnf(c_667,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_668,plain,
    ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
    | v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_667])).

cnf(c_679,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_4005,plain,
    ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,sK0(sK2,sK3))
    | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
    inference(instantiation,[status(thm)],[c_335])).

cnf(c_4006,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4005])).

cnf(c_7518,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7438,c_28,c_30,c_668,c_679,c_4006])).

cnf(c_7527,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
    | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top
    | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3465,c_7518])).

cnf(c_7588,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,k3_xboole_0(sK0(sK2,sK3),X0))) = k3_xboole_0(sK0(sK2,sK3),X0)
    | r1_tarski(k3_xboole_0(sK0(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3466,c_7527])).

cnf(c_10848,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3)))) = k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3))
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_10826,c_7588])).

cnf(c_10864,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3)
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10848,c_10826])).

cnf(c_5,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_579,plain,
    ( ~ v1_tops_1(X0,X1)
    | v1_tops_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X0,X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_22])).

cnf(c_580,plain,
    ( ~ v1_tops_1(X0,sK2)
    | v1_tops_1(X1,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(X0,X1) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_3441,plain,
    ( v1_tops_1(X0,sK2) != iProver_top
    | v1_tops_1(X1,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_580])).

cnf(c_3684,plain,
    ( v1_tops_1(X0,sK2) = iProver_top
    | v1_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_3441])).

cnf(c_20,negated_conjecture,
    ( v1_tops_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,plain,
    ( v1_tops_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3760,plain,
    ( v1_tops_1(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3684,c_29])).

cnf(c_4255,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v1_tops_1(sK0(sK2,X0),sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3760])).

cnf(c_5184,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_4255])).

cnf(c_9,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_513,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_22])).

cnf(c_514,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0)) ),
    inference(unflattening,[status(thm)],[c_513])).

cnf(c_655,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,sK0(sK2,X0))
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_514])).

cnf(c_656,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK3,sK0(sK2,sK3)) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_657,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_3785,plain,
    ( v1_tops_1(X0,sK2)
    | ~ v1_tops_1(sK3,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_4240,plain,
    ( v1_tops_1(sK0(sK2,sK3),sK2)
    | ~ v1_tops_1(sK3,sK2)
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ r1_tarski(sK3,sK0(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_3785])).

cnf(c_4241,plain,
    ( v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top
    | v1_tops_1(sK3,sK2) != iProver_top
    | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4240])).

cnf(c_5256,plain,
    ( v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5184,c_28,c_29,c_30,c_657,c_679,c_4241])).

cnf(c_7,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_549,plain,
    ( ~ v1_tops_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | k2_pre_topc(X1,X0) = u1_struct_0(X1)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_22])).

cnf(c_550,plain,
    ( ~ v1_tops_1(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_3443,plain,
    ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
    | v1_tops_1(X0,sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_550])).

cnf(c_4257,plain,
    ( k2_pre_topc(sK2,sK0(sK2,X0)) = u1_struct_0(sK2)
    | v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | v1_tops_1(sK0(sK2,X0),sK2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_3443])).

cnf(c_5486,plain,
    ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2)
    | v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5256,c_4257])).

cnf(c_4634,plain,
    ( ~ v1_tops_1(sK0(sK2,sK3),sK2)
    | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_550])).

cnf(c_5489,plain,
    ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5486,c_21,c_20,c_19,c_656,c_678,c_4240,c_4634])).

cnf(c_3445,plain,
    ( v2_tex_2(X0,sK2) != iProver_top
    | v3_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(X0,sK0(sK2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_514])).

cnf(c_3915,plain,
    ( v2_tex_2(sK3,sK2) != iProver_top
    | v3_tex_2(sK3,sK2) = iProver_top
    | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_3445])).

cnf(c_4028,plain,
    ( r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3915,c_28,c_30,c_657])).

cnf(c_7591,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4028,c_7527])).

cnf(c_3669,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
    | v1_tops_1(sK3,sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_3443])).

cnf(c_3673,plain,
    ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3669,c_29])).

cnf(c_7594,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7591,c_3673])).

cnf(c_7528,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3460,c_7518])).

cnf(c_7551,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
    | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7528,c_3673])).

cnf(c_7668,plain,
    ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7594,c_28,c_30,c_657,c_7551])).

cnf(c_10867,plain,
    ( sK0(sK2,sK3) = sK3
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10864,c_5489,c_7668])).

cnf(c_3990,plain,
    ( m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3989])).

cnf(c_8,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_531,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | sK0(X1,X0) != X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_22])).

cnf(c_532,plain,
    ( ~ v2_tex_2(X0,sK2)
    | v3_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_647,plain,
    ( ~ v2_tex_2(X0,sK2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,X0) != X0
    | sK2 != sK2
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_532])).

cnf(c_648,plain,
    ( ~ v2_tex_2(sK3,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | sK0(sK2,sK3) != sK3 ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10867,c_3990,c_679,c_648,c_30,c_19,c_28,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 12:15:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.62/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.98  
% 3.62/0.98  ------  iProver source info
% 3.62/0.98  
% 3.62/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.98  git: non_committed_changes: false
% 3.62/0.98  git: last_make_outside_of_git: false
% 3.62/0.98  
% 3.62/0.98  ------ 
% 3.62/0.98  ------ Parsing...
% 3.62/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  ------ Proving...
% 3.62/0.98  ------ Problem Properties 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  clauses                                 22
% 3.62/0.98  conjectures                             4
% 3.62/0.98  EPR                                     3
% 3.62/0.98  Horn                                    17
% 3.62/0.98  unary                                   6
% 3.62/0.98  binary                                  3
% 3.62/0.98  lits                                    62
% 3.62/0.98  lits eq                                 8
% 3.62/0.98  fd_pure                                 0
% 3.62/0.98  fd_pseudo                               0
% 3.62/0.98  fd_cond                                 0
% 3.62/0.98  fd_pseudo_cond                          1
% 3.62/0.98  AC symbols                              0
% 3.62/0.98  
% 3.62/0.98  ------ Input Options Time Limit: Unbounded
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 10 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 3.62/0.98  Current options:
% 3.62/0.98  ------ 
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 14 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 16 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 3.62/0.98  
% 3.62/0.98  ------ Proving...
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS status Theorem for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  fof(f1,axiom,(
% 3.62/0.98    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f36,plain,(
% 3.62/0.98    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f1])).
% 3.62/0.98  
% 3.62/0.98  fof(f2,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f11,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f2])).
% 3.62/0.98  
% 3.62/0.98  fof(f37,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f11])).
% 3.62/0.98  
% 3.62/0.98  fof(f4,axiom,(
% 3.62/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f22,plain,(
% 3.62/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.62/0.98    inference(nnf_transformation,[],[f4])).
% 3.62/0.98  
% 3.62/0.98  fof(f40,plain,(
% 3.62/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f22])).
% 3.62/0.98  
% 3.62/0.98  fof(f9,conjecture,(
% 3.62/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f10,negated_conjecture,(
% 3.62/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 3.62/0.98    inference(negated_conjecture,[],[f9])).
% 3.62/0.98  
% 3.62/0.98  fof(f20,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : ((~v3_tex_2(X1,X0) & (v2_tex_2(X1,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f10])).
% 3.62/0.98  
% 3.62/0.98  fof(f21,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/0.98    inference(flattening,[],[f20])).
% 3.62/0.98  
% 3.62/0.98  fof(f34,plain,(
% 3.62/0.98    ( ! [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (~v3_tex_2(sK3,X0) & v2_tex_2(sK3,X0) & v1_tops_1(sK3,X0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f33,plain,(
% 3.62/0.98    ? [X0] : (? [X1] : (~v3_tex_2(X1,X0) & v2_tex_2(X1,X0) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v3_tex_2(X1,sK2) & v2_tex_2(X1,sK2) & v1_tops_1(X1,sK2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f35,plain,(
% 3.62/0.98    (~v3_tex_2(sK3,sK2) & v2_tex_2(sK3,sK2) & v1_tops_1(sK3,sK2) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f21,f34,f33])).
% 3.62/0.98  
% 3.62/0.98  fof(f57,plain,(
% 3.62/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f7,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f16,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f7])).
% 3.62/0.98  
% 3.62/0.98  fof(f17,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f16])).
% 3.62/0.98  
% 3.62/0.98  fof(f24,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(nnf_transformation,[],[f17])).
% 3.62/0.98  
% 3.62/0.98  fof(f25,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f24])).
% 3.62/0.98  
% 3.62/0.98  fof(f26,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(rectify,[],[f25])).
% 3.62/0.98  
% 3.62/0.98  fof(f27,plain,(
% 3.62/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f28,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f26,f27])).
% 3.62/0.98  
% 3.62/0.98  fof(f46,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  fof(f56,plain,(
% 3.62/0.98    l1_pre_topc(sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f39,plain,(
% 3.62/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f22])).
% 3.62/0.98  
% 3.62/0.98  fof(f3,axiom,(
% 3.62/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f12,plain,(
% 3.62/0.98    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f3])).
% 3.62/0.98  
% 3.62/0.98  fof(f38,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.62/0.98    inference(cnf_transformation,[],[f12])).
% 3.62/0.98  
% 3.62/0.98  fof(f59,plain,(
% 3.62/0.98    v2_tex_2(sK3,sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f60,plain,(
% 3.62/0.98    ~v3_tex_2(sK3,sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f8,axiom,(
% 3.62/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f18,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.98    inference(ennf_transformation,[],[f8])).
% 3.62/0.98  
% 3.62/0.98  fof(f19,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.98    inference(flattening,[],[f18])).
% 3.62/0.98  
% 3.62/0.98  fof(f29,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.98    inference(nnf_transformation,[],[f19])).
% 3.62/0.98  
% 3.62/0.98  fof(f30,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.98    inference(rectify,[],[f29])).
% 3.62/0.98  
% 3.62/0.98  fof(f31,plain,(
% 3.62/0.98    ! [X1,X0] : (? [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) != X2 & r1_tarski(X2,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.62/0.98    introduced(choice_axiom,[])).
% 3.62/0.98  
% 3.62/0.98  fof(f32,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,sK1(X0,X1))) != sK1(X0,X1) & r1_tarski(sK1(X0,X1),X1) & m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f31])).
% 3.62/0.98  
% 3.62/0.98  fof(f50,plain,(
% 3.62/0.98    ( ! [X0,X3,X1] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X3)) = X3 | ~r1_tarski(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f32])).
% 3.62/0.98  
% 3.62/0.98  fof(f55,plain,(
% 3.62/0.98    v2_pre_topc(sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f54,plain,(
% 3.62/0.98    ~v2_struct_0(sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f47,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  fof(f5,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v1_tops_1(X1,X0)) => v1_tops_1(X2,X0)))))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f13,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (! [X2] : ((v1_tops_1(X2,X0) | (~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f5])).
% 3.62/0.98  
% 3.62/0.98  fof(f14,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (! [X2] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(flattening,[],[f13])).
% 3.62/0.98  
% 3.62/0.98  fof(f41,plain,(
% 3.62/0.98    ( ! [X2,X0,X1] : (v1_tops_1(X2,X0) | ~r1_tarski(X1,X2) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f14])).
% 3.62/0.98  
% 3.62/0.98  fof(f58,plain,(
% 3.62/0.98    v1_tops_1(sK3,sK2)),
% 3.62/0.98    inference(cnf_transformation,[],[f35])).
% 3.62/0.98  
% 3.62/0.98  fof(f48,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  fof(f6,axiom,(
% 3.62/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 3.62/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.62/0.98  
% 3.62/0.98  fof(f15,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(ennf_transformation,[],[f6])).
% 3.62/0.98  
% 3.62/0.98  fof(f23,plain,(
% 3.62/0.98    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1)) & (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.62/0.98    inference(nnf_transformation,[],[f15])).
% 3.62/0.98  
% 3.62/0.98  fof(f42,plain,(
% 3.62/0.98    ( ! [X0,X1] : (u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f23])).
% 3.62/0.98  
% 3.62/0.98  fof(f49,plain,(
% 3.62/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.62/0.98    inference(cnf_transformation,[],[f28])).
% 3.62/0.98  
% 3.62/0.98  cnf(c_0,plain,
% 3.62/0.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f36]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_1,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.62/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_190,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.62/0.98      inference(prop_impl,[status(thm)],[c_3]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_191,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_190]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_232,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X2) = X2 ),
% 3.62/0.98      inference(bin_hyper_res,[status(thm)],[c_1,c_191]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_889,plain,
% 3.62/0.98      ( X0 != X1
% 3.62/0.98      | k9_subset_1(X0,X2,X2) = X2
% 3.62/0.98      | k3_xboole_0(X1,X3) != X4 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_232]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_890,plain,
% 3.62/0.98      ( k9_subset_1(X0,X1,X1) = X1 ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_889]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_21,negated_conjecture,
% 3.62/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/0.98      inference(cnf_transformation,[],[f57]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3460,plain,
% 3.62/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_11,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f46]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_22,negated_conjecture,
% 3.62/0.98      ( l1_pre_topc(sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_477,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_478,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | v3_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_477]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3447,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_478]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3464,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.62/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4248,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK0(sK2,X0),u1_struct_0(sK2)) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3447,c_3464]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_2,plain,
% 3.62/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.62/0.98      | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.62/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_233,plain,
% 3.62/0.98      ( ~ r1_tarski(X0,X1) | k9_subset_1(X1,X2,X0) = k3_xboole_0(X2,X0) ),
% 3.62/0.98      inference(bin_hyper_res,[status(thm)],[c_2,c_191]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3459,plain,
% 3.62/0.98      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
% 3.62/0.98      | r1_tarski(X2,X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_233]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4948,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,X1)) = k3_xboole_0(X0,sK0(sK2,X1))
% 3.62/0.98      | v2_tex_2(X1,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X1,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_4248,c_3459]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10756,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3))
% 3.62/0.98      | v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(sK3,sK2) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_4948]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_19,negated_conjecture,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_18,negated_conjecture,
% 3.62/0.98      ( ~ v3_tex_2(sK3,sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_677,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | m1_subset_1(sK0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | sK2 != sK2
% 3.62/0.98      | sK3 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_478]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_678,plain,
% 3.62/0.98      ( ~ v2_tex_2(sK3,sK2)
% 3.62/0.98      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_677]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3989,plain,
% 3.62/0.98      ( ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4841,plain,
% 3.62/0.98      ( ~ r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2))
% 3.62/0.98      | k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3)) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_233]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10822,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,sK0(sK2,sK3)) = k3_xboole_0(X0,sK0(sK2,sK3)) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_10756,c_21,c_19,c_678,c_3989,c_4841]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10826,plain,
% 3.62/0.98      ( k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3)) = sK0(sK2,sK3) ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_890,c_10822]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3466,plain,
% 3.62/0.98      ( r1_tarski(k3_xboole_0(X0,X1),X0) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3465,plain,
% 3.62/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_17,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ r1_tarski(X2,X0)
% 3.62/0.98      | v2_struct_0(X1)
% 3.62/0.98      | ~ v2_pre_topc(X1)
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2 ),
% 3.62/0.98      inference(cnf_transformation,[],[f50]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_23,negated_conjecture,
% 3.62/0.98      ( v2_pre_topc(sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_330,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ r1_tarski(X2,X0)
% 3.62/0.98      | v2_struct_0(X1)
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k9_subset_1(u1_struct_0(X1),X0,k2_pre_topc(X1,X2)) = X2
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_331,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(X1,X0)
% 3.62/0.98      | v2_struct_0(sK2)
% 3.62/0.98      | ~ l1_pre_topc(sK2)
% 3.62/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_330]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_24,negated_conjecture,
% 3.62/0.98      ( ~ v2_struct_0(sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_335,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(X1,X0)
% 3.62/0.98      | k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1 ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_331,c_24,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3453,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),X0,k2_pre_topc(sK2,X1)) = X1
% 3.62/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4254,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 3.62/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v2_tex_2(sK0(sK2,X0),sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3447,c_3453]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v2_tex_2(sK0(X1,X0),X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f47]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_495,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v2_tex_2(sK0(X1,X0),X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_496,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | v2_tex_2(sK0(sK2,X0),sK2)
% 3.62/0.98      | v3_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_495]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_497,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v2_tex_2(sK0(sK2,X0),sK2) = iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7425,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_4254,c_497]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7426,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,X0),k2_pre_topc(sK2,X1)) = X1
% 3.62/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X1,sK0(sK2,X0)) != iProver_top ),
% 3.62/0.98      inference(renaming,[status(thm)],[c_7425]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7438,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 3.62/0.98      | v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(sK3,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_7426]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_28,plain,
% 3.62/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_30,plain,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_666,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | v2_tex_2(sK0(sK2,X0),sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | sK2 != sK2
% 3.62/0.98      | sK3 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_496]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_667,plain,
% 3.62/0.98      ( v2_tex_2(sK0(sK2,sK3),sK2)
% 3.62/0.98      | ~ v2_tex_2(sK3,sK2)
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_666]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_668,plain,
% 3.62/0.98      ( v2_tex_2(sK0(sK2,sK3),sK2) = iProver_top
% 3.62/0.98      | v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_667]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_679,plain,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top
% 3.62/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4005,plain,
% 3.62/0.98      ( ~ v2_tex_2(sK0(sK2,sK3),sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(X0,sK0(sK2,sK3))
% 3.62/0.98      | k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0 ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_335]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4006,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 3.62/0.98      | v2_tex_2(sK0(sK2,sK3),sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4005]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7518,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_7438,c_28,c_30,c_668,c_679,c_4006]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7527,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,X0)) = X0
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,sK3)) != iProver_top
% 3.62/0.98      | r1_tarski(X0,u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3465,c_7518]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7588,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,k3_xboole_0(sK0(sK2,sK3),X0))) = k3_xboole_0(sK0(sK2,sK3),X0)
% 3.62/0.98      | r1_tarski(k3_xboole_0(sK0(sK2,sK3),X0),u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3466,c_7527]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10848,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3)))) = k3_xboole_0(sK0(sK2,sK3),sK0(sK2,sK3))
% 3.62/0.98      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_10826,c_7588]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10864,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK0(sK2,sK3))) = sK0(sK2,sK3)
% 3.62/0.98      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_10848,c_10826]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,X1)
% 3.62/0.98      | v1_tops_1(X2,X1)
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ r1_tarski(X0,X2)
% 3.62/0.98      | ~ l1_pre_topc(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_579,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,X1)
% 3.62/0.98      | v1_tops_1(X2,X1)
% 3.62/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ r1_tarski(X0,X2)
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_5,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_580,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,sK2)
% 3.62/0.98      | v1_tops_1(X1,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(X0,X1) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_579]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3441,plain,
% 3.62/0.98      ( v1_tops_1(X0,sK2) != iProver_top
% 3.62/0.98      | v1_tops_1(X1,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_580]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3684,plain,
% 3.62/0.98      ( v1_tops_1(X0,sK2) = iProver_top
% 3.62/0.98      | v1_tops_1(sK3,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_3441]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_20,negated_conjecture,
% 3.62/0.98      ( v1_tops_1(sK3,sK2) ),
% 3.62/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_29,plain,
% 3.62/0.98      ( v1_tops_1(sK3,sK2) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3760,plain,
% 3.62/0.98      ( v1_tops_1(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,X0) != iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_3684,c_29]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4255,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | v1_tops_1(sK0(sK2,X0),sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,X0)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3447,c_3760]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5184,plain,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(sK3,sK2) = iProver_top
% 3.62/0.98      | v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_4255]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_9,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | r1_tarski(X0,sK0(X1,X0))
% 3.62/0.98      | ~ l1_pre_topc(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f48]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_513,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | r1_tarski(X0,sK0(X1,X0))
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_9,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_514,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | v3_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,X0)) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_513]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_655,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,X0))
% 3.62/0.98      | sK2 != sK2
% 3.62/0.98      | sK3 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_514]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_656,plain,
% 3.62/0.98      ( ~ v2_tex_2(sK3,sK2)
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_655]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_657,plain,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3785,plain,
% 3.62/0.98      ( v1_tops_1(X0,sK2)
% 3.62/0.98      | ~ v1_tops_1(sK3,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(sK3,X0) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_580]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4240,plain,
% 3.62/0.98      ( v1_tops_1(sK0(sK2,sK3),sK2)
% 3.62/0.98      | ~ v1_tops_1(sK3,sK2)
% 3.62/0.98      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | ~ r1_tarski(sK3,sK0(sK2,sK3)) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_3785]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4241,plain,
% 3.62/0.98      ( v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top
% 3.62/0.98      | v1_tops_1(sK3,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_4240]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5256,plain,
% 3.62/0.98      ( v1_tops_1(sK0(sK2,sK3),sK2) = iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_5184,c_28,c_29,c_30,c_657,c_679,c_4241]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1) ),
% 3.62/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_549,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | k2_pre_topc(X1,X0) = u1_struct_0(X1)
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_7,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_550,plain,
% 3.62/0.98      ( ~ v1_tops_1(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | k2_pre_topc(sK2,X0) = u1_struct_0(sK2) ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_549]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3443,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,X0) = u1_struct_0(sK2)
% 3.62/0.98      | v1_tops_1(X0,sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_550]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4257,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,sK0(sK2,X0)) = u1_struct_0(sK2)
% 3.62/0.98      | v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | v1_tops_1(sK0(sK2,X0),sK2) != iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3447,c_3443]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5486,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2)
% 3.62/0.98      | v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(sK3,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_5256,c_4257]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4634,plain,
% 3.62/0.98      ( ~ v1_tops_1(sK0(sK2,sK3),sK2)
% 3.62/0.98      | ~ m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.62/0.98      inference(instantiation,[status(thm)],[c_550]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_5489,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,sK0(sK2,sK3)) = u1_struct_0(sK2) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_5486,c_21,c_20,c_19,c_656,c_678,c_4240,c_4634]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3445,plain,
% 3.62/0.98      ( v2_tex_2(X0,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(X0,sK2) = iProver_top
% 3.62/0.98      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(X0,sK0(sK2,X0)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_514]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3915,plain,
% 3.62/0.98      ( v2_tex_2(sK3,sK2) != iProver_top
% 3.62/0.98      | v3_tex_2(sK3,sK2) = iProver_top
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_3445]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_4028,plain,
% 3.62/0.98      ( r1_tarski(sK3,sK0(sK2,sK3)) = iProver_top ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_3915,c_28,c_30,c_657]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7591,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
% 3.62/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_4028,c_7527]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3669,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2)
% 3.62/0.98      | v1_tops_1(sK3,sK2) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_3443]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3673,plain,
% 3.62/0.98      ( k2_pre_topc(sK2,sK3) = u1_struct_0(sK2) ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_3669,c_29]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7594,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 3.62/0.98      | r1_tarski(sK3,u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_7591,c_3673]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7528,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),k2_pre_topc(sK2,sK3)) = sK3
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(superposition,[status(thm)],[c_3460,c_7518]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7551,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3
% 3.62/0.98      | r1_tarski(sK3,sK0(sK2,sK3)) != iProver_top ),
% 3.62/0.98      inference(light_normalisation,[status(thm)],[c_7528,c_3673]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_7668,plain,
% 3.62/0.98      ( k9_subset_1(u1_struct_0(sK2),sK0(sK2,sK3),u1_struct_0(sK2)) = sK3 ),
% 3.62/0.98      inference(global_propositional_subsumption,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_7594,c_28,c_30,c_657,c_7551]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_10867,plain,
% 3.62/0.98      ( sK0(sK2,sK3) = sK3
% 3.62/0.98      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) != iProver_top ),
% 3.62/0.98      inference(light_normalisation,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_10864,c_5489,c_7668]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_3990,plain,
% 3.62/0.98      ( m1_subset_1(sK0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.62/0.98      | r1_tarski(sK0(sK2,sK3),u1_struct_0(sK2)) = iProver_top ),
% 3.62/0.98      inference(predicate_to_equality,[status(thm)],[c_3989]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_8,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | ~ l1_pre_topc(X1)
% 3.62/0.98      | sK0(X1,X0) != X0 ),
% 3.62/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_531,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,X1)
% 3.62/0.98      | v3_tex_2(X0,X1)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.62/0.98      | sK0(X1,X0) != X0
% 3.62/0.98      | sK2 != X1 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_8,c_22]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_532,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | v3_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | sK0(sK2,X0) != X0 ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_531]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_647,plain,
% 3.62/0.98      ( ~ v2_tex_2(X0,sK2)
% 3.62/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | sK0(sK2,X0) != X0
% 3.62/0.98      | sK2 != sK2
% 3.62/0.98      | sK3 != X0 ),
% 3.62/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_532]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(c_648,plain,
% 3.62/0.98      ( ~ v2_tex_2(sK3,sK2)
% 3.62/0.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.62/0.98      | sK0(sK2,sK3) != sK3 ),
% 3.62/0.98      inference(unflattening,[status(thm)],[c_647]) ).
% 3.62/0.98  
% 3.62/0.98  cnf(contradiction,plain,
% 3.62/0.98      ( $false ),
% 3.62/0.98      inference(minisat,
% 3.62/0.98                [status(thm)],
% 3.62/0.98                [c_10867,c_3990,c_679,c_648,c_30,c_19,c_28,c_21]) ).
% 3.62/0.98  
% 3.62/0.98  
% 3.62/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.98  
% 3.62/0.98  ------                               Statistics
% 3.62/0.98  
% 3.62/0.98  ------ Selected
% 3.62/0.98  
% 3.62/0.98  total_time:                             0.366
% 3.62/0.98  
%------------------------------------------------------------------------------
