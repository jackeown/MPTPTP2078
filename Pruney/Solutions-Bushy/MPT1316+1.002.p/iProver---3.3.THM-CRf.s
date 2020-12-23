%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1316+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:45:27 EST 2020

% Result     : Theorem 0.65s
% Output     : CNFRefutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 297 expanded)
%              Number of clauses        :   53 (  73 expanded)
%              Number of leaves         :   10 (  99 expanded)
%              Depth                    :   14
%              Number of atoms          :  364 (1832 expanded)
%              Number of equality atoms :   38 ( 253 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( v3_pre_topc(X3,X2)
      | X1 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( v3_pre_topc(X3,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f23,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v1_tops_2(X3,X2)
          & X1 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
     => ( ~ v1_tops_2(sK4,X2)
        & sK4 = X1
        & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v1_tops_2(X3,X2)
              & X1 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
          & v1_tops_2(X1,X0)
          & m1_pre_topc(X2,X0) )
     => ( ? [X3] :
            ( ~ v1_tops_2(X3,sK3)
            & X1 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) )
        & v1_tops_2(X1,X0)
        & m1_pre_topc(sK3,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v1_tops_2(X3,X2)
                & sK2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
            & v1_tops_2(sK2,X0)
            & m1_pre_topc(X2,X0) )
        & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v1_tops_2(X3,X2)
                    & X1 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
                & v1_tops_2(X1,X0)
                & m1_pre_topc(X2,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,sK1)
              & m1_pre_topc(X2,sK1) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ~ v1_tops_2(sK4,sK3)
    & sK2 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    & v1_tops_2(sK2,sK1)
    & m1_pre_topc(sK3,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f15,f23,f22,f21,f20])).

fof(f34,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( v3_pre_topc(X2,X0)
                  | ~ r2_hidden(X2,X1)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ? [X2] :
                  ( ~ v3_pre_topc(X2,X0)
                  & r2_hidden(X2,X1)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f16])).

fof(f18,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ v3_pre_topc(X2,X0)
          & r2_hidden(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ v3_pre_topc(sK0(X0,X1),X0)
        & r2_hidden(sK0(X0,X1),X1)
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ( ~ v3_pre_topc(sK0(X0,X1),X0)
                & r2_hidden(sK0(X0,X1),X1)
                & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( v3_pre_topc(X3,X0)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f18])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( v3_pre_topc(X3,X0)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f24])).

fof(f37,plain,(
    sK2 = sK4 ),
    inference(cnf_transformation,[],[f24])).

fof(f35,plain,(
    v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f38,plain,(
    ~ v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | ~ v3_pre_topc(sK0(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_tops_2(X1,X0)
      | r2_hidden(sK0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f36,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_740,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | m1_subset_1(X0_41,X0_42)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(X0_42)) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1175,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),sK4)
    | m1_subset_1(sK0(sK3,sK4),X0_42)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(X0_42)) ),
    inference(instantiation,[status(thm)],[c_740])).

cnf(c_1224,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),sK4)
    | m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ v3_pre_topc(X2,X1)
    | v3_pre_topc(X2,X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_11,negated_conjecture,
    ( m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_139,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X0,X1)
    | v3_pre_topc(X0,X2)
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_11])).

cnf(c_140,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0,sK1)
    | v3_pre_topc(X0,sK3)
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_139])).

cnf(c_13,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_144,plain,
    ( v3_pre_topc(X0,sK3)
    | ~ v3_pre_topc(X0,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_140,c_13])).

cnf(c_145,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0,sK1)
    | v3_pre_topc(X0,sK3) ),
    inference(renaming,[status(thm)],[c_144])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(X0_41,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(X0_41,sK1)
    | v3_pre_topc(X0_41,sK3) ),
    inference(subtyping,[status(esa)],[c_145])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_pre_topc(sK0(sK3,sK4),sK1)
    | v3_pre_topc(sK0(sK3,sK4),sK3) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | v3_pre_topc(X0,X2)
    | ~ v1_tops_2(X1,X2)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_332,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_pre_topc(X0,sK1)
    | ~ v1_tops_2(X1,sK1) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_346,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v3_pre_topc(X0,sK1)
    | ~ v1_tops_2(X1,sK1) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_332,c_6])).

cnf(c_727,plain,
    ( ~ r2_hidden(X0_41,X1_41)
    | ~ m1_subset_1(X1_41,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v3_pre_topc(X0_41,sK1)
    | ~ v1_tops_2(X1_41,sK1) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1176,plain,
    ( ~ r2_hidden(sK0(sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | v3_pre_topc(sK0(sK3,sK4),sK1)
    | ~ v1_tops_2(sK4,sK1) ),
    inference(instantiation,[status(thm)],[c_727])).

cnf(c_12,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_735,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1020,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_8,negated_conjecture,
    ( sK2 = sK4 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_738,negated_conjecture,
    ( sK2 = sK4 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1039,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1020,c_738])).

cnf(c_1116,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1039])).

cnf(c_10,negated_conjecture,
    ( v1_tops_2(sK2,sK1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_736,negated_conjecture,
    ( v1_tops_2(sK2,sK1) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1019,plain,
    ( v1_tops_2(sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1032,plain,
    ( v1_tops_2(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1019,c_738])).

cnf(c_1109,plain,
    ( v1_tops_2(sK4,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1032])).

cnf(c_7,negated_conjecture,
    ( ~ v1_tops_2(sK4,sK3) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_163,plain,
    ( ~ l1_pre_topc(X0)
    | l1_pre_topc(X1)
    | sK1 != X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_11])).

cnf(c_164,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_pre_topc(sK3) ),
    inference(unflattening,[status(thm)],[c_163])).

cnf(c_166,plain,
    ( l1_pre_topc(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_164,c_13])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_166])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_545,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | m1_subset_1(sK0(sK3,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_272])).

cnf(c_546,plain,
    ( m1_subset_1(sK0(sK3,sK4),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_545])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_286,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ v3_pre_topc(sK0(X1,X0),X1)
    | v1_tops_2(X0,X1)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_166])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0),sK3)
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,X0),sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_287])).

cnf(c_535,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ v3_pre_topc(sK0(sK3,sK4),sK3) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_316,plain,
    ( r2_hidden(sK0(X0,X1),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
    | v1_tops_2(X1,X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_166])).

cnf(c_317,plain,
    ( r2_hidden(sK0(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | v1_tops_2(X0,sK3) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_523,plain,
    ( r2_hidden(sK0(sK3,X0),X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | sK3 != sK3
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_317])).

cnf(c_524,plain,
    ( r2_hidden(sK0(sK3,sK4),sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_9,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1224,c_1207,c_1176,c_1116,c_1109,c_546,c_535,c_524,c_9])).


%------------------------------------------------------------------------------
