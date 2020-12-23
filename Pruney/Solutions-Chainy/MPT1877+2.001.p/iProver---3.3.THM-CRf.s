%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:26:56 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 832 expanded)
%              Number of clauses        :  119 ( 213 expanded)
%              Number of leaves         :   19 ( 282 expanded)
%              Depth                    :   16
%              Number of atoms          :  699 (6004 expanded)
%              Number of equality atoms :  262 (1715 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f44,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v3_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v3_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_tex_2(X2,X0)
                        & X2 = X3
                        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                     => v3_tex_2(X3,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v3_tex_2(X3,X1)
          & v3_tex_2(X2,X0)
          & X2 = X3
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_tex_2(sK4,X1)
        & v3_tex_2(X2,X0)
        & sK4 = X2
        & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ v3_tex_2(X3,X1)
              & v3_tex_2(X2,X0)
              & X2 = X3
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X3] :
            ( ~ v3_tex_2(X3,X1)
            & v3_tex_2(sK3,X0)
            & sK3 = X3
            & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,X0)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ v3_tex_2(X3,sK2)
                & v3_tex_2(X2,X0)
                & X2 = X3
                & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ v3_tex_2(X3,X1)
                    & v3_tex_2(X2,X0)
                    & X2 = X3
                    & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_tex_2(X3,X1)
                  & v3_tex_2(X2,sK1)
                  & X2 = X3
                  & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1))) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ~ v3_tex_2(sK4,sK2)
    & v3_tex_2(sK3,sK1)
    & sK3 = sK4
    & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_pre_topc(sK2)
    & l1_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f20,f33,f32,f31,f30])).

fof(f56,plain,(
    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f53,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_tex_2(X2,X0)
                      & X2 = X3
                      & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                   => v2_tex_2(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v2_tex_2(X3,X1)
                  | ~ v2_tex_2(X2,X0)
                  | X2 != X3
                  | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X2,X0)
      | X2 != X3
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( v2_tex_2(X3,X1)
      | ~ v2_tex_2(X3,X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f51])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

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
    inference(nnf_transformation,[],[f16])).

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
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f27,plain,(
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
    inference(rectify,[],[f26])).

fof(f28,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( X1 = X3
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f34])).

fof(f57,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f34])).

fof(f58,plain,(
    v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | sK0(X0,X1) != X1
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f59,plain,(
    ~ v3_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f55,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | r1_tarski(X1,sK0(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | v2_tex_2(sK0(X0,X1),X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_tex_2(X1,X0)
      | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f35])).

cnf(c_9,plain,
    ( m1_pre_topc(X0,X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1542,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1544,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3492,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1544])).

cnf(c_24,negated_conjecture,
    ( l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,plain,
    ( l1_pre_topc(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3607,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3492,c_25])).

cnf(c_3608,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3607])).

cnf(c_5,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1545,plain,
    ( m1_pre_topc(X0,X1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3614,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3608,c_1545])).

cnf(c_23,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_26,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3838,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | m1_pre_topc(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3614,c_26])).

cnf(c_3839,plain,
    ( m1_pre_topc(X0,sK1) != iProver_top
    | m1_pre_topc(X0,sK2) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3838])).

cnf(c_3847,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_3839])).

cnf(c_50,plain,
    ( m1_pre_topc(X0,X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_52,plain,
    ( m1_pre_topc(sK1,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_3625,plain,
    ( m1_pre_topc(sK1,sK1) != iProver_top
    | m1_pre_topc(sK1,sK2) = iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3614])).

cnf(c_4158,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3847,c_25,c_26,c_52,c_3625])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1543,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1546,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2665,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1546])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_1549,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4581,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_1549])).

cnf(c_5596,plain,
    ( u1_struct_0(X0) = u1_struct_0(X1)
    | m1_pre_topc(X1,X0) != iProver_top
    | m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2665,c_4581])).

cnf(c_8462,plain,
    ( u1_struct_0(sK2) = u1_struct_0(sK1)
    | m1_pre_topc(sK2,sK1) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_5596])).

cnf(c_998,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,X2)
    | X2 != X1 ),
    theory(equality)).

cnf(c_2903,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X0,u1_struct_0(sK1))
    | u1_struct_0(sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_3834,plain,
    ( ~ r1_tarski(X0,u1_struct_0(X1))
    | r1_tarski(X0,u1_struct_0(sK1))
    | u1_struct_0(sK1) != u1_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_2903])).

cnf(c_6889,plain,
    ( r1_tarski(sK0(sK2,sK4),u1_struct_0(sK1))
    | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(sK2))
    | u1_struct_0(sK1) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3834])).

cnf(c_997,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2986,plain,
    ( X0 != X1
    | u1_struct_0(sK1) != X1
    | u1_struct_0(sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_3897,plain,
    ( X0 != u1_struct_0(sK1)
    | u1_struct_0(sK1) = X0
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2986])).

cnf(c_4974,plain,
    ( u1_struct_0(X0) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(X0)
    | u1_struct_0(sK1) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_3897])).

cnf(c_6313,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4974])).

cnf(c_4684,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(X0,u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_6216,plain,
    ( ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK0(sK2,sK4),u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_4684])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_5763,plain,
    ( m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5765,plain,
    ( m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_5763])).

cnf(c_16,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X0,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2)
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4166,plain,
    ( v2_tex_2(sK0(sK2,sK4),X0)
    | ~ v2_tex_2(sK0(sK2,sK4),sK2)
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4185,plain,
    ( v2_tex_2(sK0(sK2,sK4),sK1)
    | ~ v2_tex_2(sK0(sK2,sK4),sK2)
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(instantiation,[status(thm)],[c_4166])).

cnf(c_14,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X2,X0)
    | ~ l1_pre_topc(X1)
    | X0 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1969,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ v3_tex_2(sK4,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(sK4,X0)
    | ~ l1_pre_topc(X1)
    | X0 = sK4 ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4136,plain,
    ( ~ v2_tex_2(sK0(sK2,sK4),X0)
    | ~ v3_tex_2(sK4,X0)
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
    | ~ r1_tarski(sK4,sK0(sK2,sK4))
    | ~ l1_pre_topc(X0)
    | sK0(sK2,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_1969])).

cnf(c_4138,plain,
    ( ~ v2_tex_2(sK0(sK2,sK4),sK1)
    | ~ v3_tex_2(sK4,sK1)
    | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ r1_tarski(sK4,sK0(sK2,sK4))
    | ~ l1_pre_topc(sK1)
    | sK0(sK2,sK4) = sK4 ),
    inference(instantiation,[status(thm)],[c_4136])).

cnf(c_2837,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1545])).

cnf(c_2855,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2837,c_25])).

cnf(c_2856,plain,
    ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(renaming,[status(thm)],[c_2855])).

cnf(c_3494,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1544,c_2856])).

cnf(c_3731,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3494,c_26])).

cnf(c_3732,plain,
    ( m1_pre_topc(X0,sK1) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3731])).

cnf(c_3738,plain,
    ( m1_pre_topc(sK2,sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1542,c_3732])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1531,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( sK3 = sK4 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1563,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1531,c_19])).

cnf(c_1535,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | v2_tex_2(X2,X1) != iProver_top
    | v2_tex_2(X2,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1902,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_tex_2(X1,X0) = iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_1535])).

cnf(c_2213,plain,
    ( l1_pre_topc(X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | v2_tex_2(X1,X0) = iProver_top
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1902,c_25])).

cnf(c_2214,plain,
    ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_tex_2(X1,X0) = iProver_top
    | v2_tex_2(X1,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2213])).

cnf(c_2224,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2214])).

cnf(c_2429,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top
    | v2_tex_2(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2224,c_26])).

cnf(c_2430,plain,
    ( v2_tex_2(X0,sK1) != iProver_top
    | v2_tex_2(X0,sK2) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2429])).

cnf(c_2440,plain,
    ( v2_tex_2(sK4,sK1) != iProver_top
    | v2_tex_2(sK4,sK2) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_2430])).

cnf(c_2458,plain,
    ( ~ v2_tex_2(sK4,sK1)
    | v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2440])).

cnf(c_1007,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1763,plain,
    ( v2_tex_2(X0,sK1)
    | ~ v2_tex_2(sK3,sK1)
    | X0 != sK3 ),
    inference(instantiation,[status(thm)],[c_1007])).

cnf(c_2202,plain,
    ( ~ v2_tex_2(sK3,sK1)
    | v2_tex_2(sK4,sK1)
    | sK4 != sK3 ),
    inference(instantiation,[status(thm)],[c_1763])).

cnf(c_2206,plain,
    ( sK4 != sK3
    | v2_tex_2(sK3,sK1) != iProver_top
    | v2_tex_2(sK4,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2202])).

cnf(c_996,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1976,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_996])).

cnf(c_1784,plain,
    ( X0 != X1
    | X0 = sK3
    | sK3 != X1 ),
    inference(instantiation,[status(thm)],[c_997])).

cnf(c_1841,plain,
    ( X0 = sK3
    | X0 != sK4
    | sK3 != sK4 ),
    inference(instantiation,[status(thm)],[c_1784])).

cnf(c_1975,plain,
    ( sK3 != sK4
    | sK4 = sK3
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1841])).

cnf(c_1696,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1563])).

cnf(c_18,negated_conjecture,
    ( v3_tex_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1533,plain,
    ( v3_tex_2(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1556,plain,
    ( v3_tex_2(sK4,sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1533,c_19])).

cnf(c_1687,plain,
    ( v3_tex_2(sK4,sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1556])).

cnf(c_1002,plain,
    ( X0 != X1
    | u1_struct_0(X0) = u1_struct_0(X1) ),
    theory(equality)).

cnf(c_1012,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_15,plain,
    ( v2_tex_2(X0,X1)
    | ~ v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_465,plain,
    ( v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK1 != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_18])).

cnf(c_466,plain,
    ( v2_tex_2(sK3,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_467,plain,
    ( v2_tex_2(sK3,sK1) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
    | l1_pre_topc(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_10,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_17,negated_conjecture,
    ( ~ v3_tex_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_451,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK0(X1,X0) != X0
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_17])).

cnf(c_452,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2)
    | sK0(sK2,sK4) != sK4 ),
    inference(unflattening,[status(thm)],[c_451])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_454,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | sK0(sK2,sK4) != sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_452,c_23,c_21])).

cnf(c_456,plain,
    ( sK0(sK2,sK4) != sK4
    | v2_tex_2(sK4,sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_454])).

cnf(c_11,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_437,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(X0,sK0(X1,X0))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_17])).

cnf(c_438,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | r1_tarski(sK4,sK0(sK2,sK4))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_440,plain,
    ( r1_tarski(sK4,sK0(sK2,sK4))
    | ~ v2_tex_2(sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_23,c_21])).

cnf(c_441,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | r1_tarski(sK4,sK0(sK2,sK4)) ),
    inference(renaming,[status(thm)],[c_440])).

cnf(c_12,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_423,plain,
    ( ~ v2_tex_2(X0,X1)
    | v2_tex_2(sK0(X1,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_17])).

cnf(c_424,plain,
    ( v2_tex_2(sK0(sK2,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_426,plain,
    ( v2_tex_2(sK0(sK2,sK4),sK2)
    | ~ v2_tex_2(sK4,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_424,c_23,c_21])).

cnf(c_13,plain,
    ( ~ v2_tex_2(X0,X1)
    | v3_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_409,plain,
    ( ~ v2_tex_2(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | sK2 != X1
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_17])).

cnf(c_410,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ l1_pre_topc(sK2) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_412,plain,
    ( ~ v2_tex_2(sK4,sK2)
    | m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_410,c_23,c_21])).

cnf(c_72,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_68,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_28,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8462,c_6889,c_6313,c_6216,c_5765,c_4185,c_4138,c_3738,c_2458,c_2440,c_2206,c_2202,c_1976,c_1975,c_1696,c_1687,c_1012,c_467,c_466,c_456,c_441,c_426,c_412,c_72,c_68,c_19,c_20,c_28,c_21,c_27,c_22,c_26,c_23,c_25,c_24])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:58:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.33/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.33/0.98  
% 3.33/0.98  ------  iProver source info
% 3.33/0.98  
% 3.33/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.33/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.33/0.98  git: non_committed_changes: false
% 3.33/0.98  git: last_make_outside_of_git: false
% 3.33/0.98  
% 3.33/0.98  ------ 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options
% 3.33/0.98  
% 3.33/0.98  --out_options                           all
% 3.33/0.98  --tptp_safe_out                         true
% 3.33/0.98  --problem_path                          ""
% 3.33/0.98  --include_path                          ""
% 3.33/0.98  --clausifier                            res/vclausify_rel
% 3.33/0.98  --clausifier_options                    --mode clausify
% 3.33/0.98  --stdin                                 false
% 3.33/0.98  --stats_out                             all
% 3.33/0.98  
% 3.33/0.98  ------ General Options
% 3.33/0.98  
% 3.33/0.98  --fof                                   false
% 3.33/0.98  --time_out_real                         305.
% 3.33/0.98  --time_out_virtual                      -1.
% 3.33/0.98  --symbol_type_check                     false
% 3.33/0.98  --clausify_out                          false
% 3.33/0.98  --sig_cnt_out                           false
% 3.33/0.98  --trig_cnt_out                          false
% 3.33/0.98  --trig_cnt_out_tolerance                1.
% 3.33/0.98  --trig_cnt_out_sk_spl                   false
% 3.33/0.98  --abstr_cl_out                          false
% 3.33/0.98  
% 3.33/0.98  ------ Global Options
% 3.33/0.98  
% 3.33/0.98  --schedule                              default
% 3.33/0.98  --add_important_lit                     false
% 3.33/0.98  --prop_solver_per_cl                    1000
% 3.33/0.98  --min_unsat_core                        false
% 3.33/0.98  --soft_assumptions                      false
% 3.33/0.98  --soft_lemma_size                       3
% 3.33/0.98  --prop_impl_unit_size                   0
% 3.33/0.98  --prop_impl_unit                        []
% 3.33/0.98  --share_sel_clauses                     true
% 3.33/0.98  --reset_solvers                         false
% 3.33/0.98  --bc_imp_inh                            [conj_cone]
% 3.33/0.98  --conj_cone_tolerance                   3.
% 3.33/0.98  --extra_neg_conj                        none
% 3.33/0.98  --large_theory_mode                     true
% 3.33/0.98  --prolific_symb_bound                   200
% 3.33/0.98  --lt_threshold                          2000
% 3.33/0.98  --clause_weak_htbl                      true
% 3.33/0.98  --gc_record_bc_elim                     false
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing Options
% 3.33/0.98  
% 3.33/0.98  --preprocessing_flag                    true
% 3.33/0.98  --time_out_prep_mult                    0.1
% 3.33/0.98  --splitting_mode                        input
% 3.33/0.98  --splitting_grd                         true
% 3.33/0.98  --splitting_cvd                         false
% 3.33/0.98  --splitting_cvd_svl                     false
% 3.33/0.98  --splitting_nvd                         32
% 3.33/0.98  --sub_typing                            true
% 3.33/0.98  --prep_gs_sim                           true
% 3.33/0.98  --prep_unflatten                        true
% 3.33/0.98  --prep_res_sim                          true
% 3.33/0.98  --prep_upred                            true
% 3.33/0.98  --prep_sem_filter                       exhaustive
% 3.33/0.98  --prep_sem_filter_out                   false
% 3.33/0.98  --pred_elim                             true
% 3.33/0.98  --res_sim_input                         true
% 3.33/0.98  --eq_ax_congr_red                       true
% 3.33/0.98  --pure_diseq_elim                       true
% 3.33/0.98  --brand_transform                       false
% 3.33/0.98  --non_eq_to_eq                          false
% 3.33/0.98  --prep_def_merge                        true
% 3.33/0.98  --prep_def_merge_prop_impl              false
% 3.33/0.98  --prep_def_merge_mbd                    true
% 3.33/0.98  --prep_def_merge_tr_red                 false
% 3.33/0.98  --prep_def_merge_tr_cl                  false
% 3.33/0.98  --smt_preprocessing                     true
% 3.33/0.98  --smt_ac_axioms                         fast
% 3.33/0.98  --preprocessed_out                      false
% 3.33/0.98  --preprocessed_stats                    false
% 3.33/0.98  
% 3.33/0.98  ------ Abstraction refinement Options
% 3.33/0.98  
% 3.33/0.98  --abstr_ref                             []
% 3.33/0.98  --abstr_ref_prep                        false
% 3.33/0.98  --abstr_ref_until_sat                   false
% 3.33/0.98  --abstr_ref_sig_restrict                funpre
% 3.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.98  --abstr_ref_under                       []
% 3.33/0.98  
% 3.33/0.98  ------ SAT Options
% 3.33/0.98  
% 3.33/0.98  --sat_mode                              false
% 3.33/0.98  --sat_fm_restart_options                ""
% 3.33/0.98  --sat_gr_def                            false
% 3.33/0.98  --sat_epr_types                         true
% 3.33/0.98  --sat_non_cyclic_types                  false
% 3.33/0.98  --sat_finite_models                     false
% 3.33/0.98  --sat_fm_lemmas                         false
% 3.33/0.98  --sat_fm_prep                           false
% 3.33/0.98  --sat_fm_uc_incr                        true
% 3.33/0.98  --sat_out_model                         small
% 3.33/0.98  --sat_out_clauses                       false
% 3.33/0.98  
% 3.33/0.98  ------ QBF Options
% 3.33/0.98  
% 3.33/0.98  --qbf_mode                              false
% 3.33/0.98  --qbf_elim_univ                         false
% 3.33/0.98  --qbf_dom_inst                          none
% 3.33/0.98  --qbf_dom_pre_inst                      false
% 3.33/0.98  --qbf_sk_in                             false
% 3.33/0.98  --qbf_pred_elim                         true
% 3.33/0.98  --qbf_split                             512
% 3.33/0.98  
% 3.33/0.98  ------ BMC1 Options
% 3.33/0.98  
% 3.33/0.98  --bmc1_incremental                      false
% 3.33/0.98  --bmc1_axioms                           reachable_all
% 3.33/0.98  --bmc1_min_bound                        0
% 3.33/0.98  --bmc1_max_bound                        -1
% 3.33/0.98  --bmc1_max_bound_default                -1
% 3.33/0.98  --bmc1_symbol_reachability              true
% 3.33/0.98  --bmc1_property_lemmas                  false
% 3.33/0.98  --bmc1_k_induction                      false
% 3.33/0.98  --bmc1_non_equiv_states                 false
% 3.33/0.98  --bmc1_deadlock                         false
% 3.33/0.98  --bmc1_ucm                              false
% 3.33/0.98  --bmc1_add_unsat_core                   none
% 3.33/0.98  --bmc1_unsat_core_children              false
% 3.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.98  --bmc1_out_stat                         full
% 3.33/0.98  --bmc1_ground_init                      false
% 3.33/0.98  --bmc1_pre_inst_next_state              false
% 3.33/0.98  --bmc1_pre_inst_state                   false
% 3.33/0.98  --bmc1_pre_inst_reach_state             false
% 3.33/0.98  --bmc1_out_unsat_core                   false
% 3.33/0.98  --bmc1_aig_witness_out                  false
% 3.33/0.98  --bmc1_verbose                          false
% 3.33/0.98  --bmc1_dump_clauses_tptp                false
% 3.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.98  --bmc1_dump_file                        -
% 3.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.98  --bmc1_ucm_extend_mode                  1
% 3.33/0.98  --bmc1_ucm_init_mode                    2
% 3.33/0.98  --bmc1_ucm_cone_mode                    none
% 3.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.98  --bmc1_ucm_relax_model                  4
% 3.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.98  --bmc1_ucm_layered_model                none
% 3.33/0.98  --bmc1_ucm_max_lemma_size               10
% 3.33/0.98  
% 3.33/0.98  ------ AIG Options
% 3.33/0.98  
% 3.33/0.98  --aig_mode                              false
% 3.33/0.98  
% 3.33/0.98  ------ Instantiation Options
% 3.33/0.98  
% 3.33/0.98  --instantiation_flag                    true
% 3.33/0.98  --inst_sos_flag                         false
% 3.33/0.98  --inst_sos_phase                        true
% 3.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel_side                     num_symb
% 3.33/0.98  --inst_solver_per_active                1400
% 3.33/0.98  --inst_solver_calls_frac                1.
% 3.33/0.98  --inst_passive_queue_type               priority_queues
% 3.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.98  --inst_passive_queues_freq              [25;2]
% 3.33/0.98  --inst_dismatching                      true
% 3.33/0.98  --inst_eager_unprocessed_to_passive     true
% 3.33/0.98  --inst_prop_sim_given                   true
% 3.33/0.98  --inst_prop_sim_new                     false
% 3.33/0.98  --inst_subs_new                         false
% 3.33/0.98  --inst_eq_res_simp                      false
% 3.33/0.98  --inst_subs_given                       false
% 3.33/0.98  --inst_orphan_elimination               true
% 3.33/0.98  --inst_learning_loop_flag               true
% 3.33/0.98  --inst_learning_start                   3000
% 3.33/0.98  --inst_learning_factor                  2
% 3.33/0.98  --inst_start_prop_sim_after_learn       3
% 3.33/0.98  --inst_sel_renew                        solver
% 3.33/0.98  --inst_lit_activity_flag                true
% 3.33/0.98  --inst_restr_to_given                   false
% 3.33/0.98  --inst_activity_threshold               500
% 3.33/0.98  --inst_out_proof                        true
% 3.33/0.98  
% 3.33/0.98  ------ Resolution Options
% 3.33/0.98  
% 3.33/0.98  --resolution_flag                       true
% 3.33/0.98  --res_lit_sel                           adaptive
% 3.33/0.98  --res_lit_sel_side                      none
% 3.33/0.98  --res_ordering                          kbo
% 3.33/0.98  --res_to_prop_solver                    active
% 3.33/0.98  --res_prop_simpl_new                    false
% 3.33/0.98  --res_prop_simpl_given                  true
% 3.33/0.98  --res_passive_queue_type                priority_queues
% 3.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.98  --res_passive_queues_freq               [15;5]
% 3.33/0.98  --res_forward_subs                      full
% 3.33/0.98  --res_backward_subs                     full
% 3.33/0.98  --res_forward_subs_resolution           true
% 3.33/0.98  --res_backward_subs_resolution          true
% 3.33/0.98  --res_orphan_elimination                true
% 3.33/0.98  --res_time_limit                        2.
% 3.33/0.98  --res_out_proof                         true
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Options
% 3.33/0.98  
% 3.33/0.98  --superposition_flag                    true
% 3.33/0.98  --sup_passive_queue_type                priority_queues
% 3.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.98  --demod_completeness_check              fast
% 3.33/0.98  --demod_use_ground                      true
% 3.33/0.98  --sup_to_prop_solver                    passive
% 3.33/0.98  --sup_prop_simpl_new                    true
% 3.33/0.98  --sup_prop_simpl_given                  true
% 3.33/0.98  --sup_fun_splitting                     false
% 3.33/0.98  --sup_smt_interval                      50000
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Simplification Setup
% 3.33/0.98  
% 3.33/0.98  --sup_indices_passive                   []
% 3.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_full_bw                           [BwDemod]
% 3.33/0.98  --sup_immed_triv                        [TrivRules]
% 3.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_immed_bw_main                     []
% 3.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  
% 3.33/0.98  ------ Combination Options
% 3.33/0.98  
% 3.33/0.98  --comb_res_mult                         3
% 3.33/0.98  --comb_sup_mult                         2
% 3.33/0.98  --comb_inst_mult                        10
% 3.33/0.98  
% 3.33/0.98  ------ Debug Options
% 3.33/0.98  
% 3.33/0.98  --dbg_backtrace                         false
% 3.33/0.98  --dbg_dump_prop_clauses                 false
% 3.33/0.98  --dbg_dump_prop_clauses_file            -
% 3.33/0.98  --dbg_out_stat                          false
% 3.33/0.98  ------ Parsing...
% 3.33/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.33/0.98  ------ Proving...
% 3.33/0.98  ------ Problem Properties 
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  clauses                                 23
% 3.33/0.98  conjectures                             8
% 3.33/0.98  EPR                                     8
% 3.33/0.98  Horn                                    20
% 3.33/0.98  unary                                   9
% 3.33/0.98  binary                                  3
% 3.33/0.98  lits                                    66
% 3.33/0.98  lits eq                                 6
% 3.33/0.98  fd_pure                                 0
% 3.33/0.98  fd_pseudo                               0
% 3.33/0.98  fd_cond                                 0
% 3.33/0.98  fd_pseudo_cond                          2
% 3.33/0.98  AC symbols                              0
% 3.33/0.98  
% 3.33/0.98  ------ Schedule dynamic 5 is on 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  ------ 
% 3.33/0.98  Current options:
% 3.33/0.98  ------ 
% 3.33/0.98  
% 3.33/0.98  ------ Input Options
% 3.33/0.98  
% 3.33/0.98  --out_options                           all
% 3.33/0.98  --tptp_safe_out                         true
% 3.33/0.98  --problem_path                          ""
% 3.33/0.98  --include_path                          ""
% 3.33/0.98  --clausifier                            res/vclausify_rel
% 3.33/0.98  --clausifier_options                    --mode clausify
% 3.33/0.98  --stdin                                 false
% 3.33/0.98  --stats_out                             all
% 3.33/0.98  
% 3.33/0.98  ------ General Options
% 3.33/0.98  
% 3.33/0.98  --fof                                   false
% 3.33/0.98  --time_out_real                         305.
% 3.33/0.98  --time_out_virtual                      -1.
% 3.33/0.98  --symbol_type_check                     false
% 3.33/0.98  --clausify_out                          false
% 3.33/0.98  --sig_cnt_out                           false
% 3.33/0.98  --trig_cnt_out                          false
% 3.33/0.98  --trig_cnt_out_tolerance                1.
% 3.33/0.98  --trig_cnt_out_sk_spl                   false
% 3.33/0.98  --abstr_cl_out                          false
% 3.33/0.98  
% 3.33/0.98  ------ Global Options
% 3.33/0.98  
% 3.33/0.98  --schedule                              default
% 3.33/0.98  --add_important_lit                     false
% 3.33/0.98  --prop_solver_per_cl                    1000
% 3.33/0.98  --min_unsat_core                        false
% 3.33/0.98  --soft_assumptions                      false
% 3.33/0.98  --soft_lemma_size                       3
% 3.33/0.98  --prop_impl_unit_size                   0
% 3.33/0.98  --prop_impl_unit                        []
% 3.33/0.98  --share_sel_clauses                     true
% 3.33/0.98  --reset_solvers                         false
% 3.33/0.98  --bc_imp_inh                            [conj_cone]
% 3.33/0.98  --conj_cone_tolerance                   3.
% 3.33/0.98  --extra_neg_conj                        none
% 3.33/0.98  --large_theory_mode                     true
% 3.33/0.98  --prolific_symb_bound                   200
% 3.33/0.98  --lt_threshold                          2000
% 3.33/0.98  --clause_weak_htbl                      true
% 3.33/0.98  --gc_record_bc_elim                     false
% 3.33/0.98  
% 3.33/0.98  ------ Preprocessing Options
% 3.33/0.98  
% 3.33/0.98  --preprocessing_flag                    true
% 3.33/0.98  --time_out_prep_mult                    0.1
% 3.33/0.98  --splitting_mode                        input
% 3.33/0.98  --splitting_grd                         true
% 3.33/0.98  --splitting_cvd                         false
% 3.33/0.98  --splitting_cvd_svl                     false
% 3.33/0.98  --splitting_nvd                         32
% 3.33/0.98  --sub_typing                            true
% 3.33/0.98  --prep_gs_sim                           true
% 3.33/0.98  --prep_unflatten                        true
% 3.33/0.98  --prep_res_sim                          true
% 3.33/0.98  --prep_upred                            true
% 3.33/0.98  --prep_sem_filter                       exhaustive
% 3.33/0.98  --prep_sem_filter_out                   false
% 3.33/0.98  --pred_elim                             true
% 3.33/0.98  --res_sim_input                         true
% 3.33/0.98  --eq_ax_congr_red                       true
% 3.33/0.98  --pure_diseq_elim                       true
% 3.33/0.98  --brand_transform                       false
% 3.33/0.98  --non_eq_to_eq                          false
% 3.33/0.98  --prep_def_merge                        true
% 3.33/0.98  --prep_def_merge_prop_impl              false
% 3.33/0.98  --prep_def_merge_mbd                    true
% 3.33/0.98  --prep_def_merge_tr_red                 false
% 3.33/0.98  --prep_def_merge_tr_cl                  false
% 3.33/0.98  --smt_preprocessing                     true
% 3.33/0.98  --smt_ac_axioms                         fast
% 3.33/0.98  --preprocessed_out                      false
% 3.33/0.98  --preprocessed_stats                    false
% 3.33/0.98  
% 3.33/0.98  ------ Abstraction refinement Options
% 3.33/0.98  
% 3.33/0.98  --abstr_ref                             []
% 3.33/0.98  --abstr_ref_prep                        false
% 3.33/0.98  --abstr_ref_until_sat                   false
% 3.33/0.98  --abstr_ref_sig_restrict                funpre
% 3.33/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.33/0.98  --abstr_ref_under                       []
% 3.33/0.98  
% 3.33/0.98  ------ SAT Options
% 3.33/0.98  
% 3.33/0.98  --sat_mode                              false
% 3.33/0.98  --sat_fm_restart_options                ""
% 3.33/0.98  --sat_gr_def                            false
% 3.33/0.98  --sat_epr_types                         true
% 3.33/0.98  --sat_non_cyclic_types                  false
% 3.33/0.98  --sat_finite_models                     false
% 3.33/0.98  --sat_fm_lemmas                         false
% 3.33/0.98  --sat_fm_prep                           false
% 3.33/0.98  --sat_fm_uc_incr                        true
% 3.33/0.98  --sat_out_model                         small
% 3.33/0.98  --sat_out_clauses                       false
% 3.33/0.98  
% 3.33/0.98  ------ QBF Options
% 3.33/0.98  
% 3.33/0.98  --qbf_mode                              false
% 3.33/0.98  --qbf_elim_univ                         false
% 3.33/0.98  --qbf_dom_inst                          none
% 3.33/0.98  --qbf_dom_pre_inst                      false
% 3.33/0.98  --qbf_sk_in                             false
% 3.33/0.98  --qbf_pred_elim                         true
% 3.33/0.98  --qbf_split                             512
% 3.33/0.98  
% 3.33/0.98  ------ BMC1 Options
% 3.33/0.98  
% 3.33/0.98  --bmc1_incremental                      false
% 3.33/0.98  --bmc1_axioms                           reachable_all
% 3.33/0.98  --bmc1_min_bound                        0
% 3.33/0.98  --bmc1_max_bound                        -1
% 3.33/0.98  --bmc1_max_bound_default                -1
% 3.33/0.98  --bmc1_symbol_reachability              true
% 3.33/0.98  --bmc1_property_lemmas                  false
% 3.33/0.98  --bmc1_k_induction                      false
% 3.33/0.98  --bmc1_non_equiv_states                 false
% 3.33/0.98  --bmc1_deadlock                         false
% 3.33/0.98  --bmc1_ucm                              false
% 3.33/0.98  --bmc1_add_unsat_core                   none
% 3.33/0.98  --bmc1_unsat_core_children              false
% 3.33/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.33/0.98  --bmc1_out_stat                         full
% 3.33/0.98  --bmc1_ground_init                      false
% 3.33/0.98  --bmc1_pre_inst_next_state              false
% 3.33/0.98  --bmc1_pre_inst_state                   false
% 3.33/0.98  --bmc1_pre_inst_reach_state             false
% 3.33/0.98  --bmc1_out_unsat_core                   false
% 3.33/0.98  --bmc1_aig_witness_out                  false
% 3.33/0.98  --bmc1_verbose                          false
% 3.33/0.98  --bmc1_dump_clauses_tptp                false
% 3.33/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.33/0.98  --bmc1_dump_file                        -
% 3.33/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.33/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.33/0.98  --bmc1_ucm_extend_mode                  1
% 3.33/0.98  --bmc1_ucm_init_mode                    2
% 3.33/0.98  --bmc1_ucm_cone_mode                    none
% 3.33/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.33/0.98  --bmc1_ucm_relax_model                  4
% 3.33/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.33/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.33/0.98  --bmc1_ucm_layered_model                none
% 3.33/0.98  --bmc1_ucm_max_lemma_size               10
% 3.33/0.98  
% 3.33/0.98  ------ AIG Options
% 3.33/0.98  
% 3.33/0.98  --aig_mode                              false
% 3.33/0.98  
% 3.33/0.98  ------ Instantiation Options
% 3.33/0.98  
% 3.33/0.98  --instantiation_flag                    true
% 3.33/0.98  --inst_sos_flag                         false
% 3.33/0.98  --inst_sos_phase                        true
% 3.33/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.33/0.98  --inst_lit_sel_side                     none
% 3.33/0.98  --inst_solver_per_active                1400
% 3.33/0.98  --inst_solver_calls_frac                1.
% 3.33/0.98  --inst_passive_queue_type               priority_queues
% 3.33/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.33/0.98  --inst_passive_queues_freq              [25;2]
% 3.33/0.98  --inst_dismatching                      true
% 3.33/0.98  --inst_eager_unprocessed_to_passive     true
% 3.33/0.98  --inst_prop_sim_given                   true
% 3.33/0.98  --inst_prop_sim_new                     false
% 3.33/0.98  --inst_subs_new                         false
% 3.33/0.98  --inst_eq_res_simp                      false
% 3.33/0.98  --inst_subs_given                       false
% 3.33/0.98  --inst_orphan_elimination               true
% 3.33/0.98  --inst_learning_loop_flag               true
% 3.33/0.98  --inst_learning_start                   3000
% 3.33/0.98  --inst_learning_factor                  2
% 3.33/0.98  --inst_start_prop_sim_after_learn       3
% 3.33/0.98  --inst_sel_renew                        solver
% 3.33/0.98  --inst_lit_activity_flag                true
% 3.33/0.98  --inst_restr_to_given                   false
% 3.33/0.98  --inst_activity_threshold               500
% 3.33/0.98  --inst_out_proof                        true
% 3.33/0.98  
% 3.33/0.98  ------ Resolution Options
% 3.33/0.98  
% 3.33/0.98  --resolution_flag                       false
% 3.33/0.98  --res_lit_sel                           adaptive
% 3.33/0.98  --res_lit_sel_side                      none
% 3.33/0.98  --res_ordering                          kbo
% 3.33/0.98  --res_to_prop_solver                    active
% 3.33/0.98  --res_prop_simpl_new                    false
% 3.33/0.98  --res_prop_simpl_given                  true
% 3.33/0.98  --res_passive_queue_type                priority_queues
% 3.33/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.33/0.98  --res_passive_queues_freq               [15;5]
% 3.33/0.98  --res_forward_subs                      full
% 3.33/0.98  --res_backward_subs                     full
% 3.33/0.98  --res_forward_subs_resolution           true
% 3.33/0.98  --res_backward_subs_resolution          true
% 3.33/0.98  --res_orphan_elimination                true
% 3.33/0.98  --res_time_limit                        2.
% 3.33/0.98  --res_out_proof                         true
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Options
% 3.33/0.98  
% 3.33/0.98  --superposition_flag                    true
% 3.33/0.98  --sup_passive_queue_type                priority_queues
% 3.33/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.33/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.33/0.98  --demod_completeness_check              fast
% 3.33/0.98  --demod_use_ground                      true
% 3.33/0.98  --sup_to_prop_solver                    passive
% 3.33/0.98  --sup_prop_simpl_new                    true
% 3.33/0.98  --sup_prop_simpl_given                  true
% 3.33/0.98  --sup_fun_splitting                     false
% 3.33/0.98  --sup_smt_interval                      50000
% 3.33/0.98  
% 3.33/0.98  ------ Superposition Simplification Setup
% 3.33/0.98  
% 3.33/0.98  --sup_indices_passive                   []
% 3.33/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.33/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.33/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_full_bw                           [BwDemod]
% 3.33/0.98  --sup_immed_triv                        [TrivRules]
% 3.33/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.33/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_immed_bw_main                     []
% 3.33/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.33/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.33/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.33/0.98  
% 3.33/0.98  ------ Combination Options
% 3.33/0.98  
% 3.33/0.98  --comb_res_mult                         3
% 3.33/0.98  --comb_sup_mult                         2
% 3.33/0.98  --comb_inst_mult                        10
% 3.33/0.98  
% 3.33/0.98  ------ Debug Options
% 3.33/0.98  
% 3.33/0.98  --dbg_backtrace                         false
% 3.33/0.98  --dbg_dump_prop_clauses                 false
% 3.33/0.98  --dbg_dump_prop_clauses_file            -
% 3.33/0.98  --dbg_out_stat                          false
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  ------ Proving...
% 3.33/0.98  
% 3.33/0.98  
% 3.33/0.98  % SZS status Theorem for theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.33/0.98  
% 3.33/0.98  fof(f6,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f14,plain,(
% 3.33/0.98    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f6])).
% 3.33/0.98  
% 3.33/0.98  fof(f44,plain,(
% 3.33/0.98    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f14])).
% 3.33/0.98  
% 3.33/0.98  fof(f9,conjecture,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f10,negated_conjecture,(
% 3.33/0.98    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tex_2(X3,X1))))))),
% 3.33/0.98    inference(negated_conjecture,[],[f9])).
% 3.33/0.98  
% 3.33/0.98  fof(f19,plain,(
% 3.33/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v3_tex_2(X3,X1) & (v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f10])).
% 3.33/0.98  
% 3.33/0.98  fof(f20,plain,(
% 3.33/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 3.33/0.98    inference(flattening,[],[f19])).
% 3.33/0.98  
% 3.33/0.98  fof(f33,plain,(
% 3.33/0.98    ( ! [X2,X0,X1] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v3_tex_2(sK4,X1) & v3_tex_2(X2,X0) & sK4 = X2 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1))))) )),
% 3.33/0.98    introduced(choice_axiom,[])).
% 3.33/0.98  
% 3.33/0.98  fof(f32,plain,(
% 3.33/0.98    ( ! [X0,X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(sK3,X0) & sK3 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(X0))))) )),
% 3.33/0.98    introduced(choice_axiom,[])).
% 3.33/0.98  
% 3.33/0.98  fof(f31,plain,(
% 3.33/0.98    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) => (? [X2] : (? [X3] : (~v3_tex_2(X3,sK2) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(sK2))) )),
% 3.33/0.98    introduced(choice_axiom,[])).
% 3.33/0.98  
% 3.33/0.98  fof(f30,plain,(
% 3.33/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X1)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : (~v3_tex_2(X3,X1) & v3_tex_2(X2,sK1) & X2 = X3 & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(X1)) & l1_pre_topc(sK1))),
% 3.33/0.98    introduced(choice_axiom,[])).
% 3.33/0.98  
% 3.33/0.98  fof(f34,plain,(
% 3.33/0.98    (((~v3_tex_2(sK4,sK2) & v3_tex_2(sK3,sK1) & sK3 = sK4 & g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) & m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & l1_pre_topc(sK2)) & l1_pre_topc(sK1)),
% 3.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f20,f33,f32,f31,f30])).
% 3.33/0.98  
% 3.33/0.98  fof(f56,plain,(
% 3.33/0.98    g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f4,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f12,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f4])).
% 3.33/0.98  
% 3.33/0.98  fof(f24,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(nnf_transformation,[],[f12])).
% 3.33/0.98  
% 3.33/0.98  fof(f41,plain,(
% 3.33/0.98    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f24])).
% 3.33/0.98  
% 3.33/0.98  fof(f52,plain,(
% 3.33/0.98    l1_pre_topc(sK1)),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f3,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f11,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f3])).
% 3.33/0.98  
% 3.33/0.98  fof(f40,plain,(
% 3.33/0.98    ( ! [X0,X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f11])).
% 3.33/0.98  
% 3.33/0.98  fof(f53,plain,(
% 3.33/0.98    l1_pre_topc(sK2)),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f5,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f13,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f5])).
% 3.33/0.98  
% 3.33/0.98  fof(f43,plain,(
% 3.33/0.98    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f13])).
% 3.33/0.98  
% 3.33/0.98  fof(f2,axiom,(
% 3.33/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f23,plain,(
% 3.33/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.33/0.98    inference(nnf_transformation,[],[f2])).
% 3.33/0.98  
% 3.33/0.98  fof(f38,plain,(
% 3.33/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.33/0.98    inference(cnf_transformation,[],[f23])).
% 3.33/0.98  
% 3.33/0.98  fof(f1,axiom,(
% 3.33/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f21,plain,(
% 3.33/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/0.98    inference(nnf_transformation,[],[f1])).
% 3.33/0.98  
% 3.33/0.98  fof(f22,plain,(
% 3.33/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.33/0.98    inference(flattening,[],[f21])).
% 3.33/0.98  
% 3.33/0.98  fof(f37,plain,(
% 3.33/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f22])).
% 3.33/0.98  
% 3.33/0.98  fof(f39,plain,(
% 3.33/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f23])).
% 3.33/0.98  
% 3.33/0.98  fof(f8,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((v2_tex_2(X2,X0) & X2 = X3 & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v2_tex_2(X3,X1))))))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f17,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v2_tex_2(X3,X1) | (~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f8])).
% 3.33/0.98  
% 3.33/0.98  fof(f18,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(flattening,[],[f17])).
% 3.33/0.98  
% 3.33/0.98  fof(f51,plain,(
% 3.33/0.98    ( ! [X2,X0,X3,X1] : (v2_tex_2(X3,X1) | ~v2_tex_2(X2,X0) | X2 != X3 | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f18])).
% 3.33/0.98  
% 3.33/0.98  fof(f62,plain,(
% 3.33/0.98    ( ! [X0,X3,X1] : (v2_tex_2(X3,X1) | ~v2_tex_2(X3,X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(equality_resolution,[],[f51])).
% 3.33/0.98  
% 3.33/0.98  fof(f7,axiom,(
% 3.33/0.98    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 3.33/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.33/0.98  
% 3.33/0.98  fof(f15,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(ennf_transformation,[],[f7])).
% 3.33/0.98  
% 3.33/0.98  fof(f16,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(flattening,[],[f15])).
% 3.33/0.98  
% 3.33/0.98  fof(f25,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(nnf_transformation,[],[f16])).
% 3.33/0.98  
% 3.33/0.98  fof(f26,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(flattening,[],[f25])).
% 3.33/0.98  
% 3.33/0.98  fof(f27,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(rectify,[],[f26])).
% 3.33/0.98  
% 3.33/0.98  fof(f28,plain,(
% 3.33/0.98    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.33/0.98    introduced(choice_axiom,[])).
% 3.33/0.98  
% 3.33/0.98  fof(f29,plain,(
% 3.33/0.98    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK0(X0,X1) != X1 & r1_tarski(X1,sK0(X0,X1)) & v2_tex_2(sK0(X0,X1),X0) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.33/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f27,f28])).
% 3.33/0.98  
% 3.33/0.98  fof(f46,plain,(
% 3.33/0.98    ( ! [X0,X3,X1] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f54,plain,(
% 3.33/0.98    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f57,plain,(
% 3.33/0.98    sK3 = sK4),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f58,plain,(
% 3.33/0.98    v3_tex_2(sK3,sK1)),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f45,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f50,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | sK0(X0,X1) != X1 | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f59,plain,(
% 3.33/0.98    ~v3_tex_2(sK4,sK2)),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f55,plain,(
% 3.33/0.98    m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))),
% 3.33/0.98    inference(cnf_transformation,[],[f34])).
% 3.33/0.98  
% 3.33/0.98  fof(f49,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | r1_tarski(X1,sK0(X0,X1)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f48,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | v2_tex_2(sK0(X0,X1),X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f47,plain,(
% 3.33/0.98    ( ! [X0,X1] : (v3_tex_2(X1,X0) | m1_subset_1(sK0(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.33/0.98    inference(cnf_transformation,[],[f29])).
% 3.33/0.98  
% 3.33/0.98  fof(f35,plain,(
% 3.33/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.33/0.98    inference(cnf_transformation,[],[f22])).
% 3.33/0.98  
% 3.33/0.98  fof(f61,plain,(
% 3.33/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.33/0.98    inference(equality_resolution,[],[f35])).
% 3.33/0.98  
% 3.33/0.98  cnf(c_9,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X0) | ~ l1_pre_topc(X0) ),
% 3.33/0.98      inference(cnf_transformation,[],[f44]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1542,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_20,negated_conjecture,
% 3.33/0.98      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.33/0.98      inference(cnf_transformation,[],[f56]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_7,plain,
% 3.33/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.33/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X0)
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1544,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3492,plain,
% 3.33/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_20,c_1544]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_24,negated_conjecture,
% 3.33/0.98      ( l1_pre_topc(sK1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_25,plain,
% 3.33/0.98      ( l1_pre_topc(sK1) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3607,plain,
% 3.33/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3492,c_25]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3608,plain,
% 3.33/0.98      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK1) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_3607]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_5,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1)
% 3.33/0.98      | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1545,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3614,plain,
% 3.33/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_3608,c_1545]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_23,negated_conjecture,
% 3.33/0.98      ( l1_pre_topc(sK2) ),
% 3.33/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_26,plain,
% 3.33/0.98      ( l1_pre_topc(sK2) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3838,plain,
% 3.33/0.98      ( l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) = iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK1) != iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3614,c_26]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3839,plain,
% 3.33/0.98      ( m1_pre_topc(X0,sK1) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(renaming,[status(thm)],[c_3838]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3847,plain,
% 3.33/0.98      ( m1_pre_topc(sK1,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1542,c_3839]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_50,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X0) = iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_52,plain,
% 3.33/0.98      ( m1_pre_topc(sK1,sK1) = iProver_top
% 3.33/0.98      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_50]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3625,plain,
% 3.33/0.98      ( m1_pre_topc(sK1,sK1) != iProver_top
% 3.33/0.98      | m1_pre_topc(sK1,sK2) = iProver_top
% 3.33/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_3614]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4158,plain,
% 3.33/0.98      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 3.33/0.98      inference(global_propositional_subsumption,
% 3.33/0.98                [status(thm)],
% 3.33/0.98                [c_3847,c_25,c_26,c_52,c_3625]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8,plain,
% 3.33/0.98      ( ~ m1_pre_topc(X0,X1)
% 3.33/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.98      | ~ l1_pre_topc(X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f43]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1543,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.33/0.98      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1))) = iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1546,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.33/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2665,plain,
% 3.33/0.98      ( m1_pre_topc(X0,X1) != iProver_top
% 3.33/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) = iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_1543,c_1546]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_0,plain,
% 3.33/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.33/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_1549,plain,
% 3.33/0.98      ( X0 = X1
% 3.33/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.33/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.33/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4581,plain,
% 3.33/0.98      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.33/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.33/0.98      | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_2665,c_1549]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_5596,plain,
% 3.33/0.98      ( u1_struct_0(X0) = u1_struct_0(X1)
% 3.33/0.98      | m1_pre_topc(X1,X0) != iProver_top
% 3.33/0.98      | m1_pre_topc(X0,X1) != iProver_top
% 3.33/0.98      | l1_pre_topc(X0) != iProver_top
% 3.33/0.98      | l1_pre_topc(X1) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_2665,c_4581]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_8462,plain,
% 3.33/0.98      ( u1_struct_0(sK2) = u1_struct_0(sK1)
% 3.33/0.98      | m1_pre_topc(sK2,sK1) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK1) != iProver_top
% 3.33/0.98      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.98      inference(superposition,[status(thm)],[c_4158,c_5596]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_998,plain,
% 3.33/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X0,X2) | X2 != X1 ),
% 3.33/0.98      theory(equality) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2903,plain,
% 3.33/0.98      ( ~ r1_tarski(X0,X1)
% 3.33/0.98      | r1_tarski(X0,u1_struct_0(sK1))
% 3.33/0.98      | u1_struct_0(sK1) != X1 ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_998]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3834,plain,
% 3.33/0.98      ( ~ r1_tarski(X0,u1_struct_0(X1))
% 3.33/0.98      | r1_tarski(X0,u1_struct_0(sK1))
% 3.33/0.98      | u1_struct_0(sK1) != u1_struct_0(X1) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_2903]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6889,plain,
% 3.33/0.98      ( r1_tarski(sK0(sK2,sK4),u1_struct_0(sK1))
% 3.33/0.98      | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(sK2))
% 3.33/0.98      | u1_struct_0(sK1) != u1_struct_0(sK2) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_3834]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_997,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_2986,plain,
% 3.33/0.98      ( X0 != X1 | u1_struct_0(sK1) != X1 | u1_struct_0(sK1) = X0 ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_997]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3897,plain,
% 3.33/0.98      ( X0 != u1_struct_0(sK1)
% 3.33/0.98      | u1_struct_0(sK1) = X0
% 3.33/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_2986]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4974,plain,
% 3.33/0.98      ( u1_struct_0(X0) != u1_struct_0(sK1)
% 3.33/0.98      | u1_struct_0(sK1) = u1_struct_0(X0)
% 3.33/0.98      | u1_struct_0(sK1) != u1_struct_0(sK1) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_3897]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6313,plain,
% 3.33/0.98      ( u1_struct_0(sK1) != u1_struct_0(sK1)
% 3.33/0.98      | u1_struct_0(sK1) = u1_struct_0(sK2)
% 3.33/0.98      | u1_struct_0(sK2) != u1_struct_0(sK1) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_4974]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_4684,plain,
% 3.33/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.98      | r1_tarski(X0,u1_struct_0(sK2)) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_6216,plain,
% 3.33/0.98      ( ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.98      | r1_tarski(sK0(sK2,sK4),u1_struct_0(sK2)) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_4684]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_3,plain,
% 3.33/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.33/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.33/0.98  
% 3.33/0.98  cnf(c_5763,plain,
% 3.33/0.98      ( m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.98      | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(X0)) ),
% 3.33/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_5765,plain,
% 3.33/0.99      ( m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.33/0.99      | ~ r1_tarski(sK0(sK2,sK4),u1_struct_0(sK1)) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_5763]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_16,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v2_tex_2(X0,X2)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | ~ l1_pre_topc(X2)
% 3.33/0.99      | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ),
% 3.33/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4166,plain,
% 3.33/0.99      ( v2_tex_2(sK0(sK2,sK4),X0)
% 3.33/0.99      | ~ v2_tex_2(sK0(sK2,sK4),sK2)
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | ~ l1_pre_topc(sK2)
% 3.33/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4185,plain,
% 3.33/0.99      ( v2_tex_2(sK0(sK2,sK4),sK1)
% 3.33/0.99      | ~ v2_tex_2(sK0(sK2,sK4),sK2)
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ l1_pre_topc(sK1)
% 3.33/0.99      | ~ l1_pre_topc(sK2)
% 3.33/0.99      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_4166]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_14,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | ~ v3_tex_2(X2,X1)
% 3.33/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ r1_tarski(X2,X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | X0 = X2 ),
% 3.33/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1969,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | ~ v3_tex_2(sK4,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ r1_tarski(sK4,X0)
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | X0 = sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4136,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK0(sK2,sK4),X0)
% 3.33/0.99      | ~ v3_tex_2(sK4,X0)
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(X0)))
% 3.33/0.99      | ~ r1_tarski(sK4,sK0(sK2,sK4))
% 3.33/0.99      | ~ l1_pre_topc(X0)
% 3.33/0.99      | sK0(sK2,sK4) = sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1969]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_4138,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK0(sK2,sK4),sK1)
% 3.33/0.99      | ~ v3_tex_2(sK4,sK1)
% 3.33/0.99      | ~ m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK1)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.33/0.99      | ~ r1_tarski(sK4,sK0(sK2,sK4))
% 3.33/0.99      | ~ l1_pre_topc(sK1)
% 3.33/0.99      | sK0(sK2,sK4) = sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_4136]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2837,plain,
% 3.33/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK1) = iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_20,c_1545]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2855,plain,
% 3.33/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.33/0.99      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_2837,c_25]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2856,plain,
% 3.33/0.99      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) != iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_2855]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3494,plain,
% 3.33/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_1544,c_2856]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3731,plain,
% 3.33/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK1) = iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_3494,c_26]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3732,plain,
% 3.33/0.99      ( m1_pre_topc(X0,sK1) = iProver_top
% 3.33/0.99      | m1_pre_topc(X0,sK2) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_3731]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_3738,plain,
% 3.33/0.99      ( m1_pre_topc(sK2,sK1) = iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_1542,c_3732]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_22,negated_conjecture,
% 3.33/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.33/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1531,plain,
% 3.33/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_19,negated_conjecture,
% 3.33/0.99      ( sK3 = sK4 ),
% 3.33/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1563,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_1531,c_19]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1535,plain,
% 3.33/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
% 3.33/0.99      | v2_tex_2(X2,X1) != iProver_top
% 3.33/0.99      | v2_tex_2(X2,X0) = iProver_top
% 3.33/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) != iProver_top
% 3.33/0.99      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X1) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1902,plain,
% 3.33/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.33/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.33/0.99      | v2_tex_2(X1,sK1) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_20,c_1535]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2213,plain,
% 3.33/0.99      ( l1_pre_topc(X0) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.99      | v2_tex_2(X1,sK1) != iProver_top
% 3.33/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.33/0.99      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_1902,c_25]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2214,plain,
% 3.33/0.99      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 3.33/0.99      | v2_tex_2(X1,X0) = iProver_top
% 3.33/0.99      | v2_tex_2(X1,sK1) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) != iProver_top
% 3.33/0.99      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | l1_pre_topc(X0) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_2213]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2224,plain,
% 3.33/0.99      ( v2_tex_2(X0,sK1) != iProver_top
% 3.33/0.99      | v2_tex_2(X0,sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK2) != iProver_top ),
% 3.33/0.99      inference(equality_resolution,[status(thm)],[c_2214]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2429,plain,
% 3.33/0.99      ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top
% 3.33/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | v2_tex_2(X0,sK2) = iProver_top
% 3.33/0.99      | v2_tex_2(X0,sK1) != iProver_top ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_2224,c_26]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2430,plain,
% 3.33/0.99      ( v2_tex_2(X0,sK1) != iProver_top
% 3.33/0.99      | v2_tex_2(X0,sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_2429]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2440,plain,
% 3.33/0.99      ( v2_tex_2(sK4,sK1) != iProver_top
% 3.33/0.99      | v2_tex_2(sK4,sK2) = iProver_top
% 3.33/0.99      | m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) != iProver_top ),
% 3.33/0.99      inference(superposition,[status(thm)],[c_1563,c_2430]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2458,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK1)
% 3.33/0.99      | v2_tex_2(sK4,sK2)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.33/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2440]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1007,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1) | v2_tex_2(X2,X1) | X2 != X0 ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1763,plain,
% 3.33/0.99      ( v2_tex_2(X0,sK1) | ~ v2_tex_2(sK3,sK1) | X0 != sK3 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1007]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2202,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK3,sK1) | v2_tex_2(sK4,sK1) | sK4 != sK3 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1763]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2206,plain,
% 3.33/0.99      ( sK4 != sK3
% 3.33/0.99      | v2_tex_2(sK3,sK1) != iProver_top
% 3.33/0.99      | v2_tex_2(sK4,sK1) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_2202]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_996,plain,( X0 = X0 ),theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1976,plain,
% 3.33/0.99      ( sK4 = sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_996]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1784,plain,
% 3.33/0.99      ( X0 != X1 | X0 = sK3 | sK3 != X1 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_997]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1841,plain,
% 3.33/0.99      ( X0 = sK3 | X0 != sK4 | sK3 != sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1784]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1975,plain,
% 3.33/0.99      ( sK3 != sK4 | sK4 = sK3 | sK4 != sK4 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1841]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1696,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK1))) ),
% 3.33/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1563]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_18,negated_conjecture,
% 3.33/0.99      ( v3_tex_2(sK3,sK1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1533,plain,
% 3.33/0.99      ( v3_tex_2(sK3,sK1) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1556,plain,
% 3.33/0.99      ( v3_tex_2(sK4,sK1) = iProver_top ),
% 3.33/0.99      inference(light_normalisation,[status(thm)],[c_1533,c_19]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1687,plain,
% 3.33/0.99      ( v3_tex_2(sK4,sK1) ),
% 3.33/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1556]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1002,plain,
% 3.33/0.99      ( X0 != X1 | u1_struct_0(X0) = u1_struct_0(X1) ),
% 3.33/0.99      theory(equality) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_1012,plain,
% 3.33/0.99      ( u1_struct_0(sK1) = u1_struct_0(sK1) | sK1 != sK1 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_1002]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_15,plain,
% 3.33/0.99      ( v2_tex_2(X0,X1)
% 3.33/0.99      | ~ v3_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_465,plain,
% 3.33/0.99      ( v2_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK1 != X1
% 3.33/0.99      | sK3 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_18]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_466,plain,
% 3.33/0.99      ( v2_tex_2(sK3,sK1)
% 3.33/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
% 3.33/0.99      | ~ l1_pre_topc(sK1) ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_465]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_467,plain,
% 3.33/0.99      ( v2_tex_2(sK3,sK1) = iProver_top
% 3.33/0.99      | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) != iProver_top
% 3.33/0.99      | l1_pre_topc(sK1) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_10,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v3_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK0(X1,X0) != X0 ),
% 3.33/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_17,negated_conjecture,
% 3.33/0.99      ( ~ v3_tex_2(sK4,sK2) ),
% 3.33/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_451,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK0(X1,X0) != X0
% 3.33/0.99      | sK2 != X1
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_17]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_452,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ l1_pre_topc(sK2)
% 3.33/0.99      | sK0(sK2,sK4) != sK4 ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_451]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_21,negated_conjecture,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_454,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2) | sK0(sK2,sK4) != sK4 ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_452,c_23,c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_456,plain,
% 3.33/0.99      ( sK0(sK2,sK4) != sK4 | v2_tex_2(sK4,sK2) != iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_454]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_11,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v3_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | r1_tarski(X0,sK0(X1,X0))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_437,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | r1_tarski(X0,sK0(X1,X0))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK2 != X1
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_17]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_438,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | r1_tarski(sK4,sK0(sK2,sK4))
% 3.33/0.99      | ~ l1_pre_topc(sK2) ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_440,plain,
% 3.33/0.99      ( r1_tarski(sK4,sK0(sK2,sK4)) | ~ v2_tex_2(sK4,sK2) ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_438,c_23,c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_441,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2) | r1_tarski(sK4,sK0(sK2,sK4)) ),
% 3.33/0.99      inference(renaming,[status(thm)],[c_440]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_12,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v2_tex_2(sK0(X1,X0),X1)
% 3.33/0.99      | v3_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_423,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v2_tex_2(sK0(X1,X0),X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK2 != X1
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_17]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_424,plain,
% 3.33/0.99      ( v2_tex_2(sK0(sK2,sK4),sK2)
% 3.33/0.99      | ~ v2_tex_2(sK4,sK2)
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ l1_pre_topc(sK2) ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_423]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_426,plain,
% 3.33/0.99      ( v2_tex_2(sK0(sK2,sK4),sK2) | ~ v2_tex_2(sK4,sK2) ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_424,c_23,c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_13,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | v3_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1) ),
% 3.33/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_409,plain,
% 3.33/0.99      ( ~ v2_tex_2(X0,X1)
% 3.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | m1_subset_1(sK0(X1,X0),k1_zfmisc_1(u1_struct_0(X1)))
% 3.33/0.99      | ~ l1_pre_topc(X1)
% 3.33/0.99      | sK2 != X1
% 3.33/0.99      | sK4 != X0 ),
% 3.33/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_17]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_410,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2)
% 3.33/0.99      | m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2)))
% 3.33/0.99      | ~ l1_pre_topc(sK2) ),
% 3.33/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_412,plain,
% 3.33/0.99      ( ~ v2_tex_2(sK4,sK2)
% 3.33/0.99      | m1_subset_1(sK0(sK2,sK4),k1_zfmisc_1(u1_struct_0(sK2))) ),
% 3.33/0.99      inference(global_propositional_subsumption,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_410,c_23,c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_72,plain,
% 3.33/0.99      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_2,plain,
% 3.33/0.99      ( r1_tarski(X0,X0) ),
% 3.33/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_68,plain,
% 3.33/0.99      ( r1_tarski(sK1,sK1) ),
% 3.33/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_28,plain,
% 3.33/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(u1_struct_0(sK2))) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(c_27,plain,
% 3.33/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) = iProver_top ),
% 3.33/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.33/0.99  
% 3.33/0.99  cnf(contradiction,plain,
% 3.33/0.99      ( $false ),
% 3.33/0.99      inference(minisat,
% 3.33/0.99                [status(thm)],
% 3.33/0.99                [c_8462,c_6889,c_6313,c_6216,c_5765,c_4185,c_4138,c_3738,
% 3.33/0.99                 c_2458,c_2440,c_2206,c_2202,c_1976,c_1975,c_1696,c_1687,
% 3.33/0.99                 c_1012,c_467,c_466,c_456,c_441,c_426,c_412,c_72,c_68,
% 3.33/0.99                 c_19,c_20,c_28,c_21,c_27,c_22,c_26,c_23,c_25,c_24]) ).
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.33/0.99  
% 3.33/0.99  ------                               Statistics
% 3.33/0.99  
% 3.33/0.99  ------ General
% 3.33/0.99  
% 3.33/0.99  abstr_ref_over_cycles:                  0
% 3.33/0.99  abstr_ref_under_cycles:                 0
% 3.33/0.99  gc_basic_clause_elim:                   0
% 3.33/0.99  forced_gc_time:                         0
% 3.33/0.99  parsing_time:                           0.008
% 3.33/0.99  unif_index_cands_time:                  0.
% 3.33/0.99  unif_index_add_time:                    0.
% 3.33/0.99  orderings_time:                         0.
% 3.33/0.99  out_proof_time:                         0.011
% 3.33/0.99  total_time:                             0.233
% 3.33/0.99  num_of_symbols:                         46
% 3.33/0.99  num_of_terms:                           3486
% 3.33/0.99  
% 3.33/0.99  ------ Preprocessing
% 3.33/0.99  
% 3.33/0.99  num_of_splits:                          0
% 3.33/0.99  num_of_split_atoms:                     0
% 3.33/0.99  num_of_reused_defs:                     0
% 3.33/0.99  num_eq_ax_congr_red:                    15
% 3.33/0.99  num_of_sem_filtered_clauses:            1
% 3.33/0.99  num_of_subtypes:                        0
% 3.33/0.99  monotx_restored_types:                  0
% 3.33/0.99  sat_num_of_epr_types:                   0
% 3.33/0.99  sat_num_of_non_cyclic_types:            0
% 3.33/0.99  sat_guarded_non_collapsed_types:        0
% 3.33/0.99  num_pure_diseq_elim:                    0
% 3.33/0.99  simp_replaced_by:                       0
% 3.33/0.99  res_preprocessed:                       117
% 3.33/0.99  prep_upred:                             0
% 3.33/0.99  prep_unflattend:                        40
% 3.33/0.99  smt_new_axioms:                         0
% 3.33/0.99  pred_elim_cands:                        6
% 3.33/0.99  pred_elim:                              0
% 3.33/0.99  pred_elim_cl:                           0
% 3.33/0.99  pred_elim_cycles:                       2
% 3.33/0.99  merged_defs:                            8
% 3.33/0.99  merged_defs_ncl:                        0
% 3.33/0.99  bin_hyper_res:                          8
% 3.33/0.99  prep_cycles:                            4
% 3.33/0.99  pred_elim_time:                         0.009
% 3.33/0.99  splitting_time:                         0.
% 3.33/0.99  sem_filter_time:                        0.
% 3.33/0.99  monotx_time:                            0.
% 3.33/0.99  subtype_inf_time:                       0.
% 3.33/0.99  
% 3.33/0.99  ------ Problem properties
% 3.33/0.99  
% 3.33/0.99  clauses:                                23
% 3.33/0.99  conjectures:                            8
% 3.33/0.99  epr:                                    8
% 3.33/0.99  horn:                                   20
% 3.33/0.99  ground:                                 8
% 3.33/0.99  unary:                                  9
% 3.33/0.99  binary:                                 3
% 3.33/0.99  lits:                                   66
% 3.33/0.99  lits_eq:                                6
% 3.33/0.99  fd_pure:                                0
% 3.33/0.99  fd_pseudo:                              0
% 3.33/0.99  fd_cond:                                0
% 3.33/0.99  fd_pseudo_cond:                         2
% 3.33/0.99  ac_symbols:                             0
% 3.33/0.99  
% 3.33/0.99  ------ Propositional Solver
% 3.33/0.99  
% 3.33/0.99  prop_solver_calls:                      33
% 3.33/0.99  prop_fast_solver_calls:                 1471
% 3.33/0.99  smt_solver_calls:                       0
% 3.33/0.99  smt_fast_solver_calls:                  0
% 3.33/0.99  prop_num_of_clauses:                    2050
% 3.33/0.99  prop_preprocess_simplified:             6290
% 3.33/0.99  prop_fo_subsumed:                       82
% 3.33/0.99  prop_solver_time:                       0.
% 3.33/0.99  smt_solver_time:                        0.
% 3.33/0.99  smt_fast_solver_time:                   0.
% 3.33/0.99  prop_fast_solver_time:                  0.
% 3.33/0.99  prop_unsat_core_time:                   0.
% 3.33/0.99  
% 3.33/0.99  ------ QBF
% 3.33/0.99  
% 3.33/0.99  qbf_q_res:                              0
% 3.33/0.99  qbf_num_tautologies:                    0
% 3.33/0.99  qbf_prep_cycles:                        0
% 3.33/0.99  
% 3.33/0.99  ------ BMC1
% 3.33/0.99  
% 3.33/0.99  bmc1_current_bound:                     -1
% 3.33/0.99  bmc1_last_solved_bound:                 -1
% 3.33/0.99  bmc1_unsat_core_size:                   -1
% 3.33/0.99  bmc1_unsat_core_parents_size:           -1
% 3.33/0.99  bmc1_merge_next_fun:                    0
% 3.33/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.33/0.99  
% 3.33/0.99  ------ Instantiation
% 3.33/0.99  
% 3.33/0.99  inst_num_of_clauses:                    634
% 3.33/0.99  inst_num_in_passive:                    90
% 3.33/0.99  inst_num_in_active:                     512
% 3.33/0.99  inst_num_in_unprocessed:                33
% 3.33/0.99  inst_num_of_loops:                      530
% 3.33/0.99  inst_num_of_learning_restarts:          0
% 3.33/0.99  inst_num_moves_active_passive:          11
% 3.33/0.99  inst_lit_activity:                      0
% 3.33/0.99  inst_lit_activity_moves:                0
% 3.33/0.99  inst_num_tautologies:                   0
% 3.33/0.99  inst_num_prop_implied:                  0
% 3.33/0.99  inst_num_existing_simplified:           0
% 3.33/0.99  inst_num_eq_res_simplified:             0
% 3.33/0.99  inst_num_child_elim:                    0
% 3.33/0.99  inst_num_of_dismatching_blockings:      585
% 3.33/0.99  inst_num_of_non_proper_insts:           1703
% 3.33/0.99  inst_num_of_duplicates:                 0
% 3.33/0.99  inst_inst_num_from_inst_to_res:         0
% 3.33/0.99  inst_dismatching_checking_time:         0.
% 3.33/0.99  
% 3.33/0.99  ------ Resolution
% 3.33/0.99  
% 3.33/0.99  res_num_of_clauses:                     0
% 3.33/0.99  res_num_in_passive:                     0
% 3.33/0.99  res_num_in_active:                      0
% 3.33/0.99  res_num_of_loops:                       121
% 3.33/0.99  res_forward_subset_subsumed:            228
% 3.33/0.99  res_backward_subset_subsumed:           6
% 3.33/0.99  res_forward_subsumed:                   0
% 3.33/0.99  res_backward_subsumed:                  0
% 3.33/0.99  res_forward_subsumption_resolution:     0
% 3.33/0.99  res_backward_subsumption_resolution:    0
% 3.33/0.99  res_clause_to_clause_subsumption:       789
% 3.33/0.99  res_orphan_elimination:                 0
% 3.33/0.99  res_tautology_del:                      280
% 3.33/0.99  res_num_eq_res_simplified:              0
% 3.33/0.99  res_num_sel_changes:                    0
% 3.33/0.99  res_moves_from_active_to_pass:          0
% 3.33/0.99  
% 3.33/0.99  ------ Superposition
% 3.33/0.99  
% 3.33/0.99  sup_time_total:                         0.
% 3.33/0.99  sup_time_generating:                    0.
% 3.33/0.99  sup_time_sim_full:                      0.
% 3.33/0.99  sup_time_sim_immed:                     0.
% 3.33/0.99  
% 3.33/0.99  sup_num_of_clauses:                     123
% 3.33/0.99  sup_num_in_active:                      106
% 3.33/0.99  sup_num_in_passive:                     17
% 3.33/0.99  sup_num_of_loops:                       105
% 3.33/0.99  sup_fw_superposition:                   130
% 3.33/0.99  sup_bw_superposition:                   39
% 3.33/0.99  sup_immediate_simplified:               35
% 3.33/0.99  sup_given_eliminated:                   0
% 3.33/0.99  comparisons_done:                       0
% 3.33/0.99  comparisons_avoided:                    0
% 3.33/0.99  
% 3.33/0.99  ------ Simplifications
% 3.33/0.99  
% 3.33/0.99  
% 3.33/0.99  sim_fw_subset_subsumed:                 22
% 3.33/0.99  sim_bw_subset_subsumed:                 0
% 3.33/0.99  sim_fw_subsumed:                        13
% 3.33/0.99  sim_bw_subsumed:                        2
% 3.33/0.99  sim_fw_subsumption_res:                 0
% 3.33/0.99  sim_bw_subsumption_res:                 0
% 3.33/0.99  sim_tautology_del:                      6
% 3.33/0.99  sim_eq_tautology_del:                   8
% 3.33/0.99  sim_eq_res_simp:                        0
% 3.33/0.99  sim_fw_demodulated:                     0
% 3.33/0.99  sim_bw_demodulated:                     0
% 3.33/0.99  sim_light_normalised:                   4
% 3.33/0.99  sim_joinable_taut:                      0
% 3.33/0.99  sim_joinable_simp:                      0
% 3.33/0.99  sim_ac_normalised:                      0
% 3.33/0.99  sim_smt_subsumption:                    0
% 3.33/0.99  
%------------------------------------------------------------------------------
