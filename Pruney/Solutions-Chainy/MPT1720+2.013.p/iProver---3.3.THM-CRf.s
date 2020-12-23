%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:09 EST 2020

% Result     : Theorem 19.85s
% Output     : CNFRefutation 19.85s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 427 expanded)
%              Number of clauses        :   75 ( 106 expanded)
%              Number of leaves         :   12 ( 146 expanded)
%              Depth                    :   18
%              Number of atoms          :  574 (4144 expanded)
%              Number of equality atoms :   92 ( 119 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   24 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X2)
      | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
          & m1_pre_topc(X3,X2)
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ~ m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2)
        & m1_pre_topc(sK3,X2)
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2)
            & m1_pre_topc(X3,sK2)
            & m1_pre_topc(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    & m1_pre_topc(sK3,sK2)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24,f23,f22])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f41,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f47,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f44,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_21,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_315,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,X2)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_21])).

cnf(c_316,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ l1_pre_topc(sK0) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_20,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_318,plain,
    ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_316,c_20])).

cnf(c_319,plain,
    ( m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
    inference(renaming,[status(thm)],[c_318])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f27])).

cnf(c_164,plain,
    ( r1_tarski(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_8,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_292,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(X2,X3)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X0) != X2
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X3) ),
    inference(resolution_lifted,[status(thm)],[c_164,c_8])).

cnf(c_293,plain,
    ( ~ m1_pre_topc(X0,X1)
    | r1_tarski(u1_struct_0(X0),X2)
    | ~ l1_pre_topc(X1)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_292])).

cnf(c_370,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X3,sK0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X3) != X4
    | u1_struct_0(X2) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X4) ),
    inference(resolution_lifted,[status(thm)],[c_319,c_293])).

cnf(c_371,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X3,sK0)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(X2) != u1_struct_0(X0)
    | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X3)) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_630,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(X2_43,X3_43)
    | ~ m1_pre_topc(X2_43,sK0)
    | ~ m1_pre_topc(X3_43,sK0)
    | ~ l1_pre_topc(X1_43)
    | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(X3_43))
    | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
    inference(subtyping,[status(esa)],[c_371])).

cnf(c_2594,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X2_43)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ l1_pre_topc(X1_43)
    | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(X2_43))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_17914,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(X1_43)
    | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_2594])).

cnf(c_52224,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
    inference(instantiation,[status(thm)],[c_17914])).

cnf(c_72007,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK2)
    | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(instantiation,[status(thm)],[c_52224])).

cnf(c_651,plain,
    ( X0_45 = X0_45 ),
    theory(equality)).

cnf(c_17769,plain,
    ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_14,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_639,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_991,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_635,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_995,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_7,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v1_pre_topc(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_129,plain,
    ( ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_7,c_6,c_5])).

cnf(c_130,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
    inference(renaming,[status(thm)],[c_129])).

cnf(c_631,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43)
    | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
    inference(subtyping,[status(esa)],[c_130])).

cnf(c_999,plain,
    ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_2863,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_995,c_999])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_23,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_26,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3906,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2863,c_23,c_25,c_26])).

cnf(c_3907,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_3906])).

cnf(c_3915,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_991,c_3907])).

cnf(c_12,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_641,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_989,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_13,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_640,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_990,plain,
    ( m1_pre_topc(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_640])).

cnf(c_2860,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_999])).

cnf(c_17,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_28,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_16,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_29,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_647,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1312,plain,
    ( ~ m1_pre_topc(sK2,X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_647])).

cnf(c_1313,plain,
    ( m1_pre_topc(sK2,X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1312])).

cnf(c_1315,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | l1_pre_topc(sK2) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1313])).

cnf(c_3055,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2860,c_25,c_26,c_28,c_29,c_1315])).

cnf(c_3056,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
    | m1_pre_topc(X0_43,sK2) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_3055])).

cnf(c_3064,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_3056])).

cnf(c_15,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_30,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3097,plain,
    ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3064,c_30])).

cnf(c_3946,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
    | v2_struct_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3915,c_3097])).

cnf(c_645,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X2_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1269,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1474,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_1254,plain,
    ( ~ m1_pre_topc(X0_43,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,sK1,X0_43),sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_645])).

cnf(c_1439,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK1,sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK2) ),
    inference(instantiation,[status(thm)],[c_1254])).

cnf(c_1314,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1312])).

cnf(c_11,negated_conjecture,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_72007,c_17769,c_3946,c_1474,c_1439,c_1314,c_11,c_12,c_13,c_14,c_30,c_15,c_16,c_17,c_18,c_19,c_20,c_22])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 20:29:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 19.85/2.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 19.85/2.99  
% 19.85/2.99  ------  iProver source info
% 19.85/2.99  
% 19.85/2.99  git: date: 2020-06-30 10:37:57 +0100
% 19.85/2.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 19.85/2.99  git: non_committed_changes: false
% 19.85/2.99  git: last_make_outside_of_git: false
% 19.85/2.99  
% 19.85/2.99  ------ 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options
% 19.85/2.99  
% 19.85/2.99  --out_options                           all
% 19.85/2.99  --tptp_safe_out                         true
% 19.85/2.99  --problem_path                          ""
% 19.85/2.99  --include_path                          ""
% 19.85/2.99  --clausifier                            res/vclausify_rel
% 19.85/2.99  --clausifier_options                    --mode clausify
% 19.85/2.99  --stdin                                 false
% 19.85/2.99  --stats_out                             all
% 19.85/2.99  
% 19.85/2.99  ------ General Options
% 19.85/2.99  
% 19.85/2.99  --fof                                   false
% 19.85/2.99  --time_out_real                         305.
% 19.85/2.99  --time_out_virtual                      -1.
% 19.85/2.99  --symbol_type_check                     false
% 19.85/2.99  --clausify_out                          false
% 19.85/2.99  --sig_cnt_out                           false
% 19.85/2.99  --trig_cnt_out                          false
% 19.85/2.99  --trig_cnt_out_tolerance                1.
% 19.85/2.99  --trig_cnt_out_sk_spl                   false
% 19.85/2.99  --abstr_cl_out                          false
% 19.85/2.99  
% 19.85/2.99  ------ Global Options
% 19.85/2.99  
% 19.85/2.99  --schedule                              default
% 19.85/2.99  --add_important_lit                     false
% 19.85/2.99  --prop_solver_per_cl                    1000
% 19.85/2.99  --min_unsat_core                        false
% 19.85/2.99  --soft_assumptions                      false
% 19.85/2.99  --soft_lemma_size                       3
% 19.85/2.99  --prop_impl_unit_size                   0
% 19.85/2.99  --prop_impl_unit                        []
% 19.85/2.99  --share_sel_clauses                     true
% 19.85/2.99  --reset_solvers                         false
% 19.85/2.99  --bc_imp_inh                            [conj_cone]
% 19.85/2.99  --conj_cone_tolerance                   3.
% 19.85/2.99  --extra_neg_conj                        none
% 19.85/2.99  --large_theory_mode                     true
% 19.85/2.99  --prolific_symb_bound                   200
% 19.85/2.99  --lt_threshold                          2000
% 19.85/2.99  --clause_weak_htbl                      true
% 19.85/2.99  --gc_record_bc_elim                     false
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing Options
% 19.85/2.99  
% 19.85/2.99  --preprocessing_flag                    true
% 19.85/2.99  --time_out_prep_mult                    0.1
% 19.85/2.99  --splitting_mode                        input
% 19.85/2.99  --splitting_grd                         true
% 19.85/2.99  --splitting_cvd                         false
% 19.85/2.99  --splitting_cvd_svl                     false
% 19.85/2.99  --splitting_nvd                         32
% 19.85/2.99  --sub_typing                            true
% 19.85/2.99  --prep_gs_sim                           true
% 19.85/2.99  --prep_unflatten                        true
% 19.85/2.99  --prep_res_sim                          true
% 19.85/2.99  --prep_upred                            true
% 19.85/2.99  --prep_sem_filter                       exhaustive
% 19.85/2.99  --prep_sem_filter_out                   false
% 19.85/2.99  --pred_elim                             true
% 19.85/2.99  --res_sim_input                         true
% 19.85/2.99  --eq_ax_congr_red                       true
% 19.85/2.99  --pure_diseq_elim                       true
% 19.85/2.99  --brand_transform                       false
% 19.85/2.99  --non_eq_to_eq                          false
% 19.85/2.99  --prep_def_merge                        true
% 19.85/2.99  --prep_def_merge_prop_impl              false
% 19.85/2.99  --prep_def_merge_mbd                    true
% 19.85/2.99  --prep_def_merge_tr_red                 false
% 19.85/2.99  --prep_def_merge_tr_cl                  false
% 19.85/2.99  --smt_preprocessing                     true
% 19.85/2.99  --smt_ac_axioms                         fast
% 19.85/2.99  --preprocessed_out                      false
% 19.85/2.99  --preprocessed_stats                    false
% 19.85/2.99  
% 19.85/2.99  ------ Abstraction refinement Options
% 19.85/2.99  
% 19.85/2.99  --abstr_ref                             []
% 19.85/2.99  --abstr_ref_prep                        false
% 19.85/2.99  --abstr_ref_until_sat                   false
% 19.85/2.99  --abstr_ref_sig_restrict                funpre
% 19.85/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.85/2.99  --abstr_ref_under                       []
% 19.85/2.99  
% 19.85/2.99  ------ SAT Options
% 19.85/2.99  
% 19.85/2.99  --sat_mode                              false
% 19.85/2.99  --sat_fm_restart_options                ""
% 19.85/2.99  --sat_gr_def                            false
% 19.85/2.99  --sat_epr_types                         true
% 19.85/2.99  --sat_non_cyclic_types                  false
% 19.85/2.99  --sat_finite_models                     false
% 19.85/2.99  --sat_fm_lemmas                         false
% 19.85/2.99  --sat_fm_prep                           false
% 19.85/2.99  --sat_fm_uc_incr                        true
% 19.85/2.99  --sat_out_model                         small
% 19.85/2.99  --sat_out_clauses                       false
% 19.85/2.99  
% 19.85/2.99  ------ QBF Options
% 19.85/2.99  
% 19.85/2.99  --qbf_mode                              false
% 19.85/2.99  --qbf_elim_univ                         false
% 19.85/2.99  --qbf_dom_inst                          none
% 19.85/2.99  --qbf_dom_pre_inst                      false
% 19.85/2.99  --qbf_sk_in                             false
% 19.85/2.99  --qbf_pred_elim                         true
% 19.85/2.99  --qbf_split                             512
% 19.85/2.99  
% 19.85/2.99  ------ BMC1 Options
% 19.85/2.99  
% 19.85/2.99  --bmc1_incremental                      false
% 19.85/2.99  --bmc1_axioms                           reachable_all
% 19.85/2.99  --bmc1_min_bound                        0
% 19.85/2.99  --bmc1_max_bound                        -1
% 19.85/2.99  --bmc1_max_bound_default                -1
% 19.85/2.99  --bmc1_symbol_reachability              true
% 19.85/2.99  --bmc1_property_lemmas                  false
% 19.85/2.99  --bmc1_k_induction                      false
% 19.85/2.99  --bmc1_non_equiv_states                 false
% 19.85/2.99  --bmc1_deadlock                         false
% 19.85/2.99  --bmc1_ucm                              false
% 19.85/2.99  --bmc1_add_unsat_core                   none
% 19.85/2.99  --bmc1_unsat_core_children              false
% 19.85/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.85/2.99  --bmc1_out_stat                         full
% 19.85/2.99  --bmc1_ground_init                      false
% 19.85/2.99  --bmc1_pre_inst_next_state              false
% 19.85/2.99  --bmc1_pre_inst_state                   false
% 19.85/2.99  --bmc1_pre_inst_reach_state             false
% 19.85/2.99  --bmc1_out_unsat_core                   false
% 19.85/2.99  --bmc1_aig_witness_out                  false
% 19.85/2.99  --bmc1_verbose                          false
% 19.85/2.99  --bmc1_dump_clauses_tptp                false
% 19.85/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.85/2.99  --bmc1_dump_file                        -
% 19.85/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.85/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.85/2.99  --bmc1_ucm_extend_mode                  1
% 19.85/2.99  --bmc1_ucm_init_mode                    2
% 19.85/2.99  --bmc1_ucm_cone_mode                    none
% 19.85/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.85/2.99  --bmc1_ucm_relax_model                  4
% 19.85/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.85/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.85/2.99  --bmc1_ucm_layered_model                none
% 19.85/2.99  --bmc1_ucm_max_lemma_size               10
% 19.85/2.99  
% 19.85/2.99  ------ AIG Options
% 19.85/2.99  
% 19.85/2.99  --aig_mode                              false
% 19.85/2.99  
% 19.85/2.99  ------ Instantiation Options
% 19.85/2.99  
% 19.85/2.99  --instantiation_flag                    true
% 19.85/2.99  --inst_sos_flag                         false
% 19.85/2.99  --inst_sos_phase                        true
% 19.85/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel_side                     num_symb
% 19.85/2.99  --inst_solver_per_active                1400
% 19.85/2.99  --inst_solver_calls_frac                1.
% 19.85/2.99  --inst_passive_queue_type               priority_queues
% 19.85/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.85/2.99  --inst_passive_queues_freq              [25;2]
% 19.85/2.99  --inst_dismatching                      true
% 19.85/2.99  --inst_eager_unprocessed_to_passive     true
% 19.85/2.99  --inst_prop_sim_given                   true
% 19.85/2.99  --inst_prop_sim_new                     false
% 19.85/2.99  --inst_subs_new                         false
% 19.85/2.99  --inst_eq_res_simp                      false
% 19.85/2.99  --inst_subs_given                       false
% 19.85/2.99  --inst_orphan_elimination               true
% 19.85/2.99  --inst_learning_loop_flag               true
% 19.85/2.99  --inst_learning_start                   3000
% 19.85/2.99  --inst_learning_factor                  2
% 19.85/2.99  --inst_start_prop_sim_after_learn       3
% 19.85/2.99  --inst_sel_renew                        solver
% 19.85/2.99  --inst_lit_activity_flag                true
% 19.85/2.99  --inst_restr_to_given                   false
% 19.85/2.99  --inst_activity_threshold               500
% 19.85/2.99  --inst_out_proof                        true
% 19.85/2.99  
% 19.85/2.99  ------ Resolution Options
% 19.85/2.99  
% 19.85/2.99  --resolution_flag                       true
% 19.85/2.99  --res_lit_sel                           adaptive
% 19.85/2.99  --res_lit_sel_side                      none
% 19.85/2.99  --res_ordering                          kbo
% 19.85/2.99  --res_to_prop_solver                    active
% 19.85/2.99  --res_prop_simpl_new                    false
% 19.85/2.99  --res_prop_simpl_given                  true
% 19.85/2.99  --res_passive_queue_type                priority_queues
% 19.85/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.85/2.99  --res_passive_queues_freq               [15;5]
% 19.85/2.99  --res_forward_subs                      full
% 19.85/2.99  --res_backward_subs                     full
% 19.85/2.99  --res_forward_subs_resolution           true
% 19.85/2.99  --res_backward_subs_resolution          true
% 19.85/2.99  --res_orphan_elimination                true
% 19.85/2.99  --res_time_limit                        2.
% 19.85/2.99  --res_out_proof                         true
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Options
% 19.85/2.99  
% 19.85/2.99  --superposition_flag                    true
% 19.85/2.99  --sup_passive_queue_type                priority_queues
% 19.85/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.85/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.85/2.99  --demod_completeness_check              fast
% 19.85/2.99  --demod_use_ground                      true
% 19.85/2.99  --sup_to_prop_solver                    passive
% 19.85/2.99  --sup_prop_simpl_new                    true
% 19.85/2.99  --sup_prop_simpl_given                  true
% 19.85/2.99  --sup_fun_splitting                     false
% 19.85/2.99  --sup_smt_interval                      50000
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Simplification Setup
% 19.85/2.99  
% 19.85/2.99  --sup_indices_passive                   []
% 19.85/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.85/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_full_bw                           [BwDemod]
% 19.85/2.99  --sup_immed_triv                        [TrivRules]
% 19.85/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_immed_bw_main                     []
% 19.85/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.85/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.85/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.85/2.99  
% 19.85/2.99  ------ Combination Options
% 19.85/2.99  
% 19.85/2.99  --comb_res_mult                         3
% 19.85/2.99  --comb_sup_mult                         2
% 19.85/2.99  --comb_inst_mult                        10
% 19.85/2.99  
% 19.85/2.99  ------ Debug Options
% 19.85/2.99  
% 19.85/2.99  --dbg_backtrace                         false
% 19.85/2.99  --dbg_dump_prop_clauses                 false
% 19.85/2.99  --dbg_dump_prop_clauses_file            -
% 19.85/2.99  --dbg_out_stat                          false
% 19.85/2.99  ------ Parsing...
% 19.85/2.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 19.85/2.99  ------ Proving...
% 19.85/2.99  ------ Problem Properties 
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  clauses                                 18
% 19.85/2.99  conjectures                             11
% 19.85/2.99  EPR                                     11
% 19.85/2.99  Horn                                    13
% 19.85/2.99  unary                                   11
% 19.85/2.99  binary                                  0
% 19.85/2.99  lits                                    60
% 19.85/2.99  lits eq                                 5
% 19.85/2.99  fd_pure                                 0
% 19.85/2.99  fd_pseudo                               0
% 19.85/2.99  fd_cond                                 0
% 19.85/2.99  fd_pseudo_cond                          1
% 19.85/2.99  AC symbols                              0
% 19.85/2.99  
% 19.85/2.99  ------ Schedule dynamic 5 is on 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  ------ 
% 19.85/2.99  Current options:
% 19.85/2.99  ------ 
% 19.85/2.99  
% 19.85/2.99  ------ Input Options
% 19.85/2.99  
% 19.85/2.99  --out_options                           all
% 19.85/2.99  --tptp_safe_out                         true
% 19.85/2.99  --problem_path                          ""
% 19.85/2.99  --include_path                          ""
% 19.85/2.99  --clausifier                            res/vclausify_rel
% 19.85/2.99  --clausifier_options                    --mode clausify
% 19.85/2.99  --stdin                                 false
% 19.85/2.99  --stats_out                             all
% 19.85/2.99  
% 19.85/2.99  ------ General Options
% 19.85/2.99  
% 19.85/2.99  --fof                                   false
% 19.85/2.99  --time_out_real                         305.
% 19.85/2.99  --time_out_virtual                      -1.
% 19.85/2.99  --symbol_type_check                     false
% 19.85/2.99  --clausify_out                          false
% 19.85/2.99  --sig_cnt_out                           false
% 19.85/2.99  --trig_cnt_out                          false
% 19.85/2.99  --trig_cnt_out_tolerance                1.
% 19.85/2.99  --trig_cnt_out_sk_spl                   false
% 19.85/2.99  --abstr_cl_out                          false
% 19.85/2.99  
% 19.85/2.99  ------ Global Options
% 19.85/2.99  
% 19.85/2.99  --schedule                              default
% 19.85/2.99  --add_important_lit                     false
% 19.85/2.99  --prop_solver_per_cl                    1000
% 19.85/2.99  --min_unsat_core                        false
% 19.85/2.99  --soft_assumptions                      false
% 19.85/2.99  --soft_lemma_size                       3
% 19.85/2.99  --prop_impl_unit_size                   0
% 19.85/2.99  --prop_impl_unit                        []
% 19.85/2.99  --share_sel_clauses                     true
% 19.85/2.99  --reset_solvers                         false
% 19.85/2.99  --bc_imp_inh                            [conj_cone]
% 19.85/2.99  --conj_cone_tolerance                   3.
% 19.85/2.99  --extra_neg_conj                        none
% 19.85/2.99  --large_theory_mode                     true
% 19.85/2.99  --prolific_symb_bound                   200
% 19.85/2.99  --lt_threshold                          2000
% 19.85/2.99  --clause_weak_htbl                      true
% 19.85/2.99  --gc_record_bc_elim                     false
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing Options
% 19.85/2.99  
% 19.85/2.99  --preprocessing_flag                    true
% 19.85/2.99  --time_out_prep_mult                    0.1
% 19.85/2.99  --splitting_mode                        input
% 19.85/2.99  --splitting_grd                         true
% 19.85/2.99  --splitting_cvd                         false
% 19.85/2.99  --splitting_cvd_svl                     false
% 19.85/2.99  --splitting_nvd                         32
% 19.85/2.99  --sub_typing                            true
% 19.85/2.99  --prep_gs_sim                           true
% 19.85/2.99  --prep_unflatten                        true
% 19.85/2.99  --prep_res_sim                          true
% 19.85/2.99  --prep_upred                            true
% 19.85/2.99  --prep_sem_filter                       exhaustive
% 19.85/2.99  --prep_sem_filter_out                   false
% 19.85/2.99  --pred_elim                             true
% 19.85/2.99  --res_sim_input                         true
% 19.85/2.99  --eq_ax_congr_red                       true
% 19.85/2.99  --pure_diseq_elim                       true
% 19.85/2.99  --brand_transform                       false
% 19.85/2.99  --non_eq_to_eq                          false
% 19.85/2.99  --prep_def_merge                        true
% 19.85/2.99  --prep_def_merge_prop_impl              false
% 19.85/2.99  --prep_def_merge_mbd                    true
% 19.85/2.99  --prep_def_merge_tr_red                 false
% 19.85/2.99  --prep_def_merge_tr_cl                  false
% 19.85/2.99  --smt_preprocessing                     true
% 19.85/2.99  --smt_ac_axioms                         fast
% 19.85/2.99  --preprocessed_out                      false
% 19.85/2.99  --preprocessed_stats                    false
% 19.85/2.99  
% 19.85/2.99  ------ Abstraction refinement Options
% 19.85/2.99  
% 19.85/2.99  --abstr_ref                             []
% 19.85/2.99  --abstr_ref_prep                        false
% 19.85/2.99  --abstr_ref_until_sat                   false
% 19.85/2.99  --abstr_ref_sig_restrict                funpre
% 19.85/2.99  --abstr_ref_af_restrict_to_split_sk     false
% 19.85/2.99  --abstr_ref_under                       []
% 19.85/2.99  
% 19.85/2.99  ------ SAT Options
% 19.85/2.99  
% 19.85/2.99  --sat_mode                              false
% 19.85/2.99  --sat_fm_restart_options                ""
% 19.85/2.99  --sat_gr_def                            false
% 19.85/2.99  --sat_epr_types                         true
% 19.85/2.99  --sat_non_cyclic_types                  false
% 19.85/2.99  --sat_finite_models                     false
% 19.85/2.99  --sat_fm_lemmas                         false
% 19.85/2.99  --sat_fm_prep                           false
% 19.85/2.99  --sat_fm_uc_incr                        true
% 19.85/2.99  --sat_out_model                         small
% 19.85/2.99  --sat_out_clauses                       false
% 19.85/2.99  
% 19.85/2.99  ------ QBF Options
% 19.85/2.99  
% 19.85/2.99  --qbf_mode                              false
% 19.85/2.99  --qbf_elim_univ                         false
% 19.85/2.99  --qbf_dom_inst                          none
% 19.85/2.99  --qbf_dom_pre_inst                      false
% 19.85/2.99  --qbf_sk_in                             false
% 19.85/2.99  --qbf_pred_elim                         true
% 19.85/2.99  --qbf_split                             512
% 19.85/2.99  
% 19.85/2.99  ------ BMC1 Options
% 19.85/2.99  
% 19.85/2.99  --bmc1_incremental                      false
% 19.85/2.99  --bmc1_axioms                           reachable_all
% 19.85/2.99  --bmc1_min_bound                        0
% 19.85/2.99  --bmc1_max_bound                        -1
% 19.85/2.99  --bmc1_max_bound_default                -1
% 19.85/2.99  --bmc1_symbol_reachability              true
% 19.85/2.99  --bmc1_property_lemmas                  false
% 19.85/2.99  --bmc1_k_induction                      false
% 19.85/2.99  --bmc1_non_equiv_states                 false
% 19.85/2.99  --bmc1_deadlock                         false
% 19.85/2.99  --bmc1_ucm                              false
% 19.85/2.99  --bmc1_add_unsat_core                   none
% 19.85/2.99  --bmc1_unsat_core_children              false
% 19.85/2.99  --bmc1_unsat_core_extrapolate_axioms    false
% 19.85/2.99  --bmc1_out_stat                         full
% 19.85/2.99  --bmc1_ground_init                      false
% 19.85/2.99  --bmc1_pre_inst_next_state              false
% 19.85/2.99  --bmc1_pre_inst_state                   false
% 19.85/2.99  --bmc1_pre_inst_reach_state             false
% 19.85/2.99  --bmc1_out_unsat_core                   false
% 19.85/2.99  --bmc1_aig_witness_out                  false
% 19.85/2.99  --bmc1_verbose                          false
% 19.85/2.99  --bmc1_dump_clauses_tptp                false
% 19.85/2.99  --bmc1_dump_unsat_core_tptp             false
% 19.85/2.99  --bmc1_dump_file                        -
% 19.85/2.99  --bmc1_ucm_expand_uc_limit              128
% 19.85/2.99  --bmc1_ucm_n_expand_iterations          6
% 19.85/2.99  --bmc1_ucm_extend_mode                  1
% 19.85/2.99  --bmc1_ucm_init_mode                    2
% 19.85/2.99  --bmc1_ucm_cone_mode                    none
% 19.85/2.99  --bmc1_ucm_reduced_relation_type        0
% 19.85/2.99  --bmc1_ucm_relax_model                  4
% 19.85/2.99  --bmc1_ucm_full_tr_after_sat            true
% 19.85/2.99  --bmc1_ucm_expand_neg_assumptions       false
% 19.85/2.99  --bmc1_ucm_layered_model                none
% 19.85/2.99  --bmc1_ucm_max_lemma_size               10
% 19.85/2.99  
% 19.85/2.99  ------ AIG Options
% 19.85/2.99  
% 19.85/2.99  --aig_mode                              false
% 19.85/2.99  
% 19.85/2.99  ------ Instantiation Options
% 19.85/2.99  
% 19.85/2.99  --instantiation_flag                    true
% 19.85/2.99  --inst_sos_flag                         false
% 19.85/2.99  --inst_sos_phase                        true
% 19.85/2.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 19.85/2.99  --inst_lit_sel_side                     none
% 19.85/2.99  --inst_solver_per_active                1400
% 19.85/2.99  --inst_solver_calls_frac                1.
% 19.85/2.99  --inst_passive_queue_type               priority_queues
% 19.85/2.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 19.85/2.99  --inst_passive_queues_freq              [25;2]
% 19.85/2.99  --inst_dismatching                      true
% 19.85/2.99  --inst_eager_unprocessed_to_passive     true
% 19.85/2.99  --inst_prop_sim_given                   true
% 19.85/2.99  --inst_prop_sim_new                     false
% 19.85/2.99  --inst_subs_new                         false
% 19.85/2.99  --inst_eq_res_simp                      false
% 19.85/2.99  --inst_subs_given                       false
% 19.85/2.99  --inst_orphan_elimination               true
% 19.85/2.99  --inst_learning_loop_flag               true
% 19.85/2.99  --inst_learning_start                   3000
% 19.85/2.99  --inst_learning_factor                  2
% 19.85/2.99  --inst_start_prop_sim_after_learn       3
% 19.85/2.99  --inst_sel_renew                        solver
% 19.85/2.99  --inst_lit_activity_flag                true
% 19.85/2.99  --inst_restr_to_given                   false
% 19.85/2.99  --inst_activity_threshold               500
% 19.85/2.99  --inst_out_proof                        true
% 19.85/2.99  
% 19.85/2.99  ------ Resolution Options
% 19.85/2.99  
% 19.85/2.99  --resolution_flag                       false
% 19.85/2.99  --res_lit_sel                           adaptive
% 19.85/2.99  --res_lit_sel_side                      none
% 19.85/2.99  --res_ordering                          kbo
% 19.85/2.99  --res_to_prop_solver                    active
% 19.85/2.99  --res_prop_simpl_new                    false
% 19.85/2.99  --res_prop_simpl_given                  true
% 19.85/2.99  --res_passive_queue_type                priority_queues
% 19.85/2.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 19.85/2.99  --res_passive_queues_freq               [15;5]
% 19.85/2.99  --res_forward_subs                      full
% 19.85/2.99  --res_backward_subs                     full
% 19.85/2.99  --res_forward_subs_resolution           true
% 19.85/2.99  --res_backward_subs_resolution          true
% 19.85/2.99  --res_orphan_elimination                true
% 19.85/2.99  --res_time_limit                        2.
% 19.85/2.99  --res_out_proof                         true
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Options
% 19.85/2.99  
% 19.85/2.99  --superposition_flag                    true
% 19.85/2.99  --sup_passive_queue_type                priority_queues
% 19.85/2.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 19.85/2.99  --sup_passive_queues_freq               [8;1;4]
% 19.85/2.99  --demod_completeness_check              fast
% 19.85/2.99  --demod_use_ground                      true
% 19.85/2.99  --sup_to_prop_solver                    passive
% 19.85/2.99  --sup_prop_simpl_new                    true
% 19.85/2.99  --sup_prop_simpl_given                  true
% 19.85/2.99  --sup_fun_splitting                     false
% 19.85/2.99  --sup_smt_interval                      50000
% 19.85/2.99  
% 19.85/2.99  ------ Superposition Simplification Setup
% 19.85/2.99  
% 19.85/2.99  --sup_indices_passive                   []
% 19.85/2.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 19.85/2.99  --sup_full_triv                         [TrivRules;PropSubs]
% 19.85/2.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_full_bw                           [BwDemod]
% 19.85/2.99  --sup_immed_triv                        [TrivRules]
% 19.85/2.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 19.85/2.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_immed_bw_main                     []
% 19.85/2.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.85/2.99  --sup_input_triv                        [Unflattening;TrivRules]
% 19.85/2.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 19.85/2.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 19.85/2.99  
% 19.85/2.99  ------ Combination Options
% 19.85/2.99  
% 19.85/2.99  --comb_res_mult                         3
% 19.85/2.99  --comb_sup_mult                         2
% 19.85/2.99  --comb_inst_mult                        10
% 19.85/2.99  
% 19.85/2.99  ------ Debug Options
% 19.85/2.99  
% 19.85/2.99  --dbg_backtrace                         false
% 19.85/2.99  --dbg_dump_prop_clauses                 false
% 19.85/2.99  --dbg_dump_prop_clauses_file            -
% 19.85/2.99  --dbg_out_stat                          false
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  ------ Proving...
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  % SZS status Theorem for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  % SZS output start CNFRefutation for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  fof(f6,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f15,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f6])).
% 19.85/2.99  
% 19.85/2.99  fof(f16,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.85/2.99    inference(flattening,[],[f15])).
% 19.85/2.99  
% 19.85/2.99  fof(f21,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f16])).
% 19.85/2.99  
% 19.85/2.99  fof(f36,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f21])).
% 19.85/2.99  
% 19.85/2.99  fof(f7,conjecture,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f8,negated_conjecture,(
% 19.85/2.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 19.85/2.99    inference(negated_conjecture,[],[f7])).
% 19.85/2.99  
% 19.85/2.99  fof(f17,plain,(
% 19.85/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f8])).
% 19.85/2.99  
% 19.85/2.99  fof(f18,plain,(
% 19.85/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f17])).
% 19.85/2.99  
% 19.85/2.99  fof(f25,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(X0,X1,sK3),X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f24,plain,(
% 19.85/2.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),sK2) & m1_pre_topc(X3,sK2) & m1_pre_topc(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f23,plain,(
% 19.85/2.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,sK1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f22,plain,(
% 19.85/2.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 19.85/2.99    introduced(choice_axiom,[])).
% 19.85/2.99  
% 19.85/2.99  fof(f26,plain,(
% 19.85/2.99    (((~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) & m1_pre_topc(sK3,sK2) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 19.85/2.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f18,f25,f24,f23,f22])).
% 19.85/2.99  
% 19.85/2.99  fof(f39,plain,(
% 19.85/2.99    v2_pre_topc(sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f40,plain,(
% 19.85/2.99    l1_pre_topc(sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f1,axiom,(
% 19.85/2.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f19,plain,(
% 19.85/2.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 19.85/2.99    inference(nnf_transformation,[],[f1])).
% 19.85/2.99  
% 19.85/2.99  fof(f27,plain,(
% 19.85/2.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 19.85/2.99    inference(cnf_transformation,[],[f19])).
% 19.85/2.99  
% 19.85/2.99  fof(f5,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f14,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f5])).
% 19.85/2.99  
% 19.85/2.99  fof(f35,plain,(
% 19.85/2.99    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f14])).
% 19.85/2.99  
% 19.85/2.99  fof(f46,plain,(
% 19.85/2.99    m1_pre_topc(sK3,sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f42,plain,(
% 19.85/2.99    m1_pre_topc(sK1,sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f3,axiom,(
% 19.85/2.99    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f10,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f3])).
% 19.85/2.99  
% 19.85/2.99  fof(f11,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f10])).
% 19.85/2.99  
% 19.85/2.99  fof(f20,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(nnf_transformation,[],[f11])).
% 19.85/2.99  
% 19.85/2.99  fof(f30,plain,(
% 19.85/2.99    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f20])).
% 19.85/2.99  
% 19.85/2.99  fof(f50,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (u1_struct_0(k1_tsep_1(X0,X1,X2)) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(equality_resolution,[],[f30])).
% 19.85/2.99  
% 19.85/2.99  fof(f4,axiom,(
% 19.85/2.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f12,plain,(
% 19.85/2.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 19.85/2.99    inference(ennf_transformation,[],[f4])).
% 19.85/2.99  
% 19.85/2.99  fof(f13,plain,(
% 19.85/2.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 19.85/2.99    inference(flattening,[],[f12])).
% 19.85/2.99  
% 19.85/2.99  fof(f32,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f13])).
% 19.85/2.99  
% 19.85/2.99  fof(f33,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f13])).
% 19.85/2.99  
% 19.85/2.99  fof(f34,plain,(
% 19.85/2.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f13])).
% 19.85/2.99  
% 19.85/2.99  fof(f38,plain,(
% 19.85/2.99    ~v2_struct_0(sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f41,plain,(
% 19.85/2.99    ~v2_struct_0(sK1)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f48,plain,(
% 19.85/2.99    m1_pre_topc(sK3,sK2)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f47,plain,(
% 19.85/2.99    m1_pre_topc(sK1,sK2)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f43,plain,(
% 19.85/2.99    ~v2_struct_0(sK2)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f44,plain,(
% 19.85/2.99    m1_pre_topc(sK2,sK0)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f2,axiom,(
% 19.85/2.99    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 19.85/2.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 19.85/2.99  
% 19.85/2.99  fof(f9,plain,(
% 19.85/2.99    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 19.85/2.99    inference(ennf_transformation,[],[f2])).
% 19.85/2.99  
% 19.85/2.99  fof(f29,plain,(
% 19.85/2.99    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 19.85/2.99    inference(cnf_transformation,[],[f9])).
% 19.85/2.99  
% 19.85/2.99  fof(f45,plain,(
% 19.85/2.99    ~v2_struct_0(sK3)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  fof(f49,plain,(
% 19.85/2.99    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 19.85/2.99    inference(cnf_transformation,[],[f26])).
% 19.85/2.99  
% 19.85/2.99  cnf(c_10,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | m1_pre_topc(X0,X2)
% 19.85/2.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.85/2.99      | ~ v2_pre_topc(X1)
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f36]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_21,negated_conjecture,
% 19.85/2.99      ( v2_pre_topc(sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f39]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_315,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | m1_pre_topc(X0,X2)
% 19.85/2.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | sK0 != X1 ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_10,c_21]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_316,plain,
% 19.85/2.99      ( m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X1,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X0,sK0)
% 19.85/2.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.85/2.99      | ~ l1_pre_topc(sK0) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_315]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_20,negated_conjecture,
% 19.85/2.99      ( l1_pre_topc(sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f40]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_318,plain,
% 19.85/2.99      ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
% 19.85/2.99      | ~ m1_pre_topc(X0,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X1,sK0)
% 19.85/2.99      | m1_pre_topc(X0,X1) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_316,c_20]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_319,plain,
% 19.85/2.99      ( m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X0,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X1,sK0)
% 19.85/2.99      | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_318]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1,plain,
% 19.85/2.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.85/2.99      inference(cnf_transformation,[],[f27]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_164,plain,
% 19.85/2.99      ( r1_tarski(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 19.85/2.99      inference(prop_impl,[status(thm)],[c_1]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_8,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(X1)))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f35]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_292,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | r1_tarski(X2,X3)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(X0) != X2
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X3) ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_164,c_8]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_293,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | r1_tarski(u1_struct_0(X0),X2)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X2) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_292]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_370,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | m1_pre_topc(X2,X3)
% 19.85/2.99      | ~ m1_pre_topc(X2,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X3,sK0)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(X3) != X4
% 19.85/2.99      | u1_struct_0(X2) != u1_struct_0(X0)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(X4) ),
% 19.85/2.99      inference(resolution_lifted,[status(thm)],[c_319,c_293]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_371,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | m1_pre_topc(X2,X3)
% 19.85/2.99      | ~ m1_pre_topc(X2,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X3,sK0)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(X2) != u1_struct_0(X0)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1)) != k1_zfmisc_1(u1_struct_0(X3)) ),
% 19.85/2.99      inference(unflattening,[status(thm)],[c_370]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_630,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | m1_pre_topc(X2_43,X3_43)
% 19.85/2.99      | ~ m1_pre_topc(X2_43,sK0)
% 19.85/2.99      | ~ m1_pre_topc(X3_43,sK0)
% 19.85/2.99      | ~ l1_pre_topc(X1_43)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(X3_43))
% 19.85/2.99      | u1_struct_0(X2_43) != u1_struct_0(X0_43) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_371]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2594,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | ~ m1_pre_topc(X2_43,sK0)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X2_43)
% 19.85/2.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.85/2.99      | ~ l1_pre_topc(X1_43)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(X2_43))
% 19.85/2.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_630]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_17914,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 19.85/2.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK2,sK0)
% 19.85/2.99      | ~ l1_pre_topc(X1_43)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(X1_43)) != k1_zfmisc_1(u1_struct_0(sK2))
% 19.85/2.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_2594]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_52224,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,sK2)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 19.85/2.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK2,sK0)
% 19.85/2.99      | ~ l1_pre_topc(sK2)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 19.85/2.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(X0_43) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_17914]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_72007,plain,
% 19.85/2.99      ( ~ m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)
% 19.85/2.99      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK2,sK0)
% 19.85/2.99      | ~ l1_pre_topc(sK2)
% 19.85/2.99      | k1_zfmisc_1(u1_struct_0(sK2)) != k1_zfmisc_1(u1_struct_0(sK2))
% 19.85/2.99      | u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) != u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_52224]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_651,plain,( X0_45 = X0_45 ),theory(equality) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_17769,plain,
% 19.85/2.99      ( k1_zfmisc_1(u1_struct_0(sK2)) = k1_zfmisc_1(u1_struct_0(sK2)) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_651]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_14,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK3,sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f46]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_639,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK3,sK0) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_14]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_991,plain,
% 19.85/2.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_18,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK1,sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f42]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_635,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK1,sK0) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_18]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_995,plain,
% 19.85/2.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_4,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | ~ m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | v2_struct_0(k1_tsep_1(X1,X0,X2))
% 19.85/2.99      | ~ v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.85/2.99      inference(cnf_transformation,[],[f50]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_7,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f32]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_6,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | v1_pre_topc(k1_tsep_1(X1,X0,X2))
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f33]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_5,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | ~ l1_pre_topc(X1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f34]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_129,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_4,c_7,c_6,c_5]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_130,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1)
% 19.85/2.99      | ~ m1_pre_topc(X2,X1)
% 19.85/2.99      | v2_struct_0(X0)
% 19.85/2.99      | v2_struct_0(X1)
% 19.85/2.99      | v2_struct_0(X2)
% 19.85/2.99      | ~ l1_pre_topc(X1)
% 19.85/2.99      | u1_struct_0(k1_tsep_1(X1,X0,X2)) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(X2)) ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_129]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_631,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | ~ m1_pre_topc(X2_43,X1_43)
% 19.85/2.99      | v2_struct_0(X0_43)
% 19.85/2.99      | v2_struct_0(X1_43)
% 19.85/2.99      | v2_struct_0(X2_43)
% 19.85/2.99      | ~ l1_pre_topc(X1_43)
% 19.85/2.99      | u1_struct_0(k1_tsep_1(X1_43,X0_43,X2_43)) = k2_xboole_0(u1_struct_0(X0_43),u1_struct_0(X2_43)) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_130]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_999,plain,
% 19.85/2.99      ( u1_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = k2_xboole_0(u1_struct_0(X1_43),u1_struct_0(X2_43))
% 19.85/2.99      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 19.85/2.99      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 19.85/2.99      | v2_struct_0(X0_43) = iProver_top
% 19.85/2.99      | v2_struct_0(X1_43) = iProver_top
% 19.85/2.99      | v2_struct_0(X2_43) = iProver_top
% 19.85/2.99      | l1_pre_topc(X0_43) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2863,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 19.85/2.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.85/2.99      | v2_struct_0(X0_43) = iProver_top
% 19.85/2.99      | v2_struct_0(sK1) = iProver_top
% 19.85/2.99      | v2_struct_0(sK0) = iProver_top
% 19.85/2.99      | l1_pre_topc(sK0) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_995,c_999]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_22,negated_conjecture,
% 19.85/2.99      ( ~ v2_struct_0(sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f38]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_23,plain,
% 19.85/2.99      ( v2_struct_0(sK0) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_25,plain,
% 19.85/2.99      ( l1_pre_topc(sK0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_19,negated_conjecture,
% 19.85/2.99      ( ~ v2_struct_0(sK1) ),
% 19.85/2.99      inference(cnf_transformation,[],[f41]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_26,plain,
% 19.85/2.99      ( v2_struct_0(sK1) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3906,plain,
% 19.85/2.99      ( v2_struct_0(X0_43) = iProver_top
% 19.85/2.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.85/2.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43)) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_2863,c_23,c_25,c_26]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3907,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 19.85/2.99      | m1_pre_topc(X0_43,sK0) != iProver_top
% 19.85/2.99      | v2_struct_0(X0_43) = iProver_top ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_3906]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3915,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 19.85/2.99      | v2_struct_0(sK3) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_991,c_3907]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_12,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK3,sK2) ),
% 19.85/2.99      inference(cnf_transformation,[],[f48]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_641,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK3,sK2) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_12]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_989,plain,
% 19.85/2.99      ( m1_pre_topc(sK3,sK2) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_13,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK1,sK2) ),
% 19.85/2.99      inference(cnf_transformation,[],[f47]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_640,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK1,sK2) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_13]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_990,plain,
% 19.85/2.99      ( m1_pre_topc(sK1,sK2) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_640]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2860,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 19.85/2.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.85/2.99      | v2_struct_0(X0_43) = iProver_top
% 19.85/2.99      | v2_struct_0(sK2) = iProver_top
% 19.85/2.99      | v2_struct_0(sK1) = iProver_top
% 19.85/2.99      | l1_pre_topc(sK2) != iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_990,c_999]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_17,negated_conjecture,
% 19.85/2.99      ( ~ v2_struct_0(sK2) ),
% 19.85/2.99      inference(cnf_transformation,[],[f43]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_28,plain,
% 19.85/2.99      ( v2_struct_0(sK2) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_16,negated_conjecture,
% 19.85/2.99      ( m1_pre_topc(sK2,sK0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f44]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_29,plain,
% 19.85/2.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_2,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 19.85/2.99      inference(cnf_transformation,[],[f29]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_647,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | ~ l1_pre_topc(X1_43)
% 19.85/2.99      | l1_pre_topc(X0_43) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_2]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1312,plain,
% 19.85/2.99      ( ~ m1_pre_topc(sK2,X0_43)
% 19.85/2.99      | ~ l1_pre_topc(X0_43)
% 19.85/2.99      | l1_pre_topc(sK2) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_647]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1313,plain,
% 19.85/2.99      ( m1_pre_topc(sK2,X0_43) != iProver_top
% 19.85/2.99      | l1_pre_topc(X0_43) != iProver_top
% 19.85/2.99      | l1_pre_topc(sK2) = iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_1312]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1315,plain,
% 19.85/2.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 19.85/2.99      | l1_pre_topc(sK2) = iProver_top
% 19.85/2.99      | l1_pre_topc(sK0) != iProver_top ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_1313]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3055,plain,
% 19.85/2.99      ( v2_struct_0(X0_43) = iProver_top
% 19.85/2.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.85/2.99      | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43)) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_2860,c_25,c_26,c_28,c_29,c_1315]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3056,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X0_43)) = u1_struct_0(k1_tsep_1(sK2,sK1,X0_43))
% 19.85/2.99      | m1_pre_topc(X0_43,sK2) != iProver_top
% 19.85/2.99      | v2_struct_0(X0_43) = iProver_top ),
% 19.85/2.99      inference(renaming,[status(thm)],[c_3055]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3064,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 19.85/2.99      | v2_struct_0(sK3) = iProver_top ),
% 19.85/2.99      inference(superposition,[status(thm)],[c_989,c_3056]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_15,negated_conjecture,
% 19.85/2.99      ( ~ v2_struct_0(sK3) ),
% 19.85/2.99      inference(cnf_transformation,[],[f45]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_30,plain,
% 19.85/2.99      ( v2_struct_0(sK3) != iProver_top ),
% 19.85/2.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3097,plain,
% 19.85/2.99      ( k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3)) ),
% 19.85/2.99      inference(global_propositional_subsumption,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_3064,c_30]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_3946,plain,
% 19.85/2.99      ( u1_struct_0(k1_tsep_1(sK0,sK1,sK3)) = u1_struct_0(k1_tsep_1(sK2,sK1,sK3))
% 19.85/2.99      | v2_struct_0(sK3) = iProver_top ),
% 19.85/2.99      inference(demodulation,[status(thm)],[c_3915,c_3097]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_645,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,X1_43)
% 19.85/2.99      | ~ m1_pre_topc(X2_43,X1_43)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 19.85/2.99      | v2_struct_0(X0_43)
% 19.85/2.99      | v2_struct_0(X1_43)
% 19.85/2.99      | v2_struct_0(X2_43)
% 19.85/2.99      | ~ l1_pre_topc(X1_43) ),
% 19.85/2.99      inference(subtyping,[status(esa)],[c_5]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1269,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,sK0)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK1,sK0)
% 19.85/2.99      | v2_struct_0(X0_43)
% 19.85/2.99      | v2_struct_0(sK1)
% 19.85/2.99      | v2_struct_0(sK0)
% 19.85/2.99      | ~ l1_pre_topc(sK0) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_645]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1474,plain,
% 19.85/2.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK3,sK0)
% 19.85/2.99      | ~ m1_pre_topc(sK1,sK0)
% 19.85/2.99      | v2_struct_0(sK3)
% 19.85/2.99      | v2_struct_0(sK1)
% 19.85/2.99      | v2_struct_0(sK0)
% 19.85/2.99      | ~ l1_pre_topc(sK0) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_1269]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1254,plain,
% 19.85/2.99      ( ~ m1_pre_topc(X0_43,sK2)
% 19.85/2.99      | m1_pre_topc(k1_tsep_1(sK2,sK1,X0_43),sK2)
% 19.85/2.99      | ~ m1_pre_topc(sK1,sK2)
% 19.85/2.99      | v2_struct_0(X0_43)
% 19.85/2.99      | v2_struct_0(sK2)
% 19.85/2.99      | v2_struct_0(sK1)
% 19.85/2.99      | ~ l1_pre_topc(sK2) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_645]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1439,plain,
% 19.85/2.99      ( m1_pre_topc(k1_tsep_1(sK2,sK1,sK3),sK2)
% 19.85/2.99      | ~ m1_pre_topc(sK3,sK2)
% 19.85/2.99      | ~ m1_pre_topc(sK1,sK2)
% 19.85/2.99      | v2_struct_0(sK2)
% 19.85/2.99      | v2_struct_0(sK3)
% 19.85/2.99      | v2_struct_0(sK1)
% 19.85/2.99      | ~ l1_pre_topc(sK2) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_1254]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_1314,plain,
% 19.85/2.99      ( ~ m1_pre_topc(sK2,sK0) | l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 19.85/2.99      inference(instantiation,[status(thm)],[c_1312]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(c_11,negated_conjecture,
% 19.85/2.99      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
% 19.85/2.99      inference(cnf_transformation,[],[f49]) ).
% 19.85/2.99  
% 19.85/2.99  cnf(contradiction,plain,
% 19.85/2.99      ( $false ),
% 19.85/2.99      inference(minisat,
% 19.85/2.99                [status(thm)],
% 19.85/2.99                [c_72007,c_17769,c_3946,c_1474,c_1439,c_1314,c_11,c_12,
% 19.85/2.99                 c_13,c_14,c_30,c_15,c_16,c_17,c_18,c_19,c_20,c_22]) ).
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  % SZS output end CNFRefutation for theBenchmark.p
% 19.85/2.99  
% 19.85/2.99  ------                               Statistics
% 19.85/2.99  
% 19.85/2.99  ------ General
% 19.85/2.99  
% 19.85/2.99  abstr_ref_over_cycles:                  0
% 19.85/2.99  abstr_ref_under_cycles:                 0
% 19.85/2.99  gc_basic_clause_elim:                   0
% 19.85/2.99  forced_gc_time:                         0
% 19.85/2.99  parsing_time:                           0.009
% 19.85/2.99  unif_index_cands_time:                  0.
% 19.85/2.99  unif_index_add_time:                    0.
% 19.85/2.99  orderings_time:                         0.
% 19.85/2.99  out_proof_time:                         0.015
% 19.85/2.99  total_time:                             2.287
% 19.85/2.99  num_of_symbols:                         49
% 19.85/2.99  num_of_terms:                           77404
% 19.85/2.99  
% 19.85/2.99  ------ Preprocessing
% 19.85/2.99  
% 19.85/2.99  num_of_splits:                          0
% 19.85/2.99  num_of_split_atoms:                     0
% 19.85/2.99  num_of_reused_defs:                     0
% 19.85/2.99  num_eq_ax_congr_red:                    0
% 19.85/2.99  num_of_sem_filtered_clauses:            1
% 19.85/2.99  num_of_subtypes:                        3
% 19.85/2.99  monotx_restored_types:                  0
% 19.85/2.99  sat_num_of_epr_types:                   0
% 19.85/2.99  sat_num_of_non_cyclic_types:            0
% 19.85/2.99  sat_guarded_non_collapsed_types:        1
% 19.85/2.99  num_pure_diseq_elim:                    0
% 19.85/2.99  simp_replaced_by:                       0
% 19.85/2.99  res_preprocessed:                       106
% 19.85/2.99  prep_upred:                             0
% 19.85/2.99  prep_unflattend:                        6
% 19.85/2.99  smt_new_axioms:                         0
% 19.85/2.99  pred_elim_cands:                        4
% 19.85/2.99  pred_elim:                              3
% 19.85/2.99  pred_elim_cl:                           5
% 19.85/2.99  pred_elim_cycles:                       5
% 19.85/2.99  merged_defs:                            2
% 19.85/2.99  merged_defs_ncl:                        0
% 19.85/2.99  bin_hyper_res:                          2
% 19.85/2.99  prep_cycles:                            4
% 19.85/2.99  pred_elim_time:                         0.007
% 19.85/2.99  splitting_time:                         0.
% 19.85/2.99  sem_filter_time:                        0.
% 19.85/2.99  monotx_time:                            0.
% 19.85/2.99  subtype_inf_time:                       0.
% 19.85/2.99  
% 19.85/2.99  ------ Problem properties
% 19.85/2.99  
% 19.85/2.99  clauses:                                18
% 19.85/2.99  conjectures:                            11
% 19.85/2.99  epr:                                    11
% 19.85/2.99  horn:                                   13
% 19.85/2.99  ground:                                 11
% 19.85/2.99  unary:                                  11
% 19.85/2.99  binary:                                 0
% 19.85/2.99  lits:                                   60
% 19.85/2.99  lits_eq:                                5
% 19.85/2.99  fd_pure:                                0
% 19.85/2.99  fd_pseudo:                              0
% 19.85/2.99  fd_cond:                                0
% 19.85/2.99  fd_pseudo_cond:                         1
% 19.85/2.99  ac_symbols:                             0
% 19.85/2.99  
% 19.85/2.99  ------ Propositional Solver
% 19.85/2.99  
% 19.85/2.99  prop_solver_calls:                      33
% 19.85/2.99  prop_fast_solver_calls:                 3628
% 19.85/2.99  smt_solver_calls:                       0
% 19.85/2.99  smt_fast_solver_calls:                  0
% 19.85/2.99  prop_num_of_clauses:                    22522
% 19.85/2.99  prop_preprocess_simplified:             36166
% 19.85/2.99  prop_fo_subsumed:                       537
% 19.85/2.99  prop_solver_time:                       0.
% 19.85/2.99  smt_solver_time:                        0.
% 19.85/2.99  smt_fast_solver_time:                   0.
% 19.85/2.99  prop_fast_solver_time:                  0.
% 19.85/2.99  prop_unsat_core_time:                   0.004
% 19.85/2.99  
% 19.85/2.99  ------ QBF
% 19.85/2.99  
% 19.85/2.99  qbf_q_res:                              0
% 19.85/2.99  qbf_num_tautologies:                    0
% 19.85/2.99  qbf_prep_cycles:                        0
% 19.85/2.99  
% 19.85/2.99  ------ BMC1
% 19.85/2.99  
% 19.85/2.99  bmc1_current_bound:                     -1
% 19.85/2.99  bmc1_last_solved_bound:                 -1
% 19.85/2.99  bmc1_unsat_core_size:                   -1
% 19.85/2.99  bmc1_unsat_core_parents_size:           -1
% 19.85/2.99  bmc1_merge_next_fun:                    0
% 19.85/2.99  bmc1_unsat_core_clauses_time:           0.
% 19.85/2.99  
% 19.85/2.99  ------ Instantiation
% 19.85/2.99  
% 19.85/2.99  inst_num_of_clauses:                    5453
% 19.85/2.99  inst_num_in_passive:                    2554
% 19.85/2.99  inst_num_in_active:                     2161
% 19.85/2.99  inst_num_in_unprocessed:                737
% 19.85/2.99  inst_num_of_loops:                      2366
% 19.85/2.99  inst_num_of_learning_restarts:          0
% 19.85/2.99  inst_num_moves_active_passive:          203
% 19.85/2.99  inst_lit_activity:                      0
% 19.85/2.99  inst_lit_activity_moves:                3
% 19.85/2.99  inst_num_tautologies:                   0
% 19.85/2.99  inst_num_prop_implied:                  0
% 19.85/2.99  inst_num_existing_simplified:           0
% 19.85/2.99  inst_num_eq_res_simplified:             0
% 19.85/2.99  inst_num_child_elim:                    0
% 19.85/2.99  inst_num_of_dismatching_blockings:      13281
% 19.85/2.99  inst_num_of_non_proper_insts:           6242
% 19.85/2.99  inst_num_of_duplicates:                 0
% 19.85/2.99  inst_inst_num_from_inst_to_res:         0
% 19.85/2.99  inst_dismatching_checking_time:         0.
% 19.85/2.99  
% 19.85/2.99  ------ Resolution
% 19.85/2.99  
% 19.85/2.99  res_num_of_clauses:                     0
% 19.85/2.99  res_num_in_passive:                     0
% 19.85/2.99  res_num_in_active:                      0
% 19.85/2.99  res_num_of_loops:                       110
% 19.85/2.99  res_forward_subset_subsumed:            221
% 19.85/2.99  res_backward_subset_subsumed:           0
% 19.85/2.99  res_forward_subsumed:                   0
% 19.85/2.99  res_backward_subsumed:                  0
% 19.85/2.99  res_forward_subsumption_resolution:     2
% 19.85/2.99  res_backward_subsumption_resolution:    0
% 19.85/2.99  res_clause_to_clause_subsumption:       9765
% 19.85/2.99  res_orphan_elimination:                 0
% 19.85/2.99  res_tautology_del:                      183
% 19.85/2.99  res_num_eq_res_simplified:              0
% 19.85/2.99  res_num_sel_changes:                    0
% 19.85/2.99  res_moves_from_active_to_pass:          0
% 19.85/2.99  
% 19.85/2.99  ------ Superposition
% 19.85/2.99  
% 19.85/2.99  sup_time_total:                         0.
% 19.85/2.99  sup_time_generating:                    0.
% 19.85/2.99  sup_time_sim_full:                      0.
% 19.85/2.99  sup_time_sim_immed:                     0.
% 19.85/2.99  
% 19.85/2.99  sup_num_of_clauses:                     1517
% 19.85/2.99  sup_num_in_active:                      438
% 19.85/2.99  sup_num_in_passive:                     1079
% 19.85/2.99  sup_num_of_loops:                       472
% 19.85/2.99  sup_fw_superposition:                   992
% 19.85/2.99  sup_bw_superposition:                   545
% 19.85/2.99  sup_immediate_simplified:               58
% 19.85/2.99  sup_given_eliminated:                   0
% 19.85/2.99  comparisons_done:                       0
% 19.85/2.99  comparisons_avoided:                    0
% 19.85/2.99  
% 19.85/2.99  ------ Simplifications
% 19.85/2.99  
% 19.85/2.99  
% 19.85/2.99  sim_fw_subset_subsumed:                 0
% 19.85/2.99  sim_bw_subset_subsumed:                 24
% 19.85/2.99  sim_fw_subsumed:                        4
% 19.85/2.99  sim_bw_subsumed:                        0
% 19.85/2.99  sim_fw_subsumption_res:                 1
% 19.85/2.99  sim_bw_subsumption_res:                 0
% 19.85/2.99  sim_tautology_del:                      8
% 19.85/2.99  sim_eq_tautology_del:                   0
% 19.85/2.99  sim_eq_res_simp:                        0
% 19.85/2.99  sim_fw_demodulated:                     12
% 19.85/2.99  sim_bw_demodulated:                     12
% 19.85/2.99  sim_light_normalised:                   46
% 19.85/2.99  sim_joinable_taut:                      0
% 19.85/2.99  sim_joinable_simp:                      0
% 19.85/2.99  sim_ac_normalised:                      0
% 19.85/2.99  sim_smt_subsumption:                    0
% 19.85/2.99  
%------------------------------------------------------------------------------
