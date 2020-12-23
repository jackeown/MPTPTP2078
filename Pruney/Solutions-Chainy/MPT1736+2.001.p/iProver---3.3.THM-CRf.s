%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:16 EST 2020

% Result     : Theorem 15.07s
% Output     : CNFRefutation 15.07s
% Verified   : 
% Statistics : Number of formulae       :  235 (2240 expanded)
%              Number of clauses        :  156 ( 565 expanded)
%              Number of leaves         :   18 ( 773 expanded)
%              Depth                    :   25
%              Number of atoms          : 1538 (29438 expanded)
%              Number of equality atoms :  431 ( 944 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f14,conjecture,(
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
                    & v1_borsuk_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
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
                      & v1_borsuk_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
            | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
            | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
            | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
          & r1_tsep_1(X3,X2)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & v1_borsuk_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
          | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
          | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
          | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
        & r1_tsep_1(sK3,X2)
        & m1_pre_topc(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & v1_borsuk_1(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
              & r1_tsep_1(X3,X2)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & v1_borsuk_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,sK2,X1))
              | ~ v1_borsuk_1(X1,k1_tsep_1(X0,sK2,X1))
              | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,sK2))
              | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,sK2)) )
            & r1_tsep_1(X3,sK2)
            & m1_pre_topc(X1,X3)
            & m1_pre_topc(X3,X0)
            & v1_borsuk_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_borsuk_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_pre_topc(sK1,k1_tsep_1(X0,X2,sK1))
                  | ~ v1_borsuk_1(sK1,k1_tsep_1(X0,X2,sK1))
                  | ~ m1_pre_topc(sK1,k1_tsep_1(X0,sK1,X2))
                  | ~ v1_borsuk_1(sK1,k1_tsep_1(X0,sK1,X2)) )
                & r1_tsep_1(X3,X2)
                & m1_pre_topc(sK1,X3)
                & m1_pre_topc(X3,X0)
                & v1_borsuk_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1))
                      | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      | ~ v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2)) )
                    & r1_tsep_1(X3,X2)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_borsuk_1(X3,X0)
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
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                    | ~ v1_borsuk_1(X1,k1_tsep_1(sK0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & v1_borsuk_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
      | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
    & r1_tsep_1(sK3,sK2)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & v1_borsuk_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f50,f49,f48,f47])).

fof(f86,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f84,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f8,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f81,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f89,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
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
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f92,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_borsuk_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_borsuk_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
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
                 => ( ~ ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                        & ~ ( r1_tsep_1(X3,X2)
                            & r1_tsep_1(X3,X1) ) )
                    & ~ ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1)
                        & ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ~ ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                        & ~ ( r1_tsep_1(X2,X3)
                            & r1_tsep_1(X1,X3) ) )
                    & ~ ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3)
                        & ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      | ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1)
                      | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      | ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) )
                    & ( ~ r1_tsep_1(X2,X3)
                      | ~ r1_tsep_1(X1,X3)
                      | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
      | r1_tsep_1(X3,X1)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
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

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  | ~ m1_pre_topc(X3,X2)
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_borsuk_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_borsuk_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_borsuk_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_borsuk_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_717,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1393,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | m1_pre_topc(k1_tsep_1(X1_43,X2_43,X0_43),X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_719,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1391,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_3066,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1393,c_1391])).

cnf(c_34,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_689,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_34])).

cnf(c_1421,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_36,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_687,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_36])).

cnf(c_1423,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_13,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43))
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1400,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,k1_tsep_1(X1_43,X2_43,X0_43)) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_14,plain,
    ( ~ m1_pre_topc(X0,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_709,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1401,plain,
    ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
    | m1_pre_topc(X0_43,X1_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_709])).

cnf(c_5370,plain,
    ( k1_tsep_1(k1_tsep_1(X0_43,X1_43,X2_43),X1_43,X1_43) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43)) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_1401])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(k1_tsep_1(X1,X0,X2)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_715,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1395,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(k1_tsep_1(X1_43,X2_43,X0_43)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_716,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ v2_struct_0(k1_tsep_1(X1_43,X0_43,X2_43))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1394,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(k1_tsep_1(X1_43,X2_43,X0_43)) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_31887,plain,
    ( k1_tsep_1(k1_tsep_1(X0_43,X1_43,X2_43),X1_43,X1_43) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5370,c_1395,c_3066,c_1394])).

cnf(c_31894,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK1),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_31887])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_41,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_39,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_42,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_43,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_37,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_44,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34982,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK1),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31894,c_41,c_42,c_43,c_44])).

cnf(c_34992,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_struct_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_34982])).

cnf(c_3011,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1401])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_2090,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_5194,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3011,c_40,c_39,c_38,c_35,c_34,c_2090])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_718,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1392,plain,
    ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_718])).

cnf(c_2940,plain,
    ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1392])).

cnf(c_46,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5819,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2940,c_41,c_43,c_46])).

cnf(c_5820,plain,
    ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_5819])).

cnf(c_5830,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_5820])).

cnf(c_5934,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5830,c_44])).

cnf(c_35125,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(sK2) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34992,c_5194,c_5934])).

cnf(c_45,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_47,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5939,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5934,c_1400])).

cnf(c_7194,plain,
    ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5939,c_41,c_42,c_43,c_44,c_45,c_46,c_47])).

cnf(c_7199,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7194,c_1401])).

cnf(c_7220,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7199,c_5194])).

cnf(c_2111,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,X0_43))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_2448,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2111])).

cnf(c_2449,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2448])).

cnf(c_2131,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK1,X0_43))
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_2483,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2131])).

cnf(c_2484,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2483])).

cnf(c_7286,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7220,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_2449,c_2484])).

cnf(c_7287,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7286])).

cnf(c_11341,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_7287])).

cnf(c_49463,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_35125,c_41,c_43,c_44,c_45,c_46,c_47,c_11341])).

cnf(c_49477,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_49463,c_1393])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_48,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_borsuk_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_49,plain,
    ( v1_borsuk_1(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_50,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_51,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2151,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_717])).

cnf(c_2512,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2151])).

cnf(c_2513,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2512])).

cnf(c_2181,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X0_43))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2541,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2181])).

cnf(c_2542,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2541])).

cnf(c_11,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_712,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X0_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_5149,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,X0_43)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_5160,plain,
    ( r1_tsep_1(sK3,sK1) != iProver_top
    | m1_pre_topc(sK3,X0_43) != iProver_top
    | m1_pre_topc(sK1,X0_43) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5149])).

cnf(c_5162,plain,
    ( r1_tsep_1(sK3,sK1) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5160])).

cnf(c_28,negated_conjecture,
    ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_695,negated_conjecture,
    ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1415,plain,
    ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_53,plain,
    ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2558,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1415,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_53,c_2542])).

cnf(c_2559,plain,
    ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2558])).

cnf(c_5937,plain,
    ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5934,c_2559])).

cnf(c_693,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1417,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_17,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3)
    | k2_tsep_1(X3,X0,k1_tsep_1(X3,X1,X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_706,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X3_43)
    | ~ m1_pre_topc(X0_43,X3_43)
    | ~ m1_pre_topc(X1_43,X3_43)
    | ~ m1_pre_topc(X2_43,X0_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43)
    | ~ l1_pre_topc(X3_43)
    | ~ v2_pre_topc(X3_43)
    | k2_tsep_1(X3_43,X0_43,k1_tsep_1(X3_43,X1_43,X2_43)) = g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1404,plain,
    ( k2_tsep_1(X0_43,X1_43,k1_tsep_1(X0_43,X2_43,X3_43)) = g1_pre_topc(u1_struct_0(X3_43),u1_pre_topc(X3_43))
    | r1_tsep_1(X1_43,X2_43) != iProver_top
    | m1_pre_topc(X3_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | m1_pre_topc(X3_43,X1_43) != iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_8070,plain,
    ( k2_tsep_1(sK0,X0_43,k1_tsep_1(sK0,sK2,X1_43)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | r1_tsep_1(X0_43,sK2) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1404])).

cnf(c_9524,plain,
    ( k2_tsep_1(sK0,X0_43,k1_tsep_1(sK0,sK2,X1_43)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | r1_tsep_1(X0_43,sK2) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | m1_pre_topc(X1_43,sK0) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8070,c_41,c_42,c_43,c_46])).

cnf(c_9537,plain,
    ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK2,sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | r1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_9524])).

cnf(c_3012,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1401])).

cnf(c_2093,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_709])).

cnf(c_5198,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3012,c_40,c_39,c_38,c_37,c_36,c_2093])).

cnf(c_9738,plain,
    ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,sK1,sK1)
    | r1_tsep_1(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9537,c_5198,c_5934])).

cnf(c_29,negated_conjecture,
    ( r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_52,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_11584,plain,
    ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9738,c_44,c_45,c_48,c_50,c_52])).

cnf(c_27,plain,
    ( r1_tsep_1(X0,X1)
    | ~ v1_borsuk_1(X0,X2)
    | v1_borsuk_1(k2_tsep_1(X2,X0,X1),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_696,plain,
    ( r1_tsep_1(X0_43,X1_43)
    | ~ v1_borsuk_1(X0_43,X2_43)
    | v1_borsuk_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1414,plain,
    ( r1_tsep_1(X0_43,X1_43) = iProver_top
    | v1_borsuk_1(X0_43,X2_43) != iProver_top
    | v1_borsuk_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43) = iProver_top
    | m1_pre_topc(X1_43,X2_43) != iProver_top
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X2_43) != iProver_top
    | v2_pre_topc(X2_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_11587,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_borsuk_1(sK3,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_11584,c_1414])).

cnf(c_21,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(X0,k1_tsep_1(X2,X1,X3))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_702,plain,
    ( r1_tsep_1(X0_43,X1_43)
    | ~ r1_tsep_1(X0_43,k1_tsep_1(X2_43,X1_43,X3_43))
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X3_43,X2_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_2269,plain,
    ( ~ r1_tsep_1(X0_43,k1_tsep_1(sK0,sK1,X1_43))
    | r1_tsep_1(X0_43,sK1)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_2765,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,X0_43))
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_25264,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,sK1)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_25265,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | r1_tsep_1(sK3,sK1) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25264])).

cnf(c_31893,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK2),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_31887])).

cnf(c_34810,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK2),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_31893,c_41,c_42,c_43,c_46])).

cnf(c_34821,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_34810])).

cnf(c_34950,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = k1_tsep_1(sK0,sK1,sK1)
    | v2_struct_0(sK1) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_34821,c_5198])).

cnf(c_48577,plain,
    ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_34950,c_44])).

cnf(c_48591,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_48577,c_1393])).

cnf(c_15,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X3,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X3),X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_708,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X3_43,X2_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | ~ m1_pre_topc(X3_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X3_43),X2_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_2319,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X1_43,sK0)
    | ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),X1_43)
    | ~ m1_pre_topc(sK1,X1_43)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_4544,plain,
    ( ~ m1_pre_topc(X0_43,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2319])).

cnf(c_14838,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_4544])).

cnf(c_14839,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14838])).

cnf(c_51213,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_48591,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_2449,c_2513,c_2542,c_14839])).

cnf(c_8,plain,
    ( v1_borsuk_1(X0,X1)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_713,plain,
    ( v1_borsuk_1(X0_43,X1_43)
    | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ l1_pre_topc(X0_43)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ v2_pre_topc(X1_43)
    | ~ v2_pre_topc(X0_43)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1397,plain,
    ( v1_borsuk_1(X0_43,X1_43) = iProver_top
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_720,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1390,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1780,plain,
    ( v1_borsuk_1(X0_43,X1_43) = iProver_top
    | v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1397,c_1390,c_1391])).

cnf(c_16976,plain,
    ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | v1_borsuk_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5198,c_1780])).

cnf(c_17032,plain,
    ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | v1_borsuk_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_16976,c_5198])).

cnf(c_2385,plain,
    ( ~ m1_pre_topc(sK3,X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(sK3) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_2386,plain,
    ( m1_pre_topc(sK3,X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2385])).

cnf(c_2388,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | l1_pre_topc(sK3) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2386])).

cnf(c_2397,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1390])).

cnf(c_692,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1418,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_2398,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1418,c_1390])).

cnf(c_2715,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | l1_pre_topc(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1417,c_1391])).

cnf(c_17918,plain,
    ( v2_pre_topc(X0_43) != iProver_top
    | v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | v1_borsuk_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17032,c_42,c_43,c_50,c_2388,c_2397,c_2398,c_2715])).

cnf(c_17919,plain,
    ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | v1_borsuk_1(sK1,X0_43) = iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(renaming,[status(thm)],[c_17918])).

cnf(c_51235,plain,
    ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_51213,c_17919])).

cnf(c_54273,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_49477,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,c_50,c_51,c_2449,c_2484,c_2513,c_2542,c_5162,c_5937,c_11587,c_25265,c_51235])).

cnf(c_54278,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3066,c_54273])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_54278,c_47,c_46,c_45,c_44,c_43,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:07:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.07/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.07/2.50  
% 15.07/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.07/2.50  
% 15.07/2.50  ------  iProver source info
% 15.07/2.50  
% 15.07/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.07/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.07/2.50  git: non_committed_changes: false
% 15.07/2.50  git: last_make_outside_of_git: false
% 15.07/2.50  
% 15.07/2.50  ------ 
% 15.07/2.50  
% 15.07/2.50  ------ Input Options
% 15.07/2.50  
% 15.07/2.50  --out_options                           all
% 15.07/2.50  --tptp_safe_out                         true
% 15.07/2.50  --problem_path                          ""
% 15.07/2.50  --include_path                          ""
% 15.07/2.50  --clausifier                            res/vclausify_rel
% 15.07/2.50  --clausifier_options                    --mode clausify
% 15.07/2.50  --stdin                                 false
% 15.07/2.50  --stats_out                             all
% 15.07/2.50  
% 15.07/2.50  ------ General Options
% 15.07/2.50  
% 15.07/2.50  --fof                                   false
% 15.07/2.50  --time_out_real                         305.
% 15.07/2.50  --time_out_virtual                      -1.
% 15.07/2.50  --symbol_type_check                     false
% 15.07/2.50  --clausify_out                          false
% 15.07/2.50  --sig_cnt_out                           false
% 15.07/2.50  --trig_cnt_out                          false
% 15.07/2.50  --trig_cnt_out_tolerance                1.
% 15.07/2.50  --trig_cnt_out_sk_spl                   false
% 15.07/2.50  --abstr_cl_out                          false
% 15.07/2.50  
% 15.07/2.50  ------ Global Options
% 15.07/2.50  
% 15.07/2.50  --schedule                              default
% 15.07/2.50  --add_important_lit                     false
% 15.07/2.50  --prop_solver_per_cl                    1000
% 15.07/2.50  --min_unsat_core                        false
% 15.07/2.50  --soft_assumptions                      false
% 15.07/2.50  --soft_lemma_size                       3
% 15.07/2.50  --prop_impl_unit_size                   0
% 15.07/2.50  --prop_impl_unit                        []
% 15.07/2.50  --share_sel_clauses                     true
% 15.07/2.50  --reset_solvers                         false
% 15.07/2.50  --bc_imp_inh                            [conj_cone]
% 15.07/2.50  --conj_cone_tolerance                   3.
% 15.07/2.50  --extra_neg_conj                        none
% 15.07/2.50  --large_theory_mode                     true
% 15.07/2.50  --prolific_symb_bound                   200
% 15.07/2.50  --lt_threshold                          2000
% 15.07/2.50  --clause_weak_htbl                      true
% 15.07/2.50  --gc_record_bc_elim                     false
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing Options
% 15.07/2.50  
% 15.07/2.50  --preprocessing_flag                    true
% 15.07/2.50  --time_out_prep_mult                    0.1
% 15.07/2.50  --splitting_mode                        input
% 15.07/2.50  --splitting_grd                         true
% 15.07/2.50  --splitting_cvd                         false
% 15.07/2.50  --splitting_cvd_svl                     false
% 15.07/2.50  --splitting_nvd                         32
% 15.07/2.50  --sub_typing                            true
% 15.07/2.50  --prep_gs_sim                           true
% 15.07/2.50  --prep_unflatten                        true
% 15.07/2.50  --prep_res_sim                          true
% 15.07/2.50  --prep_upred                            true
% 15.07/2.50  --prep_sem_filter                       exhaustive
% 15.07/2.50  --prep_sem_filter_out                   false
% 15.07/2.50  --pred_elim                             true
% 15.07/2.50  --res_sim_input                         true
% 15.07/2.50  --eq_ax_congr_red                       true
% 15.07/2.50  --pure_diseq_elim                       true
% 15.07/2.50  --brand_transform                       false
% 15.07/2.50  --non_eq_to_eq                          false
% 15.07/2.50  --prep_def_merge                        true
% 15.07/2.50  --prep_def_merge_prop_impl              false
% 15.07/2.50  --prep_def_merge_mbd                    true
% 15.07/2.50  --prep_def_merge_tr_red                 false
% 15.07/2.50  --prep_def_merge_tr_cl                  false
% 15.07/2.50  --smt_preprocessing                     true
% 15.07/2.50  --smt_ac_axioms                         fast
% 15.07/2.50  --preprocessed_out                      false
% 15.07/2.50  --preprocessed_stats                    false
% 15.07/2.50  
% 15.07/2.50  ------ Abstraction refinement Options
% 15.07/2.50  
% 15.07/2.50  --abstr_ref                             []
% 15.07/2.50  --abstr_ref_prep                        false
% 15.07/2.50  --abstr_ref_until_sat                   false
% 15.07/2.50  --abstr_ref_sig_restrict                funpre
% 15.07/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.07/2.50  --abstr_ref_under                       []
% 15.07/2.50  
% 15.07/2.50  ------ SAT Options
% 15.07/2.50  
% 15.07/2.50  --sat_mode                              false
% 15.07/2.50  --sat_fm_restart_options                ""
% 15.07/2.50  --sat_gr_def                            false
% 15.07/2.50  --sat_epr_types                         true
% 15.07/2.50  --sat_non_cyclic_types                  false
% 15.07/2.50  --sat_finite_models                     false
% 15.07/2.50  --sat_fm_lemmas                         false
% 15.07/2.50  --sat_fm_prep                           false
% 15.07/2.50  --sat_fm_uc_incr                        true
% 15.07/2.50  --sat_out_model                         small
% 15.07/2.50  --sat_out_clauses                       false
% 15.07/2.50  
% 15.07/2.50  ------ QBF Options
% 15.07/2.50  
% 15.07/2.50  --qbf_mode                              false
% 15.07/2.50  --qbf_elim_univ                         false
% 15.07/2.50  --qbf_dom_inst                          none
% 15.07/2.50  --qbf_dom_pre_inst                      false
% 15.07/2.50  --qbf_sk_in                             false
% 15.07/2.50  --qbf_pred_elim                         true
% 15.07/2.50  --qbf_split                             512
% 15.07/2.50  
% 15.07/2.50  ------ BMC1 Options
% 15.07/2.50  
% 15.07/2.50  --bmc1_incremental                      false
% 15.07/2.50  --bmc1_axioms                           reachable_all
% 15.07/2.50  --bmc1_min_bound                        0
% 15.07/2.50  --bmc1_max_bound                        -1
% 15.07/2.50  --bmc1_max_bound_default                -1
% 15.07/2.50  --bmc1_symbol_reachability              true
% 15.07/2.50  --bmc1_property_lemmas                  false
% 15.07/2.50  --bmc1_k_induction                      false
% 15.07/2.50  --bmc1_non_equiv_states                 false
% 15.07/2.50  --bmc1_deadlock                         false
% 15.07/2.50  --bmc1_ucm                              false
% 15.07/2.50  --bmc1_add_unsat_core                   none
% 15.07/2.50  --bmc1_unsat_core_children              false
% 15.07/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.07/2.50  --bmc1_out_stat                         full
% 15.07/2.50  --bmc1_ground_init                      false
% 15.07/2.50  --bmc1_pre_inst_next_state              false
% 15.07/2.50  --bmc1_pre_inst_state                   false
% 15.07/2.50  --bmc1_pre_inst_reach_state             false
% 15.07/2.50  --bmc1_out_unsat_core                   false
% 15.07/2.50  --bmc1_aig_witness_out                  false
% 15.07/2.50  --bmc1_verbose                          false
% 15.07/2.50  --bmc1_dump_clauses_tptp                false
% 15.07/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.07/2.50  --bmc1_dump_file                        -
% 15.07/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.07/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.07/2.50  --bmc1_ucm_extend_mode                  1
% 15.07/2.50  --bmc1_ucm_init_mode                    2
% 15.07/2.50  --bmc1_ucm_cone_mode                    none
% 15.07/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.07/2.50  --bmc1_ucm_relax_model                  4
% 15.07/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.07/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.07/2.50  --bmc1_ucm_layered_model                none
% 15.07/2.50  --bmc1_ucm_max_lemma_size               10
% 15.07/2.50  
% 15.07/2.50  ------ AIG Options
% 15.07/2.50  
% 15.07/2.50  --aig_mode                              false
% 15.07/2.50  
% 15.07/2.50  ------ Instantiation Options
% 15.07/2.50  
% 15.07/2.50  --instantiation_flag                    true
% 15.07/2.50  --inst_sos_flag                         false
% 15.07/2.50  --inst_sos_phase                        true
% 15.07/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.07/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.07/2.50  --inst_lit_sel_side                     num_symb
% 15.07/2.50  --inst_solver_per_active                1400
% 15.07/2.50  --inst_solver_calls_frac                1.
% 15.07/2.50  --inst_passive_queue_type               priority_queues
% 15.07/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.07/2.50  --inst_passive_queues_freq              [25;2]
% 15.07/2.50  --inst_dismatching                      true
% 15.07/2.50  --inst_eager_unprocessed_to_passive     true
% 15.07/2.50  --inst_prop_sim_given                   true
% 15.07/2.50  --inst_prop_sim_new                     false
% 15.07/2.50  --inst_subs_new                         false
% 15.07/2.50  --inst_eq_res_simp                      false
% 15.07/2.50  --inst_subs_given                       false
% 15.07/2.50  --inst_orphan_elimination               true
% 15.07/2.50  --inst_learning_loop_flag               true
% 15.07/2.50  --inst_learning_start                   3000
% 15.07/2.50  --inst_learning_factor                  2
% 15.07/2.50  --inst_start_prop_sim_after_learn       3
% 15.07/2.50  --inst_sel_renew                        solver
% 15.07/2.50  --inst_lit_activity_flag                true
% 15.07/2.50  --inst_restr_to_given                   false
% 15.07/2.50  --inst_activity_threshold               500
% 15.07/2.50  --inst_out_proof                        true
% 15.07/2.50  
% 15.07/2.50  ------ Resolution Options
% 15.07/2.50  
% 15.07/2.50  --resolution_flag                       true
% 15.07/2.50  --res_lit_sel                           adaptive
% 15.07/2.50  --res_lit_sel_side                      none
% 15.07/2.50  --res_ordering                          kbo
% 15.07/2.50  --res_to_prop_solver                    active
% 15.07/2.50  --res_prop_simpl_new                    false
% 15.07/2.50  --res_prop_simpl_given                  true
% 15.07/2.50  --res_passive_queue_type                priority_queues
% 15.07/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.07/2.50  --res_passive_queues_freq               [15;5]
% 15.07/2.50  --res_forward_subs                      full
% 15.07/2.50  --res_backward_subs                     full
% 15.07/2.50  --res_forward_subs_resolution           true
% 15.07/2.50  --res_backward_subs_resolution          true
% 15.07/2.50  --res_orphan_elimination                true
% 15.07/2.50  --res_time_limit                        2.
% 15.07/2.50  --res_out_proof                         true
% 15.07/2.50  
% 15.07/2.50  ------ Superposition Options
% 15.07/2.50  
% 15.07/2.50  --superposition_flag                    true
% 15.07/2.50  --sup_passive_queue_type                priority_queues
% 15.07/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.07/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.07/2.50  --demod_completeness_check              fast
% 15.07/2.50  --demod_use_ground                      true
% 15.07/2.50  --sup_to_prop_solver                    passive
% 15.07/2.50  --sup_prop_simpl_new                    true
% 15.07/2.50  --sup_prop_simpl_given                  true
% 15.07/2.50  --sup_fun_splitting                     false
% 15.07/2.50  --sup_smt_interval                      50000
% 15.07/2.50  
% 15.07/2.50  ------ Superposition Simplification Setup
% 15.07/2.50  
% 15.07/2.50  --sup_indices_passive                   []
% 15.07/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.07/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_full_bw                           [BwDemod]
% 15.07/2.50  --sup_immed_triv                        [TrivRules]
% 15.07/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.07/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_immed_bw_main                     []
% 15.07/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.07/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.07/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.07/2.50  
% 15.07/2.50  ------ Combination Options
% 15.07/2.50  
% 15.07/2.50  --comb_res_mult                         3
% 15.07/2.50  --comb_sup_mult                         2
% 15.07/2.50  --comb_inst_mult                        10
% 15.07/2.50  
% 15.07/2.50  ------ Debug Options
% 15.07/2.50  
% 15.07/2.50  --dbg_backtrace                         false
% 15.07/2.50  --dbg_dump_prop_clauses                 false
% 15.07/2.50  --dbg_dump_prop_clauses_file            -
% 15.07/2.50  --dbg_out_stat                          false
% 15.07/2.50  ------ Parsing...
% 15.07/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.07/2.50  ------ Proving...
% 15.07/2.50  ------ Problem Properties 
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  clauses                                 40
% 15.07/2.50  conjectures                             13
% 15.07/2.50  EPR                                     16
% 15.07/2.50  Horn                                    19
% 15.07/2.50  unary                                   12
% 15.07/2.50  binary                                  0
% 15.07/2.50  lits                                    264
% 15.07/2.50  lits eq                                 6
% 15.07/2.50  fd_pure                                 0
% 15.07/2.50  fd_pseudo                               0
% 15.07/2.50  fd_cond                                 0
% 15.07/2.50  fd_pseudo_cond                          0
% 15.07/2.50  AC symbols                              0
% 15.07/2.50  
% 15.07/2.50  ------ Schedule dynamic 5 is on 
% 15.07/2.50  
% 15.07/2.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  ------ 
% 15.07/2.50  Current options:
% 15.07/2.50  ------ 
% 15.07/2.50  
% 15.07/2.50  ------ Input Options
% 15.07/2.50  
% 15.07/2.50  --out_options                           all
% 15.07/2.50  --tptp_safe_out                         true
% 15.07/2.50  --problem_path                          ""
% 15.07/2.50  --include_path                          ""
% 15.07/2.50  --clausifier                            res/vclausify_rel
% 15.07/2.50  --clausifier_options                    --mode clausify
% 15.07/2.50  --stdin                                 false
% 15.07/2.50  --stats_out                             all
% 15.07/2.50  
% 15.07/2.50  ------ General Options
% 15.07/2.50  
% 15.07/2.50  --fof                                   false
% 15.07/2.50  --time_out_real                         305.
% 15.07/2.50  --time_out_virtual                      -1.
% 15.07/2.50  --symbol_type_check                     false
% 15.07/2.50  --clausify_out                          false
% 15.07/2.50  --sig_cnt_out                           false
% 15.07/2.50  --trig_cnt_out                          false
% 15.07/2.50  --trig_cnt_out_tolerance                1.
% 15.07/2.50  --trig_cnt_out_sk_spl                   false
% 15.07/2.50  --abstr_cl_out                          false
% 15.07/2.50  
% 15.07/2.50  ------ Global Options
% 15.07/2.50  
% 15.07/2.50  --schedule                              default
% 15.07/2.50  --add_important_lit                     false
% 15.07/2.50  --prop_solver_per_cl                    1000
% 15.07/2.50  --min_unsat_core                        false
% 15.07/2.50  --soft_assumptions                      false
% 15.07/2.50  --soft_lemma_size                       3
% 15.07/2.50  --prop_impl_unit_size                   0
% 15.07/2.50  --prop_impl_unit                        []
% 15.07/2.50  --share_sel_clauses                     true
% 15.07/2.50  --reset_solvers                         false
% 15.07/2.50  --bc_imp_inh                            [conj_cone]
% 15.07/2.50  --conj_cone_tolerance                   3.
% 15.07/2.50  --extra_neg_conj                        none
% 15.07/2.50  --large_theory_mode                     true
% 15.07/2.50  --prolific_symb_bound                   200
% 15.07/2.50  --lt_threshold                          2000
% 15.07/2.50  --clause_weak_htbl                      true
% 15.07/2.50  --gc_record_bc_elim                     false
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing Options
% 15.07/2.50  
% 15.07/2.50  --preprocessing_flag                    true
% 15.07/2.50  --time_out_prep_mult                    0.1
% 15.07/2.50  --splitting_mode                        input
% 15.07/2.50  --splitting_grd                         true
% 15.07/2.50  --splitting_cvd                         false
% 15.07/2.50  --splitting_cvd_svl                     false
% 15.07/2.50  --splitting_nvd                         32
% 15.07/2.50  --sub_typing                            true
% 15.07/2.50  --prep_gs_sim                           true
% 15.07/2.50  --prep_unflatten                        true
% 15.07/2.50  --prep_res_sim                          true
% 15.07/2.50  --prep_upred                            true
% 15.07/2.50  --prep_sem_filter                       exhaustive
% 15.07/2.50  --prep_sem_filter_out                   false
% 15.07/2.50  --pred_elim                             true
% 15.07/2.50  --res_sim_input                         true
% 15.07/2.50  --eq_ax_congr_red                       true
% 15.07/2.50  --pure_diseq_elim                       true
% 15.07/2.50  --brand_transform                       false
% 15.07/2.50  --non_eq_to_eq                          false
% 15.07/2.50  --prep_def_merge                        true
% 15.07/2.50  --prep_def_merge_prop_impl              false
% 15.07/2.50  --prep_def_merge_mbd                    true
% 15.07/2.50  --prep_def_merge_tr_red                 false
% 15.07/2.50  --prep_def_merge_tr_cl                  false
% 15.07/2.50  --smt_preprocessing                     true
% 15.07/2.50  --smt_ac_axioms                         fast
% 15.07/2.50  --preprocessed_out                      false
% 15.07/2.50  --preprocessed_stats                    false
% 15.07/2.50  
% 15.07/2.50  ------ Abstraction refinement Options
% 15.07/2.50  
% 15.07/2.50  --abstr_ref                             []
% 15.07/2.50  --abstr_ref_prep                        false
% 15.07/2.50  --abstr_ref_until_sat                   false
% 15.07/2.50  --abstr_ref_sig_restrict                funpre
% 15.07/2.50  --abstr_ref_af_restrict_to_split_sk     false
% 15.07/2.50  --abstr_ref_under                       []
% 15.07/2.50  
% 15.07/2.50  ------ SAT Options
% 15.07/2.50  
% 15.07/2.50  --sat_mode                              false
% 15.07/2.50  --sat_fm_restart_options                ""
% 15.07/2.50  --sat_gr_def                            false
% 15.07/2.50  --sat_epr_types                         true
% 15.07/2.50  --sat_non_cyclic_types                  false
% 15.07/2.50  --sat_finite_models                     false
% 15.07/2.50  --sat_fm_lemmas                         false
% 15.07/2.50  --sat_fm_prep                           false
% 15.07/2.50  --sat_fm_uc_incr                        true
% 15.07/2.50  --sat_out_model                         small
% 15.07/2.50  --sat_out_clauses                       false
% 15.07/2.50  
% 15.07/2.50  ------ QBF Options
% 15.07/2.50  
% 15.07/2.50  --qbf_mode                              false
% 15.07/2.50  --qbf_elim_univ                         false
% 15.07/2.50  --qbf_dom_inst                          none
% 15.07/2.50  --qbf_dom_pre_inst                      false
% 15.07/2.50  --qbf_sk_in                             false
% 15.07/2.50  --qbf_pred_elim                         true
% 15.07/2.50  --qbf_split                             512
% 15.07/2.50  
% 15.07/2.50  ------ BMC1 Options
% 15.07/2.50  
% 15.07/2.50  --bmc1_incremental                      false
% 15.07/2.50  --bmc1_axioms                           reachable_all
% 15.07/2.50  --bmc1_min_bound                        0
% 15.07/2.50  --bmc1_max_bound                        -1
% 15.07/2.50  --bmc1_max_bound_default                -1
% 15.07/2.50  --bmc1_symbol_reachability              true
% 15.07/2.50  --bmc1_property_lemmas                  false
% 15.07/2.50  --bmc1_k_induction                      false
% 15.07/2.50  --bmc1_non_equiv_states                 false
% 15.07/2.50  --bmc1_deadlock                         false
% 15.07/2.50  --bmc1_ucm                              false
% 15.07/2.50  --bmc1_add_unsat_core                   none
% 15.07/2.50  --bmc1_unsat_core_children              false
% 15.07/2.50  --bmc1_unsat_core_extrapolate_axioms    false
% 15.07/2.50  --bmc1_out_stat                         full
% 15.07/2.50  --bmc1_ground_init                      false
% 15.07/2.50  --bmc1_pre_inst_next_state              false
% 15.07/2.50  --bmc1_pre_inst_state                   false
% 15.07/2.50  --bmc1_pre_inst_reach_state             false
% 15.07/2.50  --bmc1_out_unsat_core                   false
% 15.07/2.50  --bmc1_aig_witness_out                  false
% 15.07/2.50  --bmc1_verbose                          false
% 15.07/2.50  --bmc1_dump_clauses_tptp                false
% 15.07/2.50  --bmc1_dump_unsat_core_tptp             false
% 15.07/2.50  --bmc1_dump_file                        -
% 15.07/2.50  --bmc1_ucm_expand_uc_limit              128
% 15.07/2.50  --bmc1_ucm_n_expand_iterations          6
% 15.07/2.50  --bmc1_ucm_extend_mode                  1
% 15.07/2.50  --bmc1_ucm_init_mode                    2
% 15.07/2.50  --bmc1_ucm_cone_mode                    none
% 15.07/2.50  --bmc1_ucm_reduced_relation_type        0
% 15.07/2.50  --bmc1_ucm_relax_model                  4
% 15.07/2.50  --bmc1_ucm_full_tr_after_sat            true
% 15.07/2.50  --bmc1_ucm_expand_neg_assumptions       false
% 15.07/2.50  --bmc1_ucm_layered_model                none
% 15.07/2.50  --bmc1_ucm_max_lemma_size               10
% 15.07/2.50  
% 15.07/2.50  ------ AIG Options
% 15.07/2.50  
% 15.07/2.50  --aig_mode                              false
% 15.07/2.50  
% 15.07/2.50  ------ Instantiation Options
% 15.07/2.50  
% 15.07/2.50  --instantiation_flag                    true
% 15.07/2.50  --inst_sos_flag                         false
% 15.07/2.50  --inst_sos_phase                        true
% 15.07/2.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.07/2.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.07/2.50  --inst_lit_sel_side                     none
% 15.07/2.50  --inst_solver_per_active                1400
% 15.07/2.50  --inst_solver_calls_frac                1.
% 15.07/2.50  --inst_passive_queue_type               priority_queues
% 15.07/2.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.07/2.50  --inst_passive_queues_freq              [25;2]
% 15.07/2.50  --inst_dismatching                      true
% 15.07/2.50  --inst_eager_unprocessed_to_passive     true
% 15.07/2.50  --inst_prop_sim_given                   true
% 15.07/2.50  --inst_prop_sim_new                     false
% 15.07/2.50  --inst_subs_new                         false
% 15.07/2.50  --inst_eq_res_simp                      false
% 15.07/2.50  --inst_subs_given                       false
% 15.07/2.50  --inst_orphan_elimination               true
% 15.07/2.50  --inst_learning_loop_flag               true
% 15.07/2.50  --inst_learning_start                   3000
% 15.07/2.50  --inst_learning_factor                  2
% 15.07/2.50  --inst_start_prop_sim_after_learn       3
% 15.07/2.50  --inst_sel_renew                        solver
% 15.07/2.50  --inst_lit_activity_flag                true
% 15.07/2.50  --inst_restr_to_given                   false
% 15.07/2.50  --inst_activity_threshold               500
% 15.07/2.50  --inst_out_proof                        true
% 15.07/2.50  
% 15.07/2.50  ------ Resolution Options
% 15.07/2.50  
% 15.07/2.50  --resolution_flag                       false
% 15.07/2.50  --res_lit_sel                           adaptive
% 15.07/2.50  --res_lit_sel_side                      none
% 15.07/2.50  --res_ordering                          kbo
% 15.07/2.50  --res_to_prop_solver                    active
% 15.07/2.50  --res_prop_simpl_new                    false
% 15.07/2.50  --res_prop_simpl_given                  true
% 15.07/2.50  --res_passive_queue_type                priority_queues
% 15.07/2.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.07/2.50  --res_passive_queues_freq               [15;5]
% 15.07/2.50  --res_forward_subs                      full
% 15.07/2.50  --res_backward_subs                     full
% 15.07/2.50  --res_forward_subs_resolution           true
% 15.07/2.50  --res_backward_subs_resolution          true
% 15.07/2.50  --res_orphan_elimination                true
% 15.07/2.50  --res_time_limit                        2.
% 15.07/2.50  --res_out_proof                         true
% 15.07/2.50  
% 15.07/2.50  ------ Superposition Options
% 15.07/2.50  
% 15.07/2.50  --superposition_flag                    true
% 15.07/2.50  --sup_passive_queue_type                priority_queues
% 15.07/2.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.07/2.50  --sup_passive_queues_freq               [8;1;4]
% 15.07/2.50  --demod_completeness_check              fast
% 15.07/2.50  --demod_use_ground                      true
% 15.07/2.50  --sup_to_prop_solver                    passive
% 15.07/2.50  --sup_prop_simpl_new                    true
% 15.07/2.50  --sup_prop_simpl_given                  true
% 15.07/2.50  --sup_fun_splitting                     false
% 15.07/2.50  --sup_smt_interval                      50000
% 15.07/2.50  
% 15.07/2.50  ------ Superposition Simplification Setup
% 15.07/2.50  
% 15.07/2.50  --sup_indices_passive                   []
% 15.07/2.50  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.07/2.50  --sup_full_triv                         [TrivRules;PropSubs]
% 15.07/2.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_full_bw                           [BwDemod]
% 15.07/2.50  --sup_immed_triv                        [TrivRules]
% 15.07/2.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.07/2.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_immed_bw_main                     []
% 15.07/2.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.07/2.50  --sup_input_triv                        [Unflattening;TrivRules]
% 15.07/2.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.07/2.50  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.07/2.50  
% 15.07/2.50  ------ Combination Options
% 15.07/2.50  
% 15.07/2.50  --comb_res_mult                         3
% 15.07/2.50  --comb_sup_mult                         2
% 15.07/2.50  --comb_inst_mult                        10
% 15.07/2.50  
% 15.07/2.50  ------ Debug Options
% 15.07/2.50  
% 15.07/2.50  --dbg_backtrace                         false
% 15.07/2.50  --dbg_dump_prop_clauses                 false
% 15.07/2.50  --dbg_dump_prop_clauses_file            -
% 15.07/2.50  --dbg_out_stat                          false
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  ------ Proving...
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  % SZS status Theorem for theBenchmark.p
% 15.07/2.50  
% 15.07/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.07/2.50  
% 15.07/2.50  fof(f4,axiom,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f16,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 15.07/2.50    inference(pure_predicate_removal,[],[f4])).
% 15.07/2.50  
% 15.07/2.50  fof(f23,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f16])).
% 15.07/2.50  
% 15.07/2.50  fof(f24,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f23])).
% 15.07/2.50  
% 15.07/2.50  fof(f56,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f24])).
% 15.07/2.50  
% 15.07/2.50  fof(f2,axiom,(
% 15.07/2.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f20,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 15.07/2.50    inference(ennf_transformation,[],[f2])).
% 15.07/2.50  
% 15.07/2.50  fof(f53,plain,(
% 15.07/2.50    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f20])).
% 15.07/2.50  
% 15.07/2.50  fof(f14,conjecture,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ((r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3)) => (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f15,negated_conjecture,(
% 15.07/2.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ((r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3)) => (m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) & v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) & v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))))))))),
% 15.07/2.50    inference(negated_conjecture,[],[f14])).
% 15.07/2.50  
% 15.07/2.50  fof(f43,plain,(
% 15.07/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f15])).
% 15.07/2.50  
% 15.07/2.50  fof(f44,plain,(
% 15.07/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f43])).
% 15.07/2.50  
% 15.07/2.50  fof(f50,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) => ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(sK3,X2) & m1_pre_topc(X1,sK3) & m1_pre_topc(sK3,X0) & v1_borsuk_1(sK3,X0) & ~v2_struct_0(sK3))) )),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f49,plain,(
% 15.07/2.50    ( ! [X0,X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,sK2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,sK2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,sK2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,sK2))) & r1_tsep_1(X3,sK2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f48,plain,(
% 15.07/2.50    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((~m1_pre_topc(sK1,k1_tsep_1(X0,X2,sK1)) | ~v1_borsuk_1(sK1,k1_tsep_1(X0,X2,sK1)) | ~m1_pre_topc(sK1,k1_tsep_1(X0,sK1,X2)) | ~v1_borsuk_1(sK1,k1_tsep_1(X0,sK1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f47,plain,(
% 15.07/2.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(X0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(X0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & v1_borsuk_1(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1)) | ~v1_borsuk_1(X1,k1_tsep_1(sK0,X2,X1)) | ~m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2)) | ~v1_borsuk_1(X1,k1_tsep_1(sK0,X1,X2))) & r1_tsep_1(X3,X2) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & v1_borsuk_1(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 15.07/2.50    introduced(choice_axiom,[])).
% 15.07/2.50  
% 15.07/2.50  fof(f51,plain,(
% 15.07/2.50    ((((~m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) | ~v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))) & r1_tsep_1(sK3,sK2) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & v1_borsuk_1(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 15.07/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f44,f50,f49,f48,f47])).
% 15.07/2.50  
% 15.07/2.50  fof(f86,plain,(
% 15.07/2.50    m1_pre_topc(sK2,sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f84,plain,(
% 15.07/2.50    m1_pre_topc(sK1,sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f8,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f31,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f8])).
% 15.07/2.50  
% 15.07/2.50  fof(f32,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f31])).
% 15.07/2.50  
% 15.07/2.50  fof(f65,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f32])).
% 15.07/2.50  
% 15.07/2.50  fof(f9,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f33,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f9])).
% 15.07/2.50  
% 15.07/2.50  fof(f34,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f33])).
% 15.07/2.50  
% 15.07/2.50  fof(f66,plain,(
% 15.07/2.50    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f34])).
% 15.07/2.50  
% 15.07/2.50  fof(f5,axiom,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f17,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 15.07/2.50    inference(pure_predicate_removal,[],[f5])).
% 15.07/2.50  
% 15.07/2.50  fof(f25,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f17])).
% 15.07/2.50  
% 15.07/2.50  fof(f26,plain,(
% 15.07/2.50    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f25])).
% 15.07/2.50  
% 15.07/2.50  fof(f58,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f26])).
% 15.07/2.50  
% 15.07/2.50  fof(f55,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f24])).
% 15.07/2.50  
% 15.07/2.50  fof(f80,plain,(
% 15.07/2.50    ~v2_struct_0(sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f81,plain,(
% 15.07/2.50    v2_pre_topc(sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f82,plain,(
% 15.07/2.50    l1_pre_topc(sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f83,plain,(
% 15.07/2.50    ~v2_struct_0(sK1)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f85,plain,(
% 15.07/2.50    ~v2_struct_0(sK2)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f3,axiom,(
% 15.07/2.50    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f21,plain,(
% 15.07/2.50    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f3])).
% 15.07/2.50  
% 15.07/2.50  fof(f22,plain,(
% 15.07/2.50    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f21])).
% 15.07/2.50  
% 15.07/2.50  fof(f54,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f22])).
% 15.07/2.50  
% 15.07/2.50  fof(f87,plain,(
% 15.07/2.50    ~v2_struct_0(sK3)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f88,plain,(
% 15.07/2.50    v1_borsuk_1(sK3,sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f89,plain,(
% 15.07/2.50    m1_pre_topc(sK3,sK0)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f90,plain,(
% 15.07/2.50    m1_pre_topc(sK1,sK3)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f7,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f29,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f7])).
% 15.07/2.50  
% 15.07/2.50  fof(f30,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f29])).
% 15.07/2.50  
% 15.07/2.50  fof(f64,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f30])).
% 15.07/2.50  
% 15.07/2.50  fof(f92,plain,(
% 15.07/2.50    ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) | ~v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) | ~m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) | ~v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f11,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f37,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f11])).
% 15.07/2.50  
% 15.07/2.50  fof(f38,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f37])).
% 15.07/2.50  
% 15.07/2.50  fof(f70,plain,(
% 15.07/2.50    ( ! [X2,X0,X3,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1)) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f38])).
% 15.07/2.50  
% 15.07/2.50  fof(f91,plain,(
% 15.07/2.50    r1_tsep_1(sK3,sK2)),
% 15.07/2.50    inference(cnf_transformation,[],[f51])).
% 15.07/2.50  
% 15.07/2.50  fof(f13,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X2,X1) => (m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f41,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1)) | r1_tsep_1(X2,X1)) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f13])).
% 15.07/2.50  
% 15.07/2.50  fof(f42,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X2,X1),X1) & v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1)) | r1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f41])).
% 15.07/2.50  
% 15.07/2.50  fof(f78,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (v1_borsuk_1(k2_tsep_1(X0,X2,X1),X1) | r1_tsep_1(X2,X1) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f42])).
% 15.07/2.50  
% 15.07/2.50  fof(f12,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~(r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ~(r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1) & ~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & ~(r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & ~(r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3) & ~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f39,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f12])).
% 15.07/2.50  
% 15.07/2.50  fof(f40,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & (~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1) | r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) | (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) & (~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3) | r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f39])).
% 15.07/2.50  
% 15.07/2.50  fof(f76,plain,(
% 15.07/2.50    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f40])).
% 15.07/2.50  
% 15.07/2.50  fof(f10,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f35,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | (~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f10])).
% 15.07/2.50  
% 15.07/2.50  fof(f36,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 15.07/2.50    inference(flattening,[],[f35])).
% 15.07/2.50  
% 15.07/2.50  fof(f67,plain,(
% 15.07/2.50    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f36])).
% 15.07/2.50  
% 15.07/2.50  fof(f6,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((l1_pre_topc(X2) & v2_pre_topc(X2)) => (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)))))))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f27,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2) | (~l1_pre_topc(X2) | ~v2_pre_topc(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f6])).
% 15.07/2.50  
% 15.07/2.50  fof(f28,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> (m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.07/2.50    inference(flattening,[],[f27])).
% 15.07/2.50  
% 15.07/2.50  fof(f45,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | (~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0))) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | (~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0)))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.07/2.50    inference(nnf_transformation,[],[f28])).
% 15.07/2.50  
% 15.07/2.50  fof(f46,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0)) & ((m1_pre_topc(X2,X0) & v1_borsuk_1(X2,X0)) | ~m1_pre_topc(X1,X0) | ~v1_borsuk_1(X1,X0))) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.07/2.50    inference(flattening,[],[f45])).
% 15.07/2.50  
% 15.07/2.50  fof(f61,plain,(
% 15.07/2.50    ( ! [X2,X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(X2,X0) | ~v1_borsuk_1(X2,X0) | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2 | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f46])).
% 15.07/2.50  
% 15.07/2.50  fof(f94,plain,(
% 15.07/2.50    ( ! [X0,X1] : (v1_borsuk_1(X1,X0) | ~m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~v1_borsuk_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.07/2.50    inference(equality_resolution,[],[f61])).
% 15.07/2.50  
% 15.07/2.50  fof(f1,axiom,(
% 15.07/2.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 15.07/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.07/2.50  
% 15.07/2.50  fof(f18,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 15.07/2.50    inference(ennf_transformation,[],[f1])).
% 15.07/2.50  
% 15.07/2.50  fof(f19,plain,(
% 15.07/2.50    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 15.07/2.50    inference(flattening,[],[f18])).
% 15.07/2.50  
% 15.07/2.50  fof(f52,plain,(
% 15.07/2.50    ( ! [X0,X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 15.07/2.50    inference(cnf_transformation,[],[f19])).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | ~ l1_pre_topc(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f56]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_717,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_3]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1393,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(X1_43,X2_43,X0_43),X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f53]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_719,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | l1_pre_topc(X0_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_1]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1391,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3066,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43)) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1393,c_1391]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f86]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_689,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_34]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1421,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_36,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK1,sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_687,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK1,sK0) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_36]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1423,plain,
% 15.07/2.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_13,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_710,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43))
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X1_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_13]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1400,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,k1_tsep_1(X1_43,X2_43,X0_43)) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_14,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X1)
% 15.07/2.50      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k1_tsep_1(X1,X0,X0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_709,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X1_43)
% 15.07/2.50      | g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_14]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1401,plain,
% 15.07/2.50      ( g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) = k1_tsep_1(X1_43,X0_43,X0_43)
% 15.07/2.50      | m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_709]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5370,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(X0_43,X1_43,X2_43),X1_43,X1_43) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(X0_43,X1_43,X2_43)) = iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43)) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(X0_43,X1_43,X2_43)) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1400,c_1401]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X1)
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(X1,X0,X2)) ),
% 15.07/2.50      inference(cnf_transformation,[],[f58]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_715,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X1_43)
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43)) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_5]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1395,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(X1_43,X2_43,X0_43)) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_4,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
% 15.07/2.50      | ~ l1_pre_topc(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_716,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ v2_struct_0(k1_tsep_1(X1_43,X0_43,X2_43))
% 15.07/2.50      | ~ l1_pre_topc(X1_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_4]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1394,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X1_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(X1_43,X2_43,X0_43)) != iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_31887,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(X0_43,X1_43,X2_43),X1_43,X1_43) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
% 15.07/2.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(forward_subsumption_resolution,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_5370,c_1395,c_3066,c_1394]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_31894,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK1),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1423,c_31887]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_40,negated_conjecture,
% 15.07/2.50      ( ~ v2_struct_0(sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_41,plain,
% 15.07/2.50      ( v2_struct_0(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_39,negated_conjecture,
% 15.07/2.50      ( v2_pre_topc(sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_42,plain,
% 15.07/2.50      ( v2_pre_topc(sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_38,negated_conjecture,
% 15.07/2.50      ( l1_pre_topc(sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_43,plain,
% 15.07/2.50      ( l1_pre_topc(sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_37,negated_conjecture,
% 15.07/2.50      ( ~ v2_struct_0(sK1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f83]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_44,plain,
% 15.07/2.50      ( v2_struct_0(sK1) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34982,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK1),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_31894,c_41,c_42,c_43,c_44]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34992,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1421,c_34982]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3011,plain,
% 15.07/2.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2)
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1421,c_1401]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_35,negated_conjecture,
% 15.07/2.50      ( ~ v2_struct_0(sK2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f85]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2090,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0)
% 15.07/2.50      | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_709]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5194,plain,
% 15.07/2.50      ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = k1_tsep_1(sK0,sK2,sK2) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_3011,c_40,c_39,c_38,c_35,c_34,c_2090]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_718,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_2]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1392,plain,
% 15.07/2.50      ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_718]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2940,plain,
% 15.07/2.50      ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1421,c_1392]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_46,plain,
% 15.07/2.50      ( v2_struct_0(sK2) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5819,plain,
% 15.07/2.50      ( v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_2940,c_41,c_43,c_46]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5820,plain,
% 15.07/2.50      ( k1_tsep_1(sK0,X0_43,sK2) = k1_tsep_1(sK0,sK2,X0_43)
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top ),
% 15.07/2.50      inference(renaming,[status(thm)],[c_5819]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5830,plain,
% 15.07/2.50      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1423,c_5820]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5934,plain,
% 15.07/2.50      ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_5830,c_44]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_35125,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top ),
% 15.07/2.50      inference(light_normalisation,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_34992,c_5194,c_5934]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_45,plain,
% 15.07/2.50      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_47,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5939,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_5934,c_1400]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7194,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_5939,c_41,c_42,c_43,c_44,c_45,c_46,c_47]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7199,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_7194,c_1401]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7220,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(light_normalisation,[status(thm)],[c_7199,c_5194]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2111,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ v2_struct_0(k1_tsep_1(sK0,sK1,X0_43))
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_716]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2448,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2111]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2449,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2448]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2131,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,X0_43))
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_715]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2483,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2131]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2484,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2483]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7286,plain,
% 15.07/2.50      ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_7220,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_2449,c_2484]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_7287,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(renaming,[status(thm)],[c_7286]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11341,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2)
% 15.07/2.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_3066,c_7287]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_49463,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK2,sK2) = k1_tsep_1(sK0,sK2,sK2) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_35125,c_41,c_43,c_44,c_45,c_46,c_47,c_11341]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_49477,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK2),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK2,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_49463,c_1393]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_33,negated_conjecture,
% 15.07/2.50      ( ~ v2_struct_0(sK3) ),
% 15.07/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_48,plain,
% 15.07/2.50      ( v2_struct_0(sK3) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_32,negated_conjecture,
% 15.07/2.50      ( v1_borsuk_1(sK3,sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f88]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_49,plain,
% 15.07/2.50      ( v1_borsuk_1(sK3,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_31,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK3,sK0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f89]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_50,plain,
% 15.07/2.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_30,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK1,sK3) ),
% 15.07/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_51,plain,
% 15.07/2.50      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2151,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_717]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2512,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2151]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2513,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2512]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2181,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X0_43))
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_710]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2541,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2181]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2542,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2541]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11,plain,
% 15.07/2.50      ( ~ r1_tsep_1(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X1,X2)
% 15.07/2.50      | ~ m1_pre_topc(X0,X2)
% 15.07/2.50      | ~ m1_pre_topc(X1,X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | ~ l1_pre_topc(X2)
% 15.07/2.50      | ~ v2_pre_topc(X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f64]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_712,plain,
% 15.07/2.50      ( ~ r1_tsep_1(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,X0_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X2_43)
% 15.07/2.50      | ~ v2_pre_topc(X2_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_11]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5149,plain,
% 15.07/2.50      ( ~ r1_tsep_1(sK3,sK1)
% 15.07/2.50      | ~ m1_pre_topc(sK3,X0_43)
% 15.07/2.50      | ~ m1_pre_topc(sK1,X0_43)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK3)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK3)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(X0_43)
% 15.07/2.50      | ~ v2_pre_topc(X0_43) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_712]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5160,plain,
% 15.07/2.50      ( r1_tsep_1(sK3,sK1) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK3) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_5149]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5162,plain,
% 15.07/2.50      ( r1_tsep_1(sK3,sK1) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK3) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_5160]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_28,negated_conjecture,
% 15.07/2.50      ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
% 15.07/2.50      | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
% 15.07/2.50      inference(cnf_transformation,[],[f92]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_695,negated_conjecture,
% 15.07/2.50      ( ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1))
% 15.07/2.50      | ~ v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_28]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1415,plain,
% 15.07/2.50      ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_53,plain,
% 15.07/2.50      ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2558,plain,
% 15.07/2.50      ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_1415,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_53,c_2542]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2559,plain,
% 15.07/2.50      ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
% 15.07/2.50      inference(renaming,[status(thm)],[c_2558]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5937,plain,
% 15.07/2.50      ( v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(demodulation,[status(thm)],[c_5934,c_2559]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_693,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK1,sK3) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_30]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1417,plain,
% 15.07/2.50      ( m1_pre_topc(sK1,sK3) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_17,plain,
% 15.07/2.50      ( ~ r1_tsep_1(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X3)
% 15.07/2.50      | ~ m1_pre_topc(X0,X3)
% 15.07/2.50      | ~ m1_pre_topc(X2,X0)
% 15.07/2.50      | ~ m1_pre_topc(X1,X3)
% 15.07/2.50      | v2_struct_0(X3)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | ~ l1_pre_topc(X3)
% 15.07/2.50      | ~ v2_pre_topc(X3)
% 15.07/2.50      | k2_tsep_1(X3,X0,k1_tsep_1(X3,X1,X2)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ),
% 15.07/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_706,plain,
% 15.07/2.50      ( ~ r1_tsep_1(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X3_43)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,X3_43)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,X3_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X0_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(X3_43)
% 15.07/2.50      | ~ l1_pre_topc(X3_43)
% 15.07/2.50      | ~ v2_pre_topc(X3_43)
% 15.07/2.50      | k2_tsep_1(X3_43,X0_43,k1_tsep_1(X3_43,X1_43,X2_43)) = g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43)) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_17]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1404,plain,
% 15.07/2.50      ( k2_tsep_1(X0_43,X1_43,k1_tsep_1(X0_43,X2_43,X3_43)) = g1_pre_topc(u1_struct_0(X3_43),u1_pre_topc(X3_43))
% 15.07/2.50      | r1_tsep_1(X1_43,X2_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X3_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X2_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X3_43,X1_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X3_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_8070,plain,
% 15.07/2.50      ( k2_tsep_1(sK0,X0_43,k1_tsep_1(sK0,sK2,X1_43)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
% 15.07/2.50      | r1_tsep_1(X0_43,sK2) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1421,c_1404]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_9524,plain,
% 15.07/2.50      ( k2_tsep_1(sK0,X0_43,k1_tsep_1(sK0,sK2,X1_43)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
% 15.07/2.50      | r1_tsep_1(X0_43,sK2) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,X0_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_8070,c_41,c_42,c_43,c_46]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_9537,plain,
% 15.07/2.50      ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK2,sK1)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 15.07/2.50      | r1_tsep_1(sK3,sK2) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1417,c_9524]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_3012,plain,
% 15.07/2.50      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1)
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1423,c_1401]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2093,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0)
% 15.07/2.50      | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_709]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_5198,plain,
% 15.07/2.50      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k1_tsep_1(sK0,sK1,sK1) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_3012,c_40,c_39,c_38,c_37,c_36,c_2093]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_9738,plain,
% 15.07/2.50      ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,sK1,sK1)
% 15.07/2.50      | r1_tsep_1(sK3,sK2) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top ),
% 15.07/2.50      inference(light_normalisation,[status(thm)],[c_9537,c_5198,c_5934]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_29,negated_conjecture,
% 15.07/2.50      ( r1_tsep_1(sK3,sK2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f91]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_52,plain,
% 15.07/2.50      ( r1_tsep_1(sK3,sK2) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11584,plain,
% 15.07/2.50      ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = k1_tsep_1(sK0,sK1,sK1) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_9738,c_44,c_45,c_48,c_50,c_52]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_27,plain,
% 15.07/2.50      ( r1_tsep_1(X0,X1)
% 15.07/2.50      | ~ v1_borsuk_1(X0,X2)
% 15.07/2.50      | v1_borsuk_1(k2_tsep_1(X2,X0,X1),X1)
% 15.07/2.50      | ~ m1_pre_topc(X1,X2)
% 15.07/2.50      | ~ m1_pre_topc(X0,X2)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | ~ l1_pre_topc(X2)
% 15.07/2.50      | ~ v2_pre_topc(X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_696,plain,
% 15.07/2.50      ( r1_tsep_1(X0_43,X1_43)
% 15.07/2.50      | ~ v1_borsuk_1(X0_43,X2_43)
% 15.07/2.50      | v1_borsuk_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,X2_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X2_43)
% 15.07/2.50      | ~ v2_pre_topc(X2_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_27]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1414,plain,
% 15.07/2.50      ( r1_tsep_1(X0_43,X1_43) = iProver_top
% 15.07/2.50      | v1_borsuk_1(X0_43,X2_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(X1_43,X2_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(X0_43,X2_43) != iProver_top
% 15.07/2.50      | v2_struct_0(X2_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X1_43) = iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | l1_pre_topc(X2_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X2_43) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_11587,plain,
% 15.07/2.50      ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v1_borsuk_1(sK3,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_11584,c_1414]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_21,plain,
% 15.07/2.50      ( r1_tsep_1(X0,X1)
% 15.07/2.50      | ~ r1_tsep_1(X0,k1_tsep_1(X2,X1,X3))
% 15.07/2.50      | ~ m1_pre_topc(X1,X2)
% 15.07/2.50      | ~ m1_pre_topc(X3,X2)
% 15.07/2.50      | ~ m1_pre_topc(X0,X2)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X3)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | ~ l1_pre_topc(X2)
% 15.07/2.50      | ~ v2_pre_topc(X2) ),
% 15.07/2.50      inference(cnf_transformation,[],[f76]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_702,plain,
% 15.07/2.50      ( r1_tsep_1(X0_43,X1_43)
% 15.07/2.50      | ~ r1_tsep_1(X0_43,k1_tsep_1(X2_43,X1_43,X3_43))
% 15.07/2.50      | ~ m1_pre_topc(X1_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X3_43,X2_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(X3_43)
% 15.07/2.50      | ~ l1_pre_topc(X2_43)
% 15.07/2.50      | ~ v2_pre_topc(X2_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_21]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2269,plain,
% 15.07/2.50      ( ~ r1_tsep_1(X0_43,k1_tsep_1(sK0,sK1,X1_43))
% 15.07/2.50      | r1_tsep_1(X0_43,sK1)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_702]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2765,plain,
% 15.07/2.50      ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,X0_43))
% 15.07/2.50      | r1_tsep_1(sK3,sK1)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(sK3)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2269]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_25264,plain,
% 15.07/2.50      ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | r1_tsep_1(sK3,sK1)
% 15.07/2.50      | ~ m1_pre_topc(sK3,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK2,sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(sK3)
% 15.07/2.50      | v2_struct_0(sK2)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2765]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_25265,plain,
% 15.07/2.50      ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | r1_tsep_1(sK3,sK1) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK3) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_25264]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_31893,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK2),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1421,c_31887]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34810,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,X0_43,sK2),X0_43,X0_43) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))
% 15.07/2.50      | m1_pre_topc(X0_43,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(X0_43) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_31893,c_41,c_42,c_43,c_46]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34821,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1423,c_34810]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_34950,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = k1_tsep_1(sK0,sK1,sK1)
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top ),
% 15.07/2.50      inference(light_normalisation,[status(thm)],[c_34821,c_5198]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_48577,plain,
% 15.07/2.50      ( k1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK1,sK1) = k1_tsep_1(sK0,sK1,sK1) ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_34950,c_44]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_48591,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_48577,c_1393]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_15,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ m1_pre_topc(X2,X1)
% 15.07/2.50      | ~ m1_pre_topc(X0,X2)
% 15.07/2.50      | ~ m1_pre_topc(X3,X2)
% 15.07/2.50      | ~ m1_pre_topc(X3,X1)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(X1,X0,X3),X2)
% 15.07/2.50      | v2_struct_0(X1)
% 15.07/2.50      | v2_struct_0(X0)
% 15.07/2.50      | v2_struct_0(X2)
% 15.07/2.50      | v2_struct_0(X3)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X1) ),
% 15.07/2.50      inference(cnf_transformation,[],[f67]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_708,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X3_43,X2_43)
% 15.07/2.50      | ~ m1_pre_topc(X2_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X3_43,X1_43)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X3_43),X2_43)
% 15.07/2.50      | v2_struct_0(X2_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(X3_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X1_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_15]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2319,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(X1_43,sK0)
% 15.07/2.50      | ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),X1_43)
% 15.07/2.50      | ~ m1_pre_topc(sK1,X1_43)
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(X1_43)
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_708]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_4544,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(X0_43,sK0)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,X0_43),k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(X0_43)
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2319]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_14838,plain,
% 15.07/2.50      ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | ~ m1_pre_topc(sK1,sK0)
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
% 15.07/2.50      | v2_struct_0(sK0)
% 15.07/2.50      | v2_struct_0(sK1)
% 15.07/2.50      | ~ l1_pre_topc(sK0)
% 15.07/2.50      | ~ v2_pre_topc(sK0) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_4544]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_14839,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_14838]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_51213,plain,
% 15.07/2.50      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_48591,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_2449,
% 15.07/2.50                 c_2513,c_2542,c_14839]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_8,plain,
% 15.07/2.50      ( v1_borsuk_1(X0,X1)
% 15.07/2.50      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.07/2.50      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ l1_pre_topc(X0)
% 15.07/2.50      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
% 15.07/2.50      | ~ v2_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X0)
% 15.07/2.50      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
% 15.07/2.50      inference(cnf_transformation,[],[f94]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_713,plain,
% 15.07/2.50      ( v1_borsuk_1(X0_43,X1_43)
% 15.07/2.50      | ~ v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
% 15.07/2.50      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ l1_pre_topc(X0_43)
% 15.07/2.50      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
% 15.07/2.50      | ~ v2_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X0_43)
% 15.07/2.50      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_8]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1397,plain,
% 15.07/2.50      ( v1_borsuk_1(X0_43,X1_43) = iProver_top
% 15.07/2.50      | v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_0,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0,X1)
% 15.07/2.50      | ~ l1_pre_topc(X1)
% 15.07/2.50      | ~ v2_pre_topc(X1)
% 15.07/2.50      | v2_pre_topc(X0) ),
% 15.07/2.50      inference(cnf_transformation,[],[f52]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_720,plain,
% 15.07/2.50      ( ~ m1_pre_topc(X0_43,X1_43)
% 15.07/2.50      | ~ l1_pre_topc(X1_43)
% 15.07/2.50      | ~ v2_pre_topc(X1_43)
% 15.07/2.50      | v2_pre_topc(X0_43) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_0]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1390,plain,
% 15.07/2.50      ( m1_pre_topc(X0_43,X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1780,plain,
% 15.07/2.50      ( v1_borsuk_1(X0_43,X1_43) = iProver_top
% 15.07/2.50      | v1_borsuk_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
% 15.07/2.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X1_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X1_43) != iProver_top ),
% 15.07/2.50      inference(forward_subsumption_resolution,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_1397,c_1390,c_1391]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_16976,plain,
% 15.07/2.50      ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,X0_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(sK1) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK1) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_5198,c_1780]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_17032,plain,
% 15.07/2.50      ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,X0_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(sK1) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK1) != iProver_top ),
% 15.07/2.50      inference(light_normalisation,[status(thm)],[c_16976,c_5198]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2385,plain,
% 15.07/2.50      ( ~ m1_pre_topc(sK3,X0_43)
% 15.07/2.50      | ~ l1_pre_topc(X0_43)
% 15.07/2.50      | l1_pre_topc(sK3) ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_719]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2386,plain,
% 15.07/2.50      ( m1_pre_topc(sK3,X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(sK3) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_2385]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2388,plain,
% 15.07/2.50      ( m1_pre_topc(sK3,sK0) != iProver_top
% 15.07/2.50      | l1_pre_topc(sK3) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(instantiation,[status(thm)],[c_2386]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2397,plain,
% 15.07/2.50      ( l1_pre_topc(sK3) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK3) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK1) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1417,c_1390]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_692,negated_conjecture,
% 15.07/2.50      ( m1_pre_topc(sK3,sK0) ),
% 15.07/2.50      inference(subtyping,[status(esa)],[c_31]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_1418,plain,
% 15.07/2.50      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 15.07/2.50      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2398,plain,
% 15.07/2.50      ( l1_pre_topc(sK0) != iProver_top
% 15.07/2.50      | v2_pre_topc(sK3) = iProver_top
% 15.07/2.50      | v2_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1418,c_1390]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_2715,plain,
% 15.07/2.50      ( l1_pre_topc(sK3) != iProver_top
% 15.07/2.50      | l1_pre_topc(sK1) = iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_1417,c_1391]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_17918,plain,
% 15.07/2.50      ( v2_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,X0_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_17032,c_42,c_43,c_50,c_2388,c_2397,c_2398,c_2715]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_17919,plain,
% 15.07/2.50      ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,X0_43) = iProver_top
% 15.07/2.50      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK1),X0_43) != iProver_top
% 15.07/2.50      | l1_pre_topc(X0_43) != iProver_top
% 15.07/2.50      | v2_pre_topc(X0_43) != iProver_top ),
% 15.07/2.50      inference(renaming,[status(thm)],[c_17918]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_51235,plain,
% 15.07/2.50      ( v1_borsuk_1(k1_tsep_1(sK0,sK1,sK1),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v1_borsuk_1(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
% 15.07/2.50      | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
% 15.07/2.50      | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_51213,c_17919]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_54273,plain,
% 15.07/2.50      ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
% 15.07/2.50      inference(global_propositional_subsumption,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_49477,c_41,c_42,c_43,c_44,c_45,c_46,c_47,c_48,c_49,
% 15.07/2.50                 c_50,c_51,c_2449,c_2484,c_2513,c_2542,c_5162,c_5937,
% 15.07/2.50                 c_11587,c_25265,c_51235]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(c_54278,plain,
% 15.07/2.50      ( m1_pre_topc(sK2,sK0) != iProver_top
% 15.07/2.50      | m1_pre_topc(sK1,sK0) != iProver_top
% 15.07/2.50      | v2_struct_0(sK2) = iProver_top
% 15.07/2.50      | v2_struct_0(sK0) = iProver_top
% 15.07/2.50      | v2_struct_0(sK1) = iProver_top
% 15.07/2.50      | l1_pre_topc(sK0) != iProver_top ),
% 15.07/2.50      inference(superposition,[status(thm)],[c_3066,c_54273]) ).
% 15.07/2.50  
% 15.07/2.50  cnf(contradiction,plain,
% 15.07/2.50      ( $false ),
% 15.07/2.50      inference(minisat,
% 15.07/2.50                [status(thm)],
% 15.07/2.50                [c_54278,c_47,c_46,c_45,c_44,c_43,c_41]) ).
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.07/2.50  
% 15.07/2.50  ------                               Statistics
% 15.07/2.50  
% 15.07/2.50  ------ General
% 15.07/2.50  
% 15.07/2.50  abstr_ref_over_cycles:                  0
% 15.07/2.50  abstr_ref_under_cycles:                 0
% 15.07/2.50  gc_basic_clause_elim:                   0
% 15.07/2.50  forced_gc_time:                         0
% 15.07/2.50  parsing_time:                           0.01
% 15.07/2.50  unif_index_cands_time:                  0.
% 15.07/2.50  unif_index_add_time:                    0.
% 15.07/2.50  orderings_time:                         0.
% 15.07/2.50  out_proof_time:                         0.023
% 15.07/2.50  total_time:                             1.635
% 15.07/2.50  num_of_symbols:                         46
% 15.07/2.50  num_of_terms:                           42049
% 15.07/2.50  
% 15.07/2.50  ------ Preprocessing
% 15.07/2.50  
% 15.07/2.50  num_of_splits:                          0
% 15.07/2.50  num_of_split_atoms:                     0
% 15.07/2.50  num_of_reused_defs:                     0
% 15.07/2.50  num_eq_ax_congr_red:                    12
% 15.07/2.50  num_of_sem_filtered_clauses:            1
% 15.07/2.50  num_of_subtypes:                        3
% 15.07/2.50  monotx_restored_types:                  0
% 15.07/2.50  sat_num_of_epr_types:                   0
% 15.07/2.50  sat_num_of_non_cyclic_types:            0
% 15.07/2.50  sat_guarded_non_collapsed_types:        0
% 15.07/2.50  num_pure_diseq_elim:                    0
% 15.07/2.50  simp_replaced_by:                       0
% 15.07/2.50  res_preprocessed:                       187
% 15.07/2.50  prep_upred:                             0
% 15.07/2.50  prep_unflattend:                        0
% 15.07/2.50  smt_new_axioms:                         0
% 15.07/2.50  pred_elim_cands:                        6
% 15.07/2.50  pred_elim:                              0
% 15.07/2.50  pred_elim_cl:                           0
% 15.07/2.50  pred_elim_cycles:                       2
% 15.07/2.50  merged_defs:                            0
% 15.07/2.50  merged_defs_ncl:                        0
% 15.07/2.50  bin_hyper_res:                          0
% 15.07/2.50  prep_cycles:                            4
% 15.07/2.50  pred_elim_time:                         0.003
% 15.07/2.50  splitting_time:                         0.
% 15.07/2.50  sem_filter_time:                        0.
% 15.07/2.50  monotx_time:                            0.
% 15.07/2.50  subtype_inf_time:                       0.001
% 15.07/2.50  
% 15.07/2.50  ------ Problem properties
% 15.07/2.50  
% 15.07/2.50  clauses:                                40
% 15.07/2.50  conjectures:                            13
% 15.07/2.50  epr:                                    16
% 15.07/2.50  horn:                                   19
% 15.07/2.50  ground:                                 13
% 15.07/2.50  unary:                                  12
% 15.07/2.50  binary:                                 0
% 15.07/2.50  lits:                                   264
% 15.07/2.50  lits_eq:                                6
% 15.07/2.50  fd_pure:                                0
% 15.07/2.50  fd_pseudo:                              0
% 15.07/2.50  fd_cond:                                0
% 15.07/2.50  fd_pseudo_cond:                         0
% 15.07/2.50  ac_symbols:                             0
% 15.07/2.50  
% 15.07/2.50  ------ Propositional Solver
% 15.07/2.50  
% 15.07/2.50  prop_solver_calls:                      29
% 15.07/2.50  prop_fast_solver_calls:                 4416
% 15.07/2.50  smt_solver_calls:                       0
% 15.07/2.50  smt_fast_solver_calls:                  0
% 15.07/2.50  prop_num_of_clauses:                    12718
% 15.07/2.50  prop_preprocess_simplified:             21511
% 15.07/2.50  prop_fo_subsumed:                       514
% 15.07/2.50  prop_solver_time:                       0.
% 15.07/2.50  smt_solver_time:                        0.
% 15.07/2.50  smt_fast_solver_time:                   0.
% 15.07/2.50  prop_fast_solver_time:                  0.
% 15.07/2.50  prop_unsat_core_time:                   0.002
% 15.07/2.50  
% 15.07/2.50  ------ QBF
% 15.07/2.50  
% 15.07/2.50  qbf_q_res:                              0
% 15.07/2.50  qbf_num_tautologies:                    0
% 15.07/2.50  qbf_prep_cycles:                        0
% 15.07/2.50  
% 15.07/2.50  ------ BMC1
% 15.07/2.50  
% 15.07/2.50  bmc1_current_bound:                     -1
% 15.07/2.50  bmc1_last_solved_bound:                 -1
% 15.07/2.50  bmc1_unsat_core_size:                   -1
% 15.07/2.50  bmc1_unsat_core_parents_size:           -1
% 15.07/2.50  bmc1_merge_next_fun:                    0
% 15.07/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.07/2.50  
% 15.07/2.50  ------ Instantiation
% 15.07/2.50  
% 15.07/2.50  inst_num_of_clauses:                    2438
% 15.07/2.50  inst_num_in_passive:                    1021
% 15.07/2.50  inst_num_in_active:                     1138
% 15.07/2.50  inst_num_in_unprocessed:                279
% 15.07/2.50  inst_num_of_loops:                      1240
% 15.07/2.50  inst_num_of_learning_restarts:          0
% 15.07/2.50  inst_num_moves_active_passive:          101
% 15.07/2.50  inst_lit_activity:                      0
% 15.07/2.50  inst_lit_activity_moves:                1
% 15.07/2.50  inst_num_tautologies:                   0
% 15.07/2.50  inst_num_prop_implied:                  0
% 15.07/2.50  inst_num_existing_simplified:           0
% 15.07/2.50  inst_num_eq_res_simplified:             0
% 15.07/2.50  inst_num_child_elim:                    0
% 15.07/2.50  inst_num_of_dismatching_blockings:      3954
% 15.07/2.50  inst_num_of_non_proper_insts:           2112
% 15.07/2.50  inst_num_of_duplicates:                 0
% 15.07/2.50  inst_inst_num_from_inst_to_res:         0
% 15.07/2.50  inst_dismatching_checking_time:         0.
% 15.07/2.50  
% 15.07/2.50  ------ Resolution
% 15.07/2.50  
% 15.07/2.50  res_num_of_clauses:                     0
% 15.07/2.50  res_num_in_passive:                     0
% 15.07/2.50  res_num_in_active:                      0
% 15.07/2.50  res_num_of_loops:                       191
% 15.07/2.50  res_forward_subset_subsumed:            84
% 15.07/2.50  res_backward_subset_subsumed:           0
% 15.07/2.50  res_forward_subsumed:                   0
% 15.07/2.50  res_backward_subsumed:                  0
% 15.07/2.50  res_forward_subsumption_resolution:     0
% 15.07/2.50  res_backward_subsumption_resolution:    0
% 15.07/2.50  res_clause_to_clause_subsumption:       10749
% 15.07/2.50  res_orphan_elimination:                 0
% 15.07/2.50  res_tautology_del:                      14
% 15.07/2.50  res_num_eq_res_simplified:              0
% 15.07/2.50  res_num_sel_changes:                    0
% 15.07/2.50  res_moves_from_active_to_pass:          0
% 15.07/2.50  
% 15.07/2.50  ------ Superposition
% 15.07/2.50  
% 15.07/2.50  sup_time_total:                         0.
% 15.07/2.50  sup_time_generating:                    0.
% 15.07/2.50  sup_time_sim_full:                      0.
% 15.07/2.50  sup_time_sim_immed:                     0.
% 15.07/2.50  
% 15.07/2.50  sup_num_of_clauses:                     1310
% 15.07/2.50  sup_num_in_active:                      235
% 15.07/2.50  sup_num_in_passive:                     1075
% 15.07/2.50  sup_num_of_loops:                       246
% 15.07/2.50  sup_fw_superposition:                   783
% 15.07/2.50  sup_bw_superposition:                   1070
% 15.07/2.50  sup_immediate_simplified:               664
% 15.07/2.50  sup_given_eliminated:                   0
% 15.07/2.50  comparisons_done:                       0
% 15.07/2.50  comparisons_avoided:                    0
% 15.07/2.50  
% 15.07/2.50  ------ Simplifications
% 15.07/2.50  
% 15.07/2.50  
% 15.07/2.50  sim_fw_subset_subsumed:                 100
% 15.07/2.50  sim_bw_subset_subsumed:                 23
% 15.07/2.50  sim_fw_subsumed:                        319
% 15.07/2.50  sim_bw_subsumed:                        0
% 15.07/2.50  sim_fw_subsumption_res:                 16
% 15.07/2.50  sim_bw_subsumption_res:                 0
% 15.07/2.50  sim_tautology_del:                      65
% 15.07/2.50  sim_eq_tautology_del:                   42
% 15.07/2.50  sim_eq_res_simp:                        0
% 15.07/2.50  sim_fw_demodulated:                     3
% 15.07/2.50  sim_bw_demodulated:                     3
% 15.07/2.50  sim_light_normalised:                   306
% 15.07/2.50  sim_joinable_taut:                      0
% 15.07/2.50  sim_joinable_simp:                      0
% 15.07/2.50  sim_ac_normalised:                      0
% 15.07/2.50  sim_smt_subsumption:                    0
% 15.07/2.50  
%------------------------------------------------------------------------------
