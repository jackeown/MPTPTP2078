%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:13 EST 2020

% Result     : Theorem 14.78s
% Output     : CNFRefutation 14.78s
% Verified   : 
% Statistics : Number of formulae       :  154 (1388 expanded)
%              Number of clauses        :   95 ( 302 expanded)
%              Number of leaves         :   13 ( 451 expanded)
%              Depth                    :   14
%              Number of atoms          : 1215 (17842 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal clause size      :   32 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
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
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
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
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
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
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f21])).

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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) )
                      & ( m1_pre_topc(X1,X3)
                       => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
                      | ~ m1_pre_topc(X2,X3) )
                    & ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
                      | ~ m1_pre_topc(X1,X3) ) )
                  | r1_tsep_1(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2))
      | ~ m1_pre_topc(X1,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(X1,X3)
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
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))
      | ~ m1_pre_topc(X2,X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
             => ( ~ r1_tsep_1(X1,X2)
               => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                  & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
                & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X2)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
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
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,conjecture,(
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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f10,negated_conjecture,(
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
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( m1_pre_topc(X2,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                        & ( m1_pre_topc(X1,X3)
                         => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                            & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
              & m1_pre_topc(X2,X3) )
            | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
              & m1_pre_topc(X1,X3) ) )
          & ~ r1_tsep_1(X1,X2)
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ( ( r1_tsep_1(k2_tsep_1(X0,sK3,X1),X2)
              | r1_tsep_1(k2_tsep_1(X0,X1,sK3),X2) )
            & m1_pre_topc(X2,sK3) )
          | ( ( r1_tsep_1(k2_tsep_1(X0,X2,sK3),X1)
              | r1_tsep_1(k2_tsep_1(X0,sK3,X2),X1) )
            & m1_pre_topc(X1,sK3) ) )
        & ~ r1_tsep_1(X1,X2)
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                    | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                  & m1_pre_topc(X2,X3) )
                | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                    | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                  & m1_pre_topc(X1,X3) ) )
              & ~ r1_tsep_1(X1,X2)
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),sK2)
                  | r1_tsep_1(k2_tsep_1(X0,X1,X3),sK2) )
                & m1_pre_topc(sK2,X3) )
              | ( ( r1_tsep_1(k2_tsep_1(X0,sK2,X3),X1)
                  | r1_tsep_1(k2_tsep_1(X0,X3,sK2),X1) )
                & m1_pre_topc(X1,X3) ) )
            & ~ r1_tsep_1(X1,sK2)
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,sK1),X2)
                      | r1_tsep_1(k2_tsep_1(X0,sK1,X3),X2) )
                    & m1_pre_topc(X2,X3) )
                  | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),sK1)
                      | r1_tsep_1(k2_tsep_1(X0,X3,X2),sK1) )
                    & m1_pre_topc(sK1,X3) ) )
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                        & m1_pre_topc(X2,X3) )
                      | ( ( r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
                        & m1_pre_topc(X1,X3) ) )
                    & ~ r1_tsep_1(X1,X2)
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
                  ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2)
                        | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2) )
                      & m1_pre_topc(X2,X3) )
                    | ( ( r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1)
                        | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1) )
                      & m1_pre_topc(X1,X3) ) )
                  & ~ r1_tsep_1(X1,X2)
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

fof(f32,plain,
    ( ( ( ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
          | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) )
        & m1_pre_topc(sK2,sK3) )
      | ( ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
          | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) )
        & m1_pre_topc(sK1,sK3) ) )
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).

fof(f59,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f57,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f58,plain,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_8,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_893,plain,
    ( ~ r1_tsep_1(X0,sK2)
    | r1_tsep_1(sK2,X1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_11765,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK2,X0)
    | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_893])).

cnf(c_28475,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK3,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11765])).

cnf(c_14,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X0,X3)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X3,X1))
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2457,plain,
    ( r1_tsep_1(sK2,X0)
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK2,X0),k2_tsep_1(X1,sK3,X0))
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_28472,plain,
    ( r1_tsep_1(sK2,sK1)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK3,sK1))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2457])).

cnf(c_10,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_958,plain,
    ( ~ r1_tsep_1(X0,sK2)
    | r1_tsep_1(X1,sK2)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2684,plain,
    ( r1_tsep_1(X0,sK2)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_958])).

cnf(c_28463,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2684])).

cnf(c_13,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_2444,plain,
    ( r1_tsep_1(X0,sK2)
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,sK2),k2_tsep_1(X1,X0,sK3))
    | ~ m1_pre_topc(sK2,X1)
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_28462,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
    | ~ m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2444])).

cnf(c_11,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_5,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_3216,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X0,X1),X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,k2_tsep_1(X2,X0,X1))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(k2_tsep_1(X2,X0,X1))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_11486,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X0,X1),X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X3,k2_tsep_1(X2,X0,X1))
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X2) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3216,c_1,c_3])).

cnf(c_17,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_11726,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(sK2,sK3)
    | m1_pre_topc(sK2,sK3)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_11486,c_17])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_18,negated_conjecture,
    ( m1_pre_topc(sK2,sK3)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_0,plain,
    ( ~ l1_pre_topc(X0)
    | l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_964,plain,
    ( ~ l1_pre_topc(sK1)
    | l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_762,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_975,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_772,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1015,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_848,plain,
    ( r1_tsep_1(X0,sK1)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1042,plain,
    ( r1_tsep_1(sK2,sK1)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_848])).

cnf(c_1117,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_24])).

cnf(c_4,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_2376,plain,
    ( ~ r1_tsep_1(sK2,sK1)
    | r1_tsep_1(sK1,sK2)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1115,plain,
    ( l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_1,c_22])).

cnf(c_1921,plain,
    ( l1_pre_topc(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1115,c_26])).

cnf(c_2402,plain,
    ( l1_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_1921,c_0])).

cnf(c_3231,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5230,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_6,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X1)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_7385,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_7387,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7385])).

cnf(c_1149,plain,
    ( r1_tsep_1(X0,sK1)
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k2_tsep_1(X1,X0,sK1),k2_tsep_1(X1,X0,sK3))
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8139,plain,
    ( r1_tsep_1(sK2,sK1)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_961,plain,
    ( ~ r1_tsep_1(X0,sK1)
    | r1_tsep_1(X1,sK1)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2728,plain,
    ( ~ r1_tsep_1(X0,sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_9623,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2728])).

cnf(c_11735,plain,
    ( m1_pre_topc(sK2,sK3)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11726,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_17,c_964,c_975,c_1015,c_1042,c_1117,c_2376,c_2402,c_3231,c_5230,c_7387,c_8139,c_9623])).

cnf(c_11736,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | m1_pre_topc(sK2,sK3) ),
    inference(renaming,[status(thm)],[c_11735])).

cnf(c_11753,plain,
    ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
    | m1_pre_topc(sK2,sK3)
    | ~ l1_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | ~ l1_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_11736,c_4])).

cnf(c_767,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1003,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_1009,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_767])).

cnf(c_12,plain,
    ( r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X2)
    | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
    | ~ v2_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_863,plain,
    ( r1_tsep_1(X0,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),X0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1089,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_863])).

cnf(c_2506,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(sK1,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2508,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2506])).

cnf(c_4005,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5061,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1169,plain,
    ( r1_tsep_1(sK1,X0)
    | ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(k2_tsep_1(X1,sK1,X0),k2_tsep_1(X1,sK3,X0))
    | ~ m1_pre_topc(sK1,X1)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,X1)
    | ~ v2_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_8202,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2722,plain,
    ( ~ r1_tsep_1(X0,sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_961])).

cnf(c_11790,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2722])).

cnf(c_11960,plain,
    ( m1_pre_topc(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11753,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_18,c_1003,c_1009,c_1089,c_2508,c_4005,c_5061,c_8202,c_11736,c_11790])).

cnf(c_1244,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,k2_tsep_1(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(k2_tsep_1(X0,X1,X2))
    | ~ l1_pre_topc(X0) ),
    inference(resolution,[status(thm)],[c_5,c_2])).

cnf(c_9068,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
    | ~ m1_pre_topc(X1,X0)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X3,X0)
    | ~ m1_pre_topc(X3,k2_tsep_1(X0,X1,X2))
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1244,c_3])).

cnf(c_15,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9434,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,k2_tsep_1(sK0,sK2,sK3))
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_9068,c_15])).

cnf(c_16,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
    | m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_9674,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
    | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9434,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_19,c_16,c_15,c_964,c_975,c_1015,c_1042,c_1117,c_2376,c_2402,c_3231,c_5230,c_7387,c_8139,c_9623])).

cnf(c_7431,plain,
    ( ~ r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ m1_pre_topc(sK2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_7433,plain,
    ( ~ r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7431])).

cnf(c_5132,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3517,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2317,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,X0)
    | ~ v2_pre_topc(X0)
    | v2_struct_0(X0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2319,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_868,plain,
    ( r1_tsep_1(X0,sK1)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),X0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1095,plain,
    ( r1_tsep_1(sK2,sK1)
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_843,plain,
    ( r1_tsep_1(X0,sK2)
    | ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1036,plain,
    ( r1_tsep_1(sK1,sK2)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_843])).

cnf(c_1012,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_772])).

cnf(c_978,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_28475,c_28472,c_28463,c_28462,c_11960,c_11790,c_9674,c_8202,c_7433,c_5230,c_5132,c_5061,c_4005,c_3517,c_2508,c_2402,c_2376,c_2319,c_1117,c_1095,c_1089,c_1036,c_1015,c_1012,c_1009,c_1003,c_978,c_964,c_16,c_19,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 14.78/3.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.78/3.05  
% 14.78/3.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 14.78/3.05  
% 14.78/3.05  ------  iProver source info
% 14.78/3.05  
% 14.78/3.05  git: date: 2020-06-30 10:37:57 +0100
% 14.78/3.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 14.78/3.05  git: non_committed_changes: false
% 14.78/3.05  git: last_make_outside_of_git: false
% 14.78/3.05  
% 14.78/3.05  ------ 
% 14.78/3.05  
% 14.78/3.05  ------ Input Options
% 14.78/3.05  
% 14.78/3.05  --out_options                           all
% 14.78/3.05  --tptp_safe_out                         true
% 14.78/3.05  --problem_path                          ""
% 14.78/3.05  --include_path                          ""
% 14.78/3.05  --clausifier                            res/vclausify_rel
% 14.78/3.05  --clausifier_options                    --mode clausify
% 14.78/3.05  --stdin                                 false
% 14.78/3.05  --stats_out                             sel
% 14.78/3.05  
% 14.78/3.05  ------ General Options
% 14.78/3.05  
% 14.78/3.05  --fof                                   false
% 14.78/3.05  --time_out_real                         604.98
% 14.78/3.05  --time_out_virtual                      -1.
% 14.78/3.05  --symbol_type_check                     false
% 14.78/3.05  --clausify_out                          false
% 14.78/3.05  --sig_cnt_out                           false
% 14.78/3.05  --trig_cnt_out                          false
% 14.78/3.05  --trig_cnt_out_tolerance                1.
% 14.78/3.05  --trig_cnt_out_sk_spl                   false
% 14.78/3.05  --abstr_cl_out                          false
% 14.78/3.05  
% 14.78/3.05  ------ Global Options
% 14.78/3.05  
% 14.78/3.05  --schedule                              none
% 14.78/3.05  --add_important_lit                     false
% 14.78/3.05  --prop_solver_per_cl                    1000
% 14.78/3.05  --min_unsat_core                        false
% 14.78/3.05  --soft_assumptions                      false
% 14.78/3.05  --soft_lemma_size                       3
% 14.78/3.05  --prop_impl_unit_size                   0
% 14.78/3.05  --prop_impl_unit                        []
% 14.78/3.05  --share_sel_clauses                     true
% 14.78/3.05  --reset_solvers                         false
% 14.78/3.05  --bc_imp_inh                            [conj_cone]
% 14.78/3.05  --conj_cone_tolerance                   3.
% 14.78/3.05  --extra_neg_conj                        none
% 14.78/3.05  --large_theory_mode                     true
% 14.78/3.05  --prolific_symb_bound                   200
% 14.78/3.05  --lt_threshold                          2000
% 14.78/3.05  --clause_weak_htbl                      true
% 14.78/3.05  --gc_record_bc_elim                     false
% 14.78/3.05  
% 14.78/3.05  ------ Preprocessing Options
% 14.78/3.05  
% 14.78/3.05  --preprocessing_flag                    true
% 14.78/3.05  --time_out_prep_mult                    0.1
% 14.78/3.05  --splitting_mode                        input
% 14.78/3.05  --splitting_grd                         true
% 14.78/3.05  --splitting_cvd                         false
% 14.78/3.05  --splitting_cvd_svl                     false
% 14.78/3.05  --splitting_nvd                         32
% 14.78/3.05  --sub_typing                            true
% 14.78/3.05  --prep_gs_sim                           false
% 14.78/3.05  --prep_unflatten                        true
% 14.78/3.05  --prep_res_sim                          true
% 14.78/3.05  --prep_upred                            true
% 14.78/3.05  --prep_sem_filter                       exhaustive
% 14.78/3.05  --prep_sem_filter_out                   false
% 14.78/3.05  --pred_elim                             false
% 14.78/3.05  --res_sim_input                         true
% 14.78/3.05  --eq_ax_congr_red                       true
% 14.78/3.05  --pure_diseq_elim                       true
% 14.78/3.05  --brand_transform                       false
% 14.78/3.05  --non_eq_to_eq                          false
% 14.78/3.05  --prep_def_merge                        true
% 14.78/3.05  --prep_def_merge_prop_impl              false
% 14.78/3.05  --prep_def_merge_mbd                    true
% 14.78/3.05  --prep_def_merge_tr_red                 false
% 14.78/3.05  --prep_def_merge_tr_cl                  false
% 14.78/3.05  --smt_preprocessing                     true
% 14.78/3.05  --smt_ac_axioms                         fast
% 14.78/3.05  --preprocessed_out                      false
% 14.78/3.05  --preprocessed_stats                    false
% 14.78/3.05  
% 14.78/3.05  ------ Abstraction refinement Options
% 14.78/3.05  
% 14.78/3.05  --abstr_ref                             []
% 14.78/3.05  --abstr_ref_prep                        false
% 14.78/3.05  --abstr_ref_until_sat                   false
% 14.78/3.05  --abstr_ref_sig_restrict                funpre
% 14.78/3.05  --abstr_ref_af_restrict_to_split_sk     false
% 14.78/3.05  --abstr_ref_under                       []
% 14.78/3.05  
% 14.78/3.05  ------ SAT Options
% 14.78/3.05  
% 14.78/3.05  --sat_mode                              false
% 14.78/3.05  --sat_fm_restart_options                ""
% 14.78/3.05  --sat_gr_def                            false
% 14.78/3.05  --sat_epr_types                         true
% 14.78/3.05  --sat_non_cyclic_types                  false
% 14.78/3.05  --sat_finite_models                     false
% 14.78/3.05  --sat_fm_lemmas                         false
% 14.78/3.05  --sat_fm_prep                           false
% 14.78/3.05  --sat_fm_uc_incr                        true
% 14.78/3.05  --sat_out_model                         small
% 14.78/3.05  --sat_out_clauses                       false
% 14.78/3.05  
% 14.78/3.05  ------ QBF Options
% 14.78/3.05  
% 14.78/3.05  --qbf_mode                              false
% 14.78/3.05  --qbf_elim_univ                         false
% 14.78/3.05  --qbf_dom_inst                          none
% 14.78/3.05  --qbf_dom_pre_inst                      false
% 14.78/3.05  --qbf_sk_in                             false
% 14.78/3.05  --qbf_pred_elim                         true
% 14.78/3.05  --qbf_split                             512
% 14.78/3.05  
% 14.78/3.05  ------ BMC1 Options
% 14.78/3.05  
% 14.78/3.05  --bmc1_incremental                      false
% 14.78/3.05  --bmc1_axioms                           reachable_all
% 14.78/3.05  --bmc1_min_bound                        0
% 14.78/3.05  --bmc1_max_bound                        -1
% 14.78/3.05  --bmc1_max_bound_default                -1
% 14.78/3.05  --bmc1_symbol_reachability              true
% 14.78/3.05  --bmc1_property_lemmas                  false
% 14.78/3.05  --bmc1_k_induction                      false
% 14.78/3.05  --bmc1_non_equiv_states                 false
% 14.78/3.05  --bmc1_deadlock                         false
% 14.78/3.05  --bmc1_ucm                              false
% 14.78/3.05  --bmc1_add_unsat_core                   none
% 14.78/3.05  --bmc1_unsat_core_children              false
% 14.78/3.05  --bmc1_unsat_core_extrapolate_axioms    false
% 14.78/3.05  --bmc1_out_stat                         full
% 14.78/3.05  --bmc1_ground_init                      false
% 14.78/3.05  --bmc1_pre_inst_next_state              false
% 14.78/3.05  --bmc1_pre_inst_state                   false
% 14.78/3.05  --bmc1_pre_inst_reach_state             false
% 14.78/3.05  --bmc1_out_unsat_core                   false
% 14.78/3.05  --bmc1_aig_witness_out                  false
% 14.78/3.05  --bmc1_verbose                          false
% 14.78/3.05  --bmc1_dump_clauses_tptp                false
% 14.78/3.05  --bmc1_dump_unsat_core_tptp             false
% 14.78/3.05  --bmc1_dump_file                        -
% 14.78/3.05  --bmc1_ucm_expand_uc_limit              128
% 14.78/3.05  --bmc1_ucm_n_expand_iterations          6
% 14.78/3.05  --bmc1_ucm_extend_mode                  1
% 14.78/3.05  --bmc1_ucm_init_mode                    2
% 14.78/3.05  --bmc1_ucm_cone_mode                    none
% 14.78/3.05  --bmc1_ucm_reduced_relation_type        0
% 14.78/3.05  --bmc1_ucm_relax_model                  4
% 14.78/3.05  --bmc1_ucm_full_tr_after_sat            true
% 14.78/3.05  --bmc1_ucm_expand_neg_assumptions       false
% 14.78/3.05  --bmc1_ucm_layered_model                none
% 14.78/3.05  --bmc1_ucm_max_lemma_size               10
% 14.78/3.05  
% 14.78/3.05  ------ AIG Options
% 14.78/3.05  
% 14.78/3.05  --aig_mode                              false
% 14.78/3.05  
% 14.78/3.05  ------ Instantiation Options
% 14.78/3.05  
% 14.78/3.05  --instantiation_flag                    true
% 14.78/3.05  --inst_sos_flag                         false
% 14.78/3.05  --inst_sos_phase                        true
% 14.78/3.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.78/3.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.78/3.05  --inst_lit_sel_side                     num_symb
% 14.78/3.05  --inst_solver_per_active                1400
% 14.78/3.05  --inst_solver_calls_frac                1.
% 14.78/3.05  --inst_passive_queue_type               priority_queues
% 14.78/3.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.78/3.05  --inst_passive_queues_freq              [25;2]
% 14.78/3.05  --inst_dismatching                      true
% 14.78/3.05  --inst_eager_unprocessed_to_passive     true
% 14.78/3.05  --inst_prop_sim_given                   true
% 14.78/3.05  --inst_prop_sim_new                     false
% 14.78/3.05  --inst_subs_new                         false
% 14.78/3.05  --inst_eq_res_simp                      false
% 14.78/3.05  --inst_subs_given                       false
% 14.78/3.05  --inst_orphan_elimination               true
% 14.78/3.05  --inst_learning_loop_flag               true
% 14.78/3.05  --inst_learning_start                   3000
% 14.78/3.05  --inst_learning_factor                  2
% 14.78/3.05  --inst_start_prop_sim_after_learn       3
% 14.78/3.05  --inst_sel_renew                        solver
% 14.78/3.05  --inst_lit_activity_flag                true
% 14.78/3.05  --inst_restr_to_given                   false
% 14.78/3.05  --inst_activity_threshold               500
% 14.78/3.05  --inst_out_proof                        true
% 14.78/3.05  
% 14.78/3.05  ------ Resolution Options
% 14.78/3.05  
% 14.78/3.05  --resolution_flag                       true
% 14.78/3.05  --res_lit_sel                           adaptive
% 14.78/3.05  --res_lit_sel_side                      none
% 14.78/3.05  --res_ordering                          kbo
% 14.78/3.05  --res_to_prop_solver                    active
% 14.78/3.05  --res_prop_simpl_new                    false
% 14.78/3.05  --res_prop_simpl_given                  true
% 14.78/3.05  --res_passive_queue_type                priority_queues
% 14.78/3.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.78/3.05  --res_passive_queues_freq               [15;5]
% 14.78/3.05  --res_forward_subs                      full
% 14.78/3.05  --res_backward_subs                     full
% 14.78/3.05  --res_forward_subs_resolution           true
% 14.78/3.05  --res_backward_subs_resolution          true
% 14.78/3.05  --res_orphan_elimination                true
% 14.78/3.05  --res_time_limit                        2.
% 14.78/3.05  --res_out_proof                         true
% 14.78/3.05  
% 14.78/3.05  ------ Superposition Options
% 14.78/3.05  
% 14.78/3.05  --superposition_flag                    true
% 14.78/3.05  --sup_passive_queue_type                priority_queues
% 14.78/3.05  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.78/3.05  --sup_passive_queues_freq               [1;4]
% 14.78/3.05  --demod_completeness_check              fast
% 14.78/3.05  --demod_use_ground                      true
% 14.78/3.05  --sup_to_prop_solver                    passive
% 14.78/3.05  --sup_prop_simpl_new                    true
% 14.78/3.05  --sup_prop_simpl_given                  true
% 14.78/3.05  --sup_fun_splitting                     false
% 14.78/3.05  --sup_smt_interval                      50000
% 14.78/3.05  
% 14.78/3.05  ------ Superposition Simplification Setup
% 14.78/3.05  
% 14.78/3.05  --sup_indices_passive                   []
% 14.78/3.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_full_triv                         [TrivRules;PropSubs]
% 14.78/3.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_full_bw                           [BwDemod]
% 14.78/3.05  --sup_immed_triv                        [TrivRules]
% 14.78/3.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.78/3.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_immed_bw_main                     []
% 14.78/3.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.78/3.05  --sup_input_triv                        [Unflattening;TrivRules]
% 14.78/3.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.78/3.05  
% 14.78/3.05  ------ Combination Options
% 14.78/3.05  
% 14.78/3.05  --comb_res_mult                         3
% 14.78/3.05  --comb_sup_mult                         2
% 14.78/3.05  --comb_inst_mult                        10
% 14.78/3.05  
% 14.78/3.05  ------ Debug Options
% 14.78/3.05  
% 14.78/3.05  --dbg_backtrace                         false
% 14.78/3.05  --dbg_dump_prop_clauses                 false
% 14.78/3.05  --dbg_dump_prop_clauses_file            -
% 14.78/3.05  --dbg_out_stat                          false
% 14.78/3.05  ------ Parsing...
% 14.78/3.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 14.78/3.05  
% 14.78/3.05  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 14.78/3.05  
% 14.78/3.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 14.78/3.05  ------ Proving...
% 14.78/3.05  ------ Problem Properties 
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  clauses                                 29
% 14.78/3.05  conjectures                             14
% 14.78/3.05  EPR                                     20
% 14.78/3.05  Horn                                    13
% 14.78/3.05  unary                                   10
% 14.78/3.05  binary                                  2
% 14.78/3.05  lits                                    153
% 14.78/3.05  lits eq                                 0
% 14.78/3.05  fd_pure                                 0
% 14.78/3.05  fd_pseudo                               0
% 14.78/3.05  fd_cond                                 0
% 14.78/3.05  fd_pseudo_cond                          0
% 14.78/3.05  AC symbols                              0
% 14.78/3.05  
% 14.78/3.05  ------ Input Options Time Limit: Unbounded
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  ------ 
% 14.78/3.05  Current options:
% 14.78/3.05  ------ 
% 14.78/3.05  
% 14.78/3.05  ------ Input Options
% 14.78/3.05  
% 14.78/3.05  --out_options                           all
% 14.78/3.05  --tptp_safe_out                         true
% 14.78/3.05  --problem_path                          ""
% 14.78/3.05  --include_path                          ""
% 14.78/3.05  --clausifier                            res/vclausify_rel
% 14.78/3.05  --clausifier_options                    --mode clausify
% 14.78/3.05  --stdin                                 false
% 14.78/3.05  --stats_out                             sel
% 14.78/3.05  
% 14.78/3.05  ------ General Options
% 14.78/3.05  
% 14.78/3.05  --fof                                   false
% 14.78/3.05  --time_out_real                         604.98
% 14.78/3.05  --time_out_virtual                      -1.
% 14.78/3.05  --symbol_type_check                     false
% 14.78/3.05  --clausify_out                          false
% 14.78/3.05  --sig_cnt_out                           false
% 14.78/3.05  --trig_cnt_out                          false
% 14.78/3.05  --trig_cnt_out_tolerance                1.
% 14.78/3.05  --trig_cnt_out_sk_spl                   false
% 14.78/3.05  --abstr_cl_out                          false
% 14.78/3.05  
% 14.78/3.05  ------ Global Options
% 14.78/3.05  
% 14.78/3.05  --schedule                              none
% 14.78/3.05  --add_important_lit                     false
% 14.78/3.05  --prop_solver_per_cl                    1000
% 14.78/3.05  --min_unsat_core                        false
% 14.78/3.05  --soft_assumptions                      false
% 14.78/3.05  --soft_lemma_size                       3
% 14.78/3.05  --prop_impl_unit_size                   0
% 14.78/3.05  --prop_impl_unit                        []
% 14.78/3.05  --share_sel_clauses                     true
% 14.78/3.05  --reset_solvers                         false
% 14.78/3.05  --bc_imp_inh                            [conj_cone]
% 14.78/3.05  --conj_cone_tolerance                   3.
% 14.78/3.05  --extra_neg_conj                        none
% 14.78/3.05  --large_theory_mode                     true
% 14.78/3.05  --prolific_symb_bound                   200
% 14.78/3.05  --lt_threshold                          2000
% 14.78/3.05  --clause_weak_htbl                      true
% 14.78/3.05  --gc_record_bc_elim                     false
% 14.78/3.05  
% 14.78/3.05  ------ Preprocessing Options
% 14.78/3.05  
% 14.78/3.05  --preprocessing_flag                    true
% 14.78/3.05  --time_out_prep_mult                    0.1
% 14.78/3.05  --splitting_mode                        input
% 14.78/3.05  --splitting_grd                         true
% 14.78/3.05  --splitting_cvd                         false
% 14.78/3.05  --splitting_cvd_svl                     false
% 14.78/3.05  --splitting_nvd                         32
% 14.78/3.05  --sub_typing                            true
% 14.78/3.05  --prep_gs_sim                           false
% 14.78/3.05  --prep_unflatten                        true
% 14.78/3.05  --prep_res_sim                          true
% 14.78/3.05  --prep_upred                            true
% 14.78/3.05  --prep_sem_filter                       exhaustive
% 14.78/3.05  --prep_sem_filter_out                   false
% 14.78/3.05  --pred_elim                             false
% 14.78/3.05  --res_sim_input                         true
% 14.78/3.05  --eq_ax_congr_red                       true
% 14.78/3.05  --pure_diseq_elim                       true
% 14.78/3.05  --brand_transform                       false
% 14.78/3.05  --non_eq_to_eq                          false
% 14.78/3.05  --prep_def_merge                        true
% 14.78/3.05  --prep_def_merge_prop_impl              false
% 14.78/3.05  --prep_def_merge_mbd                    true
% 14.78/3.05  --prep_def_merge_tr_red                 false
% 14.78/3.05  --prep_def_merge_tr_cl                  false
% 14.78/3.05  --smt_preprocessing                     true
% 14.78/3.05  --smt_ac_axioms                         fast
% 14.78/3.05  --preprocessed_out                      false
% 14.78/3.05  --preprocessed_stats                    false
% 14.78/3.05  
% 14.78/3.05  ------ Abstraction refinement Options
% 14.78/3.05  
% 14.78/3.05  --abstr_ref                             []
% 14.78/3.05  --abstr_ref_prep                        false
% 14.78/3.05  --abstr_ref_until_sat                   false
% 14.78/3.05  --abstr_ref_sig_restrict                funpre
% 14.78/3.05  --abstr_ref_af_restrict_to_split_sk     false
% 14.78/3.05  --abstr_ref_under                       []
% 14.78/3.05  
% 14.78/3.05  ------ SAT Options
% 14.78/3.05  
% 14.78/3.05  --sat_mode                              false
% 14.78/3.05  --sat_fm_restart_options                ""
% 14.78/3.05  --sat_gr_def                            false
% 14.78/3.05  --sat_epr_types                         true
% 14.78/3.05  --sat_non_cyclic_types                  false
% 14.78/3.05  --sat_finite_models                     false
% 14.78/3.05  --sat_fm_lemmas                         false
% 14.78/3.05  --sat_fm_prep                           false
% 14.78/3.05  --sat_fm_uc_incr                        true
% 14.78/3.05  --sat_out_model                         small
% 14.78/3.05  --sat_out_clauses                       false
% 14.78/3.05  
% 14.78/3.05  ------ QBF Options
% 14.78/3.05  
% 14.78/3.05  --qbf_mode                              false
% 14.78/3.05  --qbf_elim_univ                         false
% 14.78/3.05  --qbf_dom_inst                          none
% 14.78/3.05  --qbf_dom_pre_inst                      false
% 14.78/3.05  --qbf_sk_in                             false
% 14.78/3.05  --qbf_pred_elim                         true
% 14.78/3.05  --qbf_split                             512
% 14.78/3.05  
% 14.78/3.05  ------ BMC1 Options
% 14.78/3.05  
% 14.78/3.05  --bmc1_incremental                      false
% 14.78/3.05  --bmc1_axioms                           reachable_all
% 14.78/3.05  --bmc1_min_bound                        0
% 14.78/3.05  --bmc1_max_bound                        -1
% 14.78/3.05  --bmc1_max_bound_default                -1
% 14.78/3.05  --bmc1_symbol_reachability              true
% 14.78/3.05  --bmc1_property_lemmas                  false
% 14.78/3.05  --bmc1_k_induction                      false
% 14.78/3.05  --bmc1_non_equiv_states                 false
% 14.78/3.05  --bmc1_deadlock                         false
% 14.78/3.05  --bmc1_ucm                              false
% 14.78/3.05  --bmc1_add_unsat_core                   none
% 14.78/3.05  --bmc1_unsat_core_children              false
% 14.78/3.05  --bmc1_unsat_core_extrapolate_axioms    false
% 14.78/3.05  --bmc1_out_stat                         full
% 14.78/3.05  --bmc1_ground_init                      false
% 14.78/3.05  --bmc1_pre_inst_next_state              false
% 14.78/3.05  --bmc1_pre_inst_state                   false
% 14.78/3.05  --bmc1_pre_inst_reach_state             false
% 14.78/3.05  --bmc1_out_unsat_core                   false
% 14.78/3.05  --bmc1_aig_witness_out                  false
% 14.78/3.05  --bmc1_verbose                          false
% 14.78/3.05  --bmc1_dump_clauses_tptp                false
% 14.78/3.05  --bmc1_dump_unsat_core_tptp             false
% 14.78/3.05  --bmc1_dump_file                        -
% 14.78/3.05  --bmc1_ucm_expand_uc_limit              128
% 14.78/3.05  --bmc1_ucm_n_expand_iterations          6
% 14.78/3.05  --bmc1_ucm_extend_mode                  1
% 14.78/3.05  --bmc1_ucm_init_mode                    2
% 14.78/3.05  --bmc1_ucm_cone_mode                    none
% 14.78/3.05  --bmc1_ucm_reduced_relation_type        0
% 14.78/3.05  --bmc1_ucm_relax_model                  4
% 14.78/3.05  --bmc1_ucm_full_tr_after_sat            true
% 14.78/3.05  --bmc1_ucm_expand_neg_assumptions       false
% 14.78/3.05  --bmc1_ucm_layered_model                none
% 14.78/3.05  --bmc1_ucm_max_lemma_size               10
% 14.78/3.05  
% 14.78/3.05  ------ AIG Options
% 14.78/3.05  
% 14.78/3.05  --aig_mode                              false
% 14.78/3.05  
% 14.78/3.05  ------ Instantiation Options
% 14.78/3.05  
% 14.78/3.05  --instantiation_flag                    true
% 14.78/3.05  --inst_sos_flag                         false
% 14.78/3.05  --inst_sos_phase                        true
% 14.78/3.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 14.78/3.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 14.78/3.05  --inst_lit_sel_side                     num_symb
% 14.78/3.05  --inst_solver_per_active                1400
% 14.78/3.05  --inst_solver_calls_frac                1.
% 14.78/3.05  --inst_passive_queue_type               priority_queues
% 14.78/3.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 14.78/3.05  --inst_passive_queues_freq              [25;2]
% 14.78/3.05  --inst_dismatching                      true
% 14.78/3.05  --inst_eager_unprocessed_to_passive     true
% 14.78/3.05  --inst_prop_sim_given                   true
% 14.78/3.05  --inst_prop_sim_new                     false
% 14.78/3.05  --inst_subs_new                         false
% 14.78/3.05  --inst_eq_res_simp                      false
% 14.78/3.05  --inst_subs_given                       false
% 14.78/3.05  --inst_orphan_elimination               true
% 14.78/3.05  --inst_learning_loop_flag               true
% 14.78/3.05  --inst_learning_start                   3000
% 14.78/3.05  --inst_learning_factor                  2
% 14.78/3.05  --inst_start_prop_sim_after_learn       3
% 14.78/3.05  --inst_sel_renew                        solver
% 14.78/3.05  --inst_lit_activity_flag                true
% 14.78/3.05  --inst_restr_to_given                   false
% 14.78/3.05  --inst_activity_threshold               500
% 14.78/3.05  --inst_out_proof                        true
% 14.78/3.05  
% 14.78/3.05  ------ Resolution Options
% 14.78/3.05  
% 14.78/3.05  --resolution_flag                       true
% 14.78/3.05  --res_lit_sel                           adaptive
% 14.78/3.05  --res_lit_sel_side                      none
% 14.78/3.05  --res_ordering                          kbo
% 14.78/3.05  --res_to_prop_solver                    active
% 14.78/3.05  --res_prop_simpl_new                    false
% 14.78/3.05  --res_prop_simpl_given                  true
% 14.78/3.05  --res_passive_queue_type                priority_queues
% 14.78/3.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 14.78/3.05  --res_passive_queues_freq               [15;5]
% 14.78/3.05  --res_forward_subs                      full
% 14.78/3.05  --res_backward_subs                     full
% 14.78/3.05  --res_forward_subs_resolution           true
% 14.78/3.05  --res_backward_subs_resolution          true
% 14.78/3.05  --res_orphan_elimination                true
% 14.78/3.05  --res_time_limit                        2.
% 14.78/3.05  --res_out_proof                         true
% 14.78/3.05  
% 14.78/3.05  ------ Superposition Options
% 14.78/3.05  
% 14.78/3.05  --superposition_flag                    true
% 14.78/3.05  --sup_passive_queue_type                priority_queues
% 14.78/3.05  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 14.78/3.05  --sup_passive_queues_freq               [1;4]
% 14.78/3.05  --demod_completeness_check              fast
% 14.78/3.05  --demod_use_ground                      true
% 14.78/3.05  --sup_to_prop_solver                    passive
% 14.78/3.05  --sup_prop_simpl_new                    true
% 14.78/3.05  --sup_prop_simpl_given                  true
% 14.78/3.05  --sup_fun_splitting                     false
% 14.78/3.05  --sup_smt_interval                      50000
% 14.78/3.05  
% 14.78/3.05  ------ Superposition Simplification Setup
% 14.78/3.05  
% 14.78/3.05  --sup_indices_passive                   []
% 14.78/3.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 14.78/3.05  --sup_full_triv                         [TrivRules;PropSubs]
% 14.78/3.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_full_bw                           [BwDemod]
% 14.78/3.05  --sup_immed_triv                        [TrivRules]
% 14.78/3.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 14.78/3.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_immed_bw_main                     []
% 14.78/3.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.78/3.05  --sup_input_triv                        [Unflattening;TrivRules]
% 14.78/3.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 14.78/3.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 14.78/3.05  
% 14.78/3.05  ------ Combination Options
% 14.78/3.05  
% 14.78/3.05  --comb_res_mult                         3
% 14.78/3.05  --comb_sup_mult                         2
% 14.78/3.05  --comb_inst_mult                        10
% 14.78/3.05  
% 14.78/3.05  ------ Debug Options
% 14.78/3.05  
% 14.78/3.05  --dbg_backtrace                         false
% 14.78/3.05  --dbg_dump_prop_clauses                 false
% 14.78/3.05  --dbg_dump_prop_clauses_file            -
% 14.78/3.05  --dbg_out_stat                          false
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  ------ Proving...
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  % SZS status Theorem for theBenchmark.p
% 14.78/3.05  
% 14.78/3.05  % SZS output start CNFRefutation for theBenchmark.p
% 14.78/3.05  
% 14.78/3.05  fof(f6,axiom,(
% 14.78/3.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f20,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f6])).
% 14.78/3.05  
% 14.78/3.05  fof(f21,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f20])).
% 14.78/3.05  
% 14.78/3.05  fof(f42,plain,(
% 14.78/3.05    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X3,X1) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f21])).
% 14.78/3.05  
% 14.78/3.05  fof(f8,axiom,(
% 14.78/3.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3))) & (m1_pre_topc(X1,X3) => m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)))))))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f24,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f8])).
% 14.78/3.05  
% 14.78/3.05  fof(f25,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3)) & (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f24])).
% 14.78/3.05  
% 14.78/3.05  fof(f46,plain,(
% 14.78/3.05    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X2)) | ~m1_pre_topc(X1,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f25])).
% 14.78/3.05  
% 14.78/3.05  fof(f40,plain,(
% 14.78/3.05    ( ! [X2,X0,X3,X1] : (r1_tsep_1(X1,X3) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f21])).
% 14.78/3.05  
% 14.78/3.05  fof(f47,plain,(
% 14.78/3.05    ( ! [X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X1,X3)) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f25])).
% 14.78/3.05  
% 14.78/3.05  fof(f7,axiom,(
% 14.78/3.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1))))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f22,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f7])).
% 14.78/3.05  
% 14.78/3.05  fof(f23,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) & m1_pre_topc(k2_tsep_1(X0,X1,X2),X1)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f22])).
% 14.78/3.05  
% 14.78/3.05  fof(f45,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X2) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f23])).
% 14.78/3.05  
% 14.78/3.05  fof(f5,axiom,(
% 14.78/3.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f18,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f5])).
% 14.78/3.05  
% 14.78/3.05  fof(f19,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f18])).
% 14.78/3.05  
% 14.78/3.05  fof(f39,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f19])).
% 14.78/3.05  
% 14.78/3.05  fof(f2,axiom,(
% 14.78/3.05    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f13,plain,(
% 14.78/3.05    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 14.78/3.05    inference(ennf_transformation,[],[f2])).
% 14.78/3.05  
% 14.78/3.05  fof(f34,plain,(
% 14.78/3.05    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f13])).
% 14.78/3.05  
% 14.78/3.05  fof(f3,axiom,(
% 14.78/3.05    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f11,plain,(
% 14.78/3.05    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 14.78/3.05    inference(pure_predicate_removal,[],[f3])).
% 14.78/3.05  
% 14.78/3.05  fof(f14,plain,(
% 14.78/3.05    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f11])).
% 14.78/3.05  
% 14.78/3.05  fof(f15,plain,(
% 14.78/3.05    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f14])).
% 14.78/3.05  
% 14.78/3.05  fof(f35,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f15])).
% 14.78/3.05  
% 14.78/3.05  fof(f9,conjecture,(
% 14.78/3.05    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f10,negated_conjecture,(
% 14.78/3.05    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 14.78/3.05    inference(negated_conjecture,[],[f9])).
% 14.78/3.05  
% 14.78/3.05  fof(f26,plain,(
% 14.78/3.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f10])).
% 14.78/3.05  
% 14.78/3.05  fof(f27,plain,(
% 14.78/3.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f26])).
% 14.78/3.05  
% 14.78/3.05  fof(f31,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((((r1_tsep_1(k2_tsep_1(X0,sK3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,sK3),X2)) & m1_pre_topc(X2,sK3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,sK3),X1) | r1_tsep_1(k2_tsep_1(X0,sK3,X2),X1)) & m1_pre_topc(X1,sK3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 14.78/3.05    introduced(choice_axiom,[])).
% 14.78/3.05  
% 14.78/3.05  fof(f30,plain,(
% 14.78/3.05    ( ! [X0,X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),sK2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),sK2)) & m1_pre_topc(sK2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,sK2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,sK2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,sK2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 14.78/3.05    introduced(choice_axiom,[])).
% 14.78/3.05  
% 14.78/3.05  fof(f29,plain,(
% 14.78/3.05    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,sK1),X2) | r1_tsep_1(k2_tsep_1(X0,sK1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),sK1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),sK1)) & m1_pre_topc(sK1,X3))) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 14.78/3.05    introduced(choice_axiom,[])).
% 14.78/3.05  
% 14.78/3.05  fof(f28,plain,(
% 14.78/3.05    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((((r1_tsep_1(k2_tsep_1(sK0,X3,X1),X2) | r1_tsep_1(k2_tsep_1(sK0,X1,X3),X2)) & m1_pre_topc(X2,X3)) | ((r1_tsep_1(k2_tsep_1(sK0,X2,X3),X1) | r1_tsep_1(k2_tsep_1(sK0,X3,X2),X1)) & m1_pre_topc(X1,X3))) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 14.78/3.05    introduced(choice_axiom,[])).
% 14.78/3.05  
% 14.78/3.05  fof(f32,plain,(
% 14.78/3.05    ((((((r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)) & m1_pre_topc(sK2,sK3)) | ((r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)) & m1_pre_topc(sK1,sK3))) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 14.78/3.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f27,f31,f30,f29,f28])).
% 14.78/3.05  
% 14.78/3.05  fof(f59,plain,(
% 14.78/3.05    m1_pre_topc(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f48,plain,(
% 14.78/3.05    ~v2_struct_0(sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f49,plain,(
% 14.78/3.05    v2_pre_topc(sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f50,plain,(
% 14.78/3.05    l1_pre_topc(sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f51,plain,(
% 14.78/3.05    ~v2_struct_0(sK1)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f52,plain,(
% 14.78/3.05    m1_pre_topc(sK1,sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f53,plain,(
% 14.78/3.05    ~v2_struct_0(sK2)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f54,plain,(
% 14.78/3.05    m1_pre_topc(sK2,sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f55,plain,(
% 14.78/3.05    ~v2_struct_0(sK3)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f56,plain,(
% 14.78/3.05    m1_pre_topc(sK3,sK0)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f57,plain,(
% 14.78/3.05    ~r1_tsep_1(sK1,sK2)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f58,plain,(
% 14.78/3.05    m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f1,axiom,(
% 14.78/3.05    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f12,plain,(
% 14.78/3.05    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 14.78/3.05    inference(ennf_transformation,[],[f1])).
% 14.78/3.05  
% 14.78/3.05  fof(f33,plain,(
% 14.78/3.05    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f12])).
% 14.78/3.05  
% 14.78/3.05  fof(f36,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f15])).
% 14.78/3.05  
% 14.78/3.05  fof(f4,axiom,(
% 14.78/3.05    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 14.78/3.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 14.78/3.05  
% 14.78/3.05  fof(f16,plain,(
% 14.78/3.05    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 14.78/3.05    inference(ennf_transformation,[],[f4])).
% 14.78/3.05  
% 14.78/3.05  fof(f17,plain,(
% 14.78/3.05    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 14.78/3.05    inference(flattening,[],[f16])).
% 14.78/3.05  
% 14.78/3.05  fof(f37,plain,(
% 14.78/3.05    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f17])).
% 14.78/3.05  
% 14.78/3.05  fof(f38,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (~r1_tsep_1(X1,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f19])).
% 14.78/3.05  
% 14.78/3.05  fof(f44,plain,(
% 14.78/3.05    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 14.78/3.05    inference(cnf_transformation,[],[f23])).
% 14.78/3.05  
% 14.78/3.05  fof(f61,plain,(
% 14.78/3.05    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  fof(f60,plain,(
% 14.78/3.05    r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2) | m1_pre_topc(sK1,sK3)),
% 14.78/3.05    inference(cnf_transformation,[],[f32])).
% 14.78/3.05  
% 14.78/3.05  cnf(c_8,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,X1)
% 14.78/3.05      | r1_tsep_1(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X2,X3)
% 14.78/3.05      | ~ m1_pre_topc(X0,X3)
% 14.78/3.05      | ~ m1_pre_topc(X2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X1,X3)
% 14.78/3.05      | ~ v2_pre_topc(X3)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | ~ l1_pre_topc(X3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f42]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_893,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,sK2)
% 14.78/3.05      | r1_tsep_1(sK2,X1)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(X1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_8]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11765,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 14.78/3.05      | r1_tsep_1(sK2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_893]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_28475,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 14.78/3.05      | r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_11765]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_14,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X3,X2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X3)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X3,X1))
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f46]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2457,plain,
% 14.78/3.05      ( r1_tsep_1(sK2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X1,sK2,X0),k2_tsep_1(X1,sK3,X0))
% 14.78/3.05      | ~ m1_pre_topc(sK2,X1)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK3,X1)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_14]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_28472,plain,
% 14.78/3.05      ( r1_tsep_1(sK2,sK1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2457]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_10,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,X1)
% 14.78/3.05      | r1_tsep_1(X2,X1)
% 14.78/3.05      | ~ m1_pre_topc(X2,X3)
% 14.78/3.05      | ~ m1_pre_topc(X0,X3)
% 14.78/3.05      | ~ m1_pre_topc(X2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X1,X3)
% 14.78/3.05      | ~ v2_pre_topc(X3)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | ~ l1_pre_topc(X3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f40]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_958,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,sK2)
% 14.78/3.05      | r1_tsep_1(X1,sK2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(X1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_10]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2684,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK2)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_958]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_28463,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2684]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_13,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X3,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X3)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X2,X0,X1),k2_tsep_1(X2,X0,X3))
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f47]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2444,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X1,X0,sK2),k2_tsep_1(X1,X0,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK2,X1)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK3,X1)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_13]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_28462,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,sK2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2444]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X2,X0,X1),X1)
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f45]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_5,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f39]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_3216,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X1),X3)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X3,X1)
% 14.78/3.05      | ~ m1_pre_topc(X3,k2_tsep_1(X2,X0,X1))
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(X2,X0,X1))
% 14.78/3.05      | ~ l1_pre_topc(X1)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,X1) | ~ l1_pre_topc(X1) | l1_pre_topc(X0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f34]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_3,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X2,X1)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(X1,X0,X2))
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(cnf_transformation,[],[f35]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11486,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X1),X3)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X3,X1)
% 14.78/3.05      | ~ m1_pre_topc(X3,k2_tsep_1(X2,X0,X1))
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(forward_subsumption_resolution,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_3216,c_1,c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_17,negated_conjecture,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | m1_pre_topc(sK2,sK3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f59]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11726,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | r1_tsep_1(sK2,sK3)
% 14.78/3.05      | m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK3)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_11486,c_17]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_28,negated_conjecture,
% 14.78/3.05      ( ~ v2_struct_0(sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f48]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_27,negated_conjecture,
% 14.78/3.05      ( v2_pre_topc(sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f49]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_26,negated_conjecture,
% 14.78/3.05      ( l1_pre_topc(sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f50]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_25,negated_conjecture,
% 14.78/3.05      ( ~ v2_struct_0(sK1) ),
% 14.78/3.05      inference(cnf_transformation,[],[f51]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_24,negated_conjecture,
% 14.78/3.05      ( m1_pre_topc(sK1,sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f52]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_23,negated_conjecture,
% 14.78/3.05      ( ~ v2_struct_0(sK2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f53]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_22,negated_conjecture,
% 14.78/3.05      ( m1_pre_topc(sK2,sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f54]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_21,negated_conjecture,
% 14.78/3.05      ( ~ v2_struct_0(sK3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f55]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_20,negated_conjecture,
% 14.78/3.05      ( m1_pre_topc(sK3,sK0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f56]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_19,negated_conjecture,
% 14.78/3.05      ( ~ r1_tsep_1(sK1,sK2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f57]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_18,negated_conjecture,
% 14.78/3.05      ( m1_pre_topc(sK2,sK3) | m1_pre_topc(sK1,sK3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f58]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_0,plain,
% 14.78/3.05      ( ~ l1_pre_topc(X0) | l1_struct_0(X0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f33]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_964,plain,
% 14.78/3.05      ( ~ l1_pre_topc(sK1) | l1_struct_0(sK1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_0]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X2,X1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X1,X0,X2),X1)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(cnf_transformation,[],[f36]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_762,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_975,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_762]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_772,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1015,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_772]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_848,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK1)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_11]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1042,plain,
% 14.78/3.05      ( r1_tsep_1(sK2,sK1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_848]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1117,plain,
% 14.78/3.05      ( l1_pre_topc(sK1) | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_1,c_24]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_4,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,X1)
% 14.78/3.05      | r1_tsep_1(X1,X0)
% 14.78/3.05      | ~ l1_struct_0(X1)
% 14.78/3.05      | ~ l1_struct_0(X0) ),
% 14.78/3.05      inference(cnf_transformation,[],[f37]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2376,plain,
% 14.78/3.05      ( ~ r1_tsep_1(sK2,sK1)
% 14.78/3.05      | r1_tsep_1(sK1,sK2)
% 14.78/3.05      | ~ l1_struct_0(sK2)
% 14.78/3.05      | ~ l1_struct_0(sK1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_4]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1115,plain,
% 14.78/3.05      ( l1_pre_topc(sK2) | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_1,c_22]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1921,plain,
% 14.78/3.05      ( l1_pre_topc(sK2) ),
% 14.78/3.05      inference(global_propositional_subsumption,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_1115,c_26]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2402,plain,
% 14.78/3.05      ( l1_struct_0(sK2) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_1921,c_0]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_3231,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_5230,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_6,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f38]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_7385,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(sK1,X0)
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_6]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_7387,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_7385]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1149,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X1,X0,sK1),k2_tsep_1(X1,X0,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK1,X1)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK3,X1)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_13]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_8139,plain,
% 14.78/3.05      ( r1_tsep_1(sK2,sK1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_1149]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_961,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,sK1)
% 14.78/3.05      | r1_tsep_1(X1,sK1)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(X1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_10]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2728,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_961]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_9623,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK1),sK1)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2728]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11735,plain,
% 14.78/3.05      ( m1_pre_topc(sK2,sK3) | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) ),
% 14.78/3.05      inference(global_propositional_subsumption,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_11726,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,
% 14.78/3.05                 c_19,c_18,c_17,c_964,c_975,c_1015,c_1042,c_1117,c_2376,
% 14.78/3.05                 c_2402,c_3231,c_5230,c_7387,c_8139,c_9623]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11736,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1) | m1_pre_topc(sK2,sK3) ),
% 14.78/3.05      inference(renaming,[status(thm)],[c_11735]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11753,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | m1_pre_topc(sK2,sK3)
% 14.78/3.05      | ~ l1_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | ~ l1_struct_0(sK1) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_11736,c_4]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_767,plain,
% 14.78/3.05      ( ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1003,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_767]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1009,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_767]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_12,plain,
% 14.78/3.05      ( r1_tsep_1(X0,X1)
% 14.78/3.05      | ~ m1_pre_topc(X0,X2)
% 14.78/3.05      | ~ m1_pre_topc(X1,X2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X2,X0,X1),X0)
% 14.78/3.05      | ~ v2_pre_topc(X2)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | ~ l1_pre_topc(X2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f44]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_863,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK2)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),X0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_12]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1089,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,sK2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_863]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2506,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(sK1,X0)
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_6]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2508,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2506]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_4005,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_5061,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1169,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X0,X1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(X1,sK1,X0),k2_tsep_1(X1,sK3,X0))
% 14.78/3.05      | ~ m1_pre_topc(sK1,X1)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK3,X1)
% 14.78/3.05      | ~ v2_pre_topc(X1)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | ~ l1_pre_topc(X1) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_14]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_8202,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,sK2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK3)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_1169]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2722,plain,
% 14.78/3.05      ( ~ r1_tsep_1(X0,sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_961]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11790,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK1)
% 14.78/3.05      | ~ r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK3,sK2))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2722]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_11960,plain,
% 14.78/3.05      ( m1_pre_topc(sK2,sK3) ),
% 14.78/3.05      inference(global_propositional_subsumption,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_11753,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,
% 14.78/3.05                 c_19,c_18,c_1003,c_1009,c_1089,c_2508,c_4005,c_5061,
% 14.78/3.05                 c_8202,c_11736,c_11790]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1244,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X3,X0)
% 14.78/3.05      | ~ m1_pre_topc(X3,k2_tsep_1(X0,X1,X2))
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(X0,X1,X2))
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_5,c_2]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_9068,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
% 14.78/3.05      | ~ m1_pre_topc(X1,X0)
% 14.78/3.05      | ~ m1_pre_topc(X2,X0)
% 14.78/3.05      | ~ m1_pre_topc(X3,X0)
% 14.78/3.05      | ~ m1_pre_topc(X3,k2_tsep_1(X0,X1,X2))
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(X1)
% 14.78/3.05      | v2_struct_0(X2)
% 14.78/3.05      | v2_struct_0(X3)
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(forward_subsumption_resolution,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_1244,c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_15,negated_conjecture,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK3),sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 14.78/3.05      inference(cnf_transformation,[],[f61]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_9434,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,k2_tsep_1(sK0,sK2,sK3))
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(resolution,[status(thm)],[c_9068,c_15]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_16,negated_conjecture,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2)
% 14.78/3.05      | m1_pre_topc(sK1,sK3) ),
% 14.78/3.05      inference(cnf_transformation,[],[f60]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_9674,plain,
% 14.78/3.05      ( r1_tsep_1(k2_tsep_1(sK0,sK1,sK3),sK2)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK2),sK1)
% 14.78/3.05      | r1_tsep_1(k2_tsep_1(sK0,sK3,sK1),sK2) ),
% 14.78/3.05      inference(global_propositional_subsumption,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_9434,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,
% 14.78/3.05                 c_19,c_16,c_15,c_964,c_975,c_1015,c_1042,c_1117,c_2376,
% 14.78/3.05                 c_2402,c_3231,c_5230,c_7387,c_8139,c_9623]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_7431,plain,
% 14.78/3.05      ( ~ r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,X0)
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_5]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_7433,plain,
% 14.78/3.05      ( ~ r1_tsep_1(sK2,k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK2,sK1))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_7431]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_5132,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK3,sK1))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_3517,plain,
% 14.78/3.05      ( ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | ~ v2_struct_0(k2_tsep_1(sK0,sK1,sK3))
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_3]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2317,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,X0)
% 14.78/3.05      | ~ v2_pre_topc(X0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | ~ l1_pre_topc(X0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_6]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_2319,plain,
% 14.78/3.05      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(k2_tsep_1(sK0,sK1,sK2))
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_2317]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_868,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK1)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK1),X0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_12]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1095,plain,
% 14.78/3.05      ( r1_tsep_1(sK2,sK1)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK1),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_868]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_843,plain,
% 14.78/3.05      ( r1_tsep_1(X0,sK2)
% 14.78/3.05      | ~ m1_pre_topc(X0,sK0)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,X0,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(X0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_11]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1036,plain,
% 14.78/3.05      ( r1_tsep_1(sK1,sK2)
% 14.78/3.05      | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK2)
% 14.78/3.05      | ~ m1_pre_topc(sK2,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ v2_pre_topc(sK0)
% 14.78/3.05      | v2_struct_0(sK2)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_843]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_1012,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK3,sK1),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_772]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(c_978,plain,
% 14.78/3.05      ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK3),sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK1,sK0)
% 14.78/3.05      | ~ m1_pre_topc(sK3,sK0)
% 14.78/3.05      | v2_struct_0(sK1)
% 14.78/3.05      | v2_struct_0(sK3)
% 14.78/3.05      | v2_struct_0(sK0)
% 14.78/3.05      | ~ l1_pre_topc(sK0) ),
% 14.78/3.05      inference(instantiation,[status(thm)],[c_762]) ).
% 14.78/3.05  
% 14.78/3.05  cnf(contradiction,plain,
% 14.78/3.05      ( $false ),
% 14.78/3.05      inference(minisat,
% 14.78/3.05                [status(thm)],
% 14.78/3.05                [c_28475,c_28472,c_28463,c_28462,c_11960,c_11790,c_9674,
% 14.78/3.05                 c_8202,c_7433,c_5230,c_5132,c_5061,c_4005,c_3517,c_2508,
% 14.78/3.05                 c_2402,c_2376,c_2319,c_1117,c_1095,c_1089,c_1036,c_1015,
% 14.78/3.05                 c_1012,c_1009,c_1003,c_978,c_964,c_16,c_19,c_20,c_21,
% 14.78/3.05                 c_22,c_23,c_24,c_25,c_26,c_27,c_28]) ).
% 14.78/3.05  
% 14.78/3.05  
% 14.78/3.05  % SZS output end CNFRefutation for theBenchmark.p
% 14.78/3.05  
% 14.78/3.05  ------                               Statistics
% 14.78/3.05  
% 14.78/3.05  ------ Selected
% 14.78/3.05  
% 14.78/3.05  total_time:                             2.134
% 14.78/3.05  
%------------------------------------------------------------------------------
