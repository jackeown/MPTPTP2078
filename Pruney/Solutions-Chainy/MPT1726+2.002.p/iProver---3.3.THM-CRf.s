%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:22:14 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  164 (1180 expanded)
%              Number of clauses        :  109 ( 235 expanded)
%              Number of leaves         :   12 ( 491 expanded)
%              Depth                    :   21
%              Number of atoms          : 1125 (18200 expanded)
%              Number of equality atoms :  113 ( 184 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   34 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
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
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
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
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f22])).

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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => ( ( r1_tsep_1(X4,X1)
                            & r1_tsep_1(X2,X3) )
                          | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                            & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => ( ( r1_tsep_1(X4,X1)
                              & r1_tsep_1(X2,X3) )
                            | ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                              & ~ r1_tsep_1(X2,X4) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
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

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ r1_tsep_1(X4,X1)
            | ~ r1_tsep_1(X2,X3) )
          & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
            | r1_tsep_1(X2,X4) )
          & m1_pre_topc(X3,X4)
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X4,X0)
          & ~ v2_struct_0(X4) )
     => ( ( ~ r1_tsep_1(sK4,X1)
          | ~ r1_tsep_1(X2,X3) )
        & ( r1_tsep_1(k2_tsep_1(X0,X2,sK4),k1_tsep_1(X0,X1,X3))
          | r1_tsep_1(X2,sK4) )
        & m1_pre_topc(X3,sK4)
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r1_tsep_1(X4,X1)
                | ~ r1_tsep_1(X2,X3) )
              & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                | r1_tsep_1(X2,X4) )
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X4,X0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ? [X4] :
            ( ( ~ r1_tsep_1(X4,X1)
              | ~ r1_tsep_1(X2,sK3) )
            & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,sK3))
              | r1_tsep_1(X2,X4) )
            & m1_pre_topc(sK3,X4)
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r1_tsep_1(X4,X1)
                    | ~ r1_tsep_1(X2,X3) )
                  & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                    | r1_tsep_1(X2,X4) )
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X4,X0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r1_tsep_1(X4,X1)
                  | ~ r1_tsep_1(sK2,X3) )
                & ( r1_tsep_1(k2_tsep_1(X0,sK2,X4),k1_tsep_1(X0,X1,X3))
                  | r1_tsep_1(sK2,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(X1,sK2)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r1_tsep_1(X4,sK1)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,sK1,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(sK1,X2)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r1_tsep_1(X4,X1)
                          | ~ r1_tsep_1(X2,X3) )
                        & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3))
                          | r1_tsep_1(X2,X4) )
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ( ~ r1_tsep_1(X4,X1)
                        | ~ r1_tsep_1(X2,X3) )
                      & ( r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
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

fof(f35,plain,
    ( ( ~ r1_tsep_1(sK4,sK1)
      | ~ r1_tsep_1(sK2,sK3) )
    & ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
      | r1_tsep_1(sK2,sK4) )
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f34,f33,f32,f31,f30])).

fof(f55,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f56,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

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
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) )
                      | ~ m1_pre_topc(X2,X3) )
                    & ( ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                        & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) )
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
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
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
    inference(cnf_transformation,[],[f27])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f62,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f67,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X3,X1)
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
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f60,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f63,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f64,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
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

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)
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
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f66,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_8,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_433,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_31])).

cnf(c_434,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_436,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_32,c_30])).

cnf(c_437,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_436])).

cnf(c_6892,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,sK1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_437])).

cnf(c_12098,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_6892])).

cnf(c_14,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_647,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_648,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_650,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_648,c_32,c_30])).

cnf(c_651,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_650])).

cnf(c_2423,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,X0,sK4),sK1)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK1,X0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_651])).

cnf(c_10586,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2423])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1775,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1779,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_979,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_980,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_979])).

cnf(c_984,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_980,c_32])).

cnf(c_985,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_984])).

cnf(c_1753,plain,
    ( k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_2485,plain,
    ( k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1779,c_1753])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2554,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2485,c_40])).

cnf(c_2555,plain,
    ( k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2554])).

cnf(c_2566,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1775,c_2555])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2615,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2566,c_36])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_332,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_333,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_337,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_32,c_30])).

cnf(c_338,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_1772,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_3022,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2615,c_1772])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_7784,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3022,c_36,c_37,c_40,c_41])).

cnf(c_19,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1784,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_6,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X0,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_503,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_31])).

cnf(c_504,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_506,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_504,c_32,c_30])).

cnf(c_507,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_506])).

cnf(c_1767,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_507])).

cnf(c_4606,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1767])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_42,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_43,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_929,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_30])).

cnf(c_930,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_929])).

cnf(c_934,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_930,c_32])).

cnf(c_935,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_934])).

cnf(c_3097,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_935])).

cnf(c_3098,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3097])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_879,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_30])).

cnf(c_880,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_879])).

cnf(c_884,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_880,c_32])).

cnf(c_885,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_884])).

cnf(c_3109,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_885])).

cnf(c_3110,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3109])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_904,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_30])).

cnf(c_905,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_904])).

cnf(c_909,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_905,c_32])).

cnf(c_910,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_909])).

cnf(c_3348,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_910])).

cnf(c_3349,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3348])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_954,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_955,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_954])).

cnf(c_959,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_955,c_32])).

cnf(c_960,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_959])).

cnf(c_3576,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_960])).

cnf(c_3577,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3576])).

cnf(c_6680,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4606,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_3098,c_3110,c_3349,c_3577])).

cnf(c_7790,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7784,c_6680])).

cnf(c_7808,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | r1_tsep_1(sK2,sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7790])).

cnf(c_6691,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1772,c_6680])).

cnf(c_6692,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
    | r1_tsep_1(sK2,sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6691])).

cnf(c_15,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X3) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_612,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_613,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_612])).

cnf(c_615,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_613,c_32,c_30])).

cnf(c_616,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_615])).

cnf(c_2190,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_4513,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2190])).

cnf(c_2175,plain,
    ( ~ r1_tsep_1(sK2,X0)
    | r1_tsep_1(sK2,sK3)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,X0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_3913,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK2,sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_2175])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12098,c_10586,c_7808,c_6692,c_4513,c_3913,c_18,c_20,c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:50:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.26/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.99  
% 3.26/0.99  ------  iProver source info
% 3.26/0.99  
% 3.26/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.99  git: non_committed_changes: false
% 3.26/0.99  git: last_make_outside_of_git: false
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     num_symb
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       true
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  ------ Parsing...
% 3.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... gs_s  sp: 2 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.99  ------ Proving...
% 3.26/0.99  ------ Problem Properties 
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  clauses                                 33
% 3.26/0.99  conjectures                             13
% 3.26/0.99  EPR                                     19
% 3.26/0.99  Horn                                    14
% 3.26/0.99  unary                                   12
% 3.26/0.99  binary                                  3
% 3.26/0.99  lits                                    148
% 3.26/0.99  lits eq                                 4
% 3.26/0.99  fd_pure                                 0
% 3.26/0.99  fd_pseudo                               0
% 3.26/0.99  fd_cond                                 0
% 3.26/0.99  fd_pseudo_cond                          0
% 3.26/0.99  AC symbols                              0
% 3.26/0.99  
% 3.26/0.99  ------ Schedule dynamic 5 is on 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  Current options:
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     none
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       false
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ Proving...
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS status Theorem for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  fof(f5,axiom,(
% 3.26/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f21,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f5])).
% 3.26/0.99  
% 3.26/0.99  fof(f22,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f21])).
% 3.26/0.99  
% 3.26/0.99  fof(f43,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f9,conjecture,(
% 3.26/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f10,negated_conjecture,(
% 3.26/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.26/0.99    inference(negated_conjecture,[],[f9])).
% 3.26/0.99  
% 3.26/0.99  fof(f28,plain,(
% 3.26/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4))) & (m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f10])).
% 3.26/0.99  
% 3.26/0.99  fof(f29,plain,(
% 3.26/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f28])).
% 3.26/0.99  
% 3.26/0.99  fof(f34,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~r1_tsep_1(sK4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,sK4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,sK4)) & m1_pre_topc(X3,sK4) & m1_pre_topc(X1,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f33,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,sK3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,sK3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f32,plain,(
% 3.26/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(X0,sK2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f31,plain,(
% 3.26/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f30,plain,(
% 3.26/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f35,plain,(
% 3.26/0.99    (((((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f29,f34,f33,f32,f31,f30])).
% 3.26/0.99  
% 3.26/0.99  fof(f55,plain,(
% 3.26/0.99    v2_pre_topc(sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f54,plain,(
% 3.26/0.99    ~v2_struct_0(sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f56,plain,(
% 3.26/0.99    l1_pre_topc(sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f8,axiom,(
% 3.26/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f26,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f8])).
% 3.26/0.99  
% 3.26/0.99  fof(f27,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f53,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f27])).
% 3.26/0.99  
% 3.26/0.99  fof(f58,plain,(
% 3.26/0.99    m1_pre_topc(sK1,sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f62,plain,(
% 3.26/0.99    m1_pre_topc(sK3,sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f1,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f13,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f1])).
% 3.26/0.99  
% 3.26/0.99  fof(f14,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f13])).
% 3.26/0.99  
% 3.26/0.99  fof(f36,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f14])).
% 3.26/0.99  
% 3.26/0.99  fof(f61,plain,(
% 3.26/0.99    ~v2_struct_0(sK3)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f57,plain,(
% 3.26/0.99    ~v2_struct_0(sK1)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f4,axiom,(
% 3.26/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f19,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f4])).
% 3.26/0.99  
% 3.26/0.99  fof(f20,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f19])).
% 3.26/0.99  
% 3.26/0.99  fof(f41,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f20])).
% 3.26/0.99  
% 3.26/0.99  fof(f67,plain,(
% 3.26/0.99    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f45,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f59,plain,(
% 3.26/0.99    ~v2_struct_0(sK2)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f60,plain,(
% 3.26/0.99    m1_pre_topc(sK2,sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f63,plain,(
% 3.26/0.99    ~v2_struct_0(sK4)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f64,plain,(
% 3.26/0.99    m1_pre_topc(sK4,sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f2,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f11,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.26/0.99    inference(pure_predicate_removal,[],[f2])).
% 3.26/0.99  
% 3.26/0.99  fof(f15,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f11])).
% 3.26/0.99  
% 3.26/0.99  fof(f16,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f15])).
% 3.26/0.99  
% 3.26/0.99  fof(f37,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f3,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f12,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.26/0.99    inference(pure_predicate_removal,[],[f3])).
% 3.26/0.99  
% 3.26/0.99  fof(f17,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f12])).
% 3.26/0.99  
% 3.26/0.99  fof(f18,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.26/0.99    inference(flattening,[],[f17])).
% 3.26/0.99  
% 3.26/0.99  fof(f39,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f18])).
% 3.26/0.99  
% 3.26/0.99  fof(f40,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f18])).
% 3.26/0.99  
% 3.26/0.99  fof(f38,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f52,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f27])).
% 3.26/0.99  
% 3.26/0.99  fof(f68,plain,(
% 3.26/0.99    ~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f66,plain,(
% 3.26/0.99    m1_pre_topc(sK3,sK4)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f65,plain,(
% 3.26/0.99    m1_pre_topc(sK1,sK2)),
% 3.26/0.99    inference(cnf_transformation,[],[f35])).
% 3.26/0.99  
% 3.26/0.99  cnf(c_8,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X0,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X0)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ v2_pre_topc(X3)
% 3.26/0.99      | ~ l1_pre_topc(X3)
% 3.26/0.99      | v2_struct_0(X3)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1) ),
% 3.26/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_31,negated_conjecture,
% 3.26/0.99      ( v2_pre_topc(sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_433,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X0)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X3)
% 3.26/0.99      | ~ m1_pre_topc(X0,X3)
% 3.26/0.99      | ~ l1_pre_topc(X3)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X3)
% 3.26/0.99      | sK0 != X3 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_434,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X0)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ l1_pre_topc(sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(sK0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_32,negated_conjecture,
% 3.26/0.99      ( ~ v2_struct_0(sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_30,negated_conjecture,
% 3.26/0.99      ( l1_pre_topc(sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_436,plain,
% 3.26/0.99      ( v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X0)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_434,c_32,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_437,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X0)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2) ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_436]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6892,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X1,sK1)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,X0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(sK1) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_437]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_12098,plain,
% 3.26/0.99      ( ~ r1_tsep_1(sK2,sK4)
% 3.26/0.99      | r1_tsep_1(sK4,sK1)
% 3.26/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK2)
% 3.26/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.26/0.99      | v2_struct_0(sK2)
% 3.26/0.99      | v2_struct_0(sK1)
% 3.26/0.99      | v2_struct_0(sK4) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_6892]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_14,plain,
% 3.26/0.99      ( r1_tsep_1(X0,X1)
% 3.26/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X3,X2)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ v2_pre_topc(X2)
% 3.26/0.99      | ~ l1_pre_topc(X2)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X3) ),
% 3.26/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_647,plain,
% 3.26/0.99      ( r1_tsep_1(X0,X1)
% 3.26/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ m1_pre_topc(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X3,X2)
% 3.26/0.99      | ~ l1_pre_topc(X2)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X3)
% 3.26/0.99      | sK0 != X2 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_648,plain,
% 3.26/0.99      ( r1_tsep_1(X0,X1)
% 3.26/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ l1_pre_topc(sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(sK0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_647]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_650,plain,
% 3.26/0.99      ( v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | r1_tsep_1(X0,X1)
% 3.26/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_648,c_32,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_651,plain,
% 3.26/0.99      ( r1_tsep_1(X0,X1)
% 3.26/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2) ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_650]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2423,plain,
% 3.26/0.99      ( ~ r1_tsep_1(k2_tsep_1(sK0,X0,sK4),sK1)
% 3.26/0.99      | r1_tsep_1(sK4,sK1)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,X0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(sK1)
% 3.26/0.99      | v2_struct_0(sK4) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_651]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_10586,plain,
% 3.26/0.99      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
% 3.26/0.99      | r1_tsep_1(sK4,sK1)
% 3.26/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(sK1,sK2)
% 3.26/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.26/0.99      | v2_struct_0(sK2)
% 3.26/0.99      | v2_struct_0(sK1)
% 3.26/0.99      | v2_struct_0(sK4) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_2423]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_28,negated_conjecture,
% 3.26/0.99      ( m1_pre_topc(sK1,sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1775,plain,
% 3.26/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_24,negated_conjecture,
% 3.26/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1779,plain,
% 3.26/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_0,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ l1_pre_topc(X1)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_979,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2)
% 3.26/0.99      | sK0 != X1 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_980,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(sK0)
% 3.26/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_979]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_984,plain,
% 3.26/0.99      ( v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_980,c_32]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_985,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_984]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1753,plain,
% 3.26/0.99      ( k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)
% 3.26/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.26/0.99      | v2_struct_0(X0) = iProver_top
% 3.26/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2485,plain,
% 3.26/0.99      ( k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0)
% 3.26/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/0.99      | v2_struct_0(X0) = iProver_top
% 3.26/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1779,c_1753]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_25,negated_conjecture,
% 3.26/0.99      ( ~ v2_struct_0(sK3) ),
% 3.26/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_40,plain,
% 3.26/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2554,plain,
% 3.26/0.99      ( v2_struct_0(X0) = iProver_top
% 3.26/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/0.99      | k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2485,c_40]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2555,plain,
% 3.26/0.99      ( k1_tsep_1(sK0,X0,sK3) = k1_tsep_1(sK0,sK3,X0)
% 3.26/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_2554]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2566,plain,
% 3.26/0.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
% 3.26/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1775,c_2555]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_29,negated_conjecture,
% 3.26/0.99      ( ~ v2_struct_0(sK1) ),
% 3.26/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_36,plain,
% 3.26/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2615,plain,
% 3.26/0.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2566,c_36]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
% 3.26/0.99      | ~ v2_pre_topc(X1)
% 3.26/0.99      | ~ l1_pre_topc(X1)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_332,plain,
% 3.26/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
% 3.26/0.99      | ~ l1_pre_topc(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | sK0 != X1 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_333,plain,
% 3.26/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ l1_pre_topc(sK0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(sK0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_337,plain,
% 3.26/0.99      ( v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_333,c_32,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_338,plain,
% 3.26/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1) ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_337]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1772,plain,
% 3.26/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1)) = iProver_top
% 3.26/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.26/0.99      | v2_struct_0(X0) = iProver_top
% 3.26/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3022,plain,
% 3.26/0.99      ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top
% 3.26/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.26/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.26/0.99      | v2_struct_0(sK3) = iProver_top
% 3.26/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_2615,c_1772]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_37,plain,
% 3.26/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_41,plain,
% 3.26/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_7784,plain,
% 3.26/0.99      ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_3022,c_36,c_37,c_40,c_41]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_19,negated_conjecture,
% 3.26/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
% 3.26/0.99      | r1_tsep_1(sK2,sK4) ),
% 3.26/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1784,plain,
% 3.26/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) = iProver_top
% 3.26/0.99      | r1_tsep_1(sK2,sK4) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ m1_pre_topc(X0,X3)
% 3.26/0.99      | ~ v2_pre_topc(X3)
% 3.26/0.99      | ~ l1_pre_topc(X3)
% 3.26/0.99      | v2_struct_0(X3)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_503,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ m1_pre_topc(X1,X3)
% 3.26/0.99      | ~ m1_pre_topc(X2,X3)
% 3.26/0.99      | ~ m1_pre_topc(X0,X3)
% 3.26/0.99      | ~ l1_pre_topc(X3)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X3)
% 3.26/0.99      | sK0 != X3 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_504,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.26/0.99      | ~ l1_pre_topc(sK0)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(sK0) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_503]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_506,plain,
% 3.26/0.99      ( v2_struct_0(X2)
% 3.26/0.99      | v2_struct_0(X1)
% 3.26/0.99      | v2_struct_0(X0)
% 3.26/0.99      | ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.26/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_504,c_32,c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_507,plain,
% 3.26/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.26/0.99      | r1_tsep_1(X0,X2)
% 3.26/0.99      | ~ m1_pre_topc(X2,X1)
% 3.26/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_506]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1767,plain,
% 3.26/1.00      ( r1_tsep_1(X0,X1) != iProver_top
% 3.26/1.00      | r1_tsep_1(X0,X2) = iProver_top
% 3.26/1.00      | m1_pre_topc(X2,X1) != iProver_top
% 3.26/1.00      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(X1,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(X2,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(X2) = iProver_top
% 3.26/1.00      | v2_struct_0(X0) = iProver_top
% 3.26/1.00      | v2_struct_0(X1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_507]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4606,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
% 3.26/1.00      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.26/1.00      | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.26/1.00      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(X0) = iProver_top
% 3.26/1.00      | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) = iProver_top
% 3.26/1.00      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1784,c_1767]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_27,negated_conjecture,
% 3.26/1.00      ( ~ v2_struct_0(sK2) ),
% 3.26/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_38,plain,
% 3.26/1.00      ( v2_struct_0(sK2) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_26,negated_conjecture,
% 3.26/1.00      ( m1_pre_topc(sK2,sK0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_39,plain,
% 3.26/1.00      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_23,negated_conjecture,
% 3.26/1.00      ( ~ v2_struct_0(sK4) ),
% 3.26/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_42,plain,
% 3.26/1.00      ( v2_struct_0(sK4) != iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_22,negated_conjecture,
% 3.26/1.00      ( m1_pre_topc(sK4,sK0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_43,plain,
% 3.26/1.00      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | ~ l1_pre_topc(X1)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f37]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_929,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
% 3.26/1.00      | sK0 != X1 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_2,c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_930,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 3.26/1.00      | v2_struct_0(sK0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_929]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_934,plain,
% 3.26/1.00      ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_930,c_32]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_935,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_934]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3097,plain,
% 3.26/1.00      ( ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK1,sK0)
% 3.26/1.00      | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK3))
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK1) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_935]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3098,plain,
% 3.26/1.00      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.26/1.00      | v2_struct_0(sK3) = iProver_top
% 3.26/1.00      | v2_struct_0(sK1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3097]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | ~ l1_pre_topc(X1)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
% 3.26/1.00      inference(cnf_transformation,[],[f39]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_879,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
% 3.26/1.00      | sK0 != X1 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_4,c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_880,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.26/1.00      | v2_struct_0(sK0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_879]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_884,plain,
% 3.26/1.00      ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_880,c_32]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_885,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_884]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3109,plain,
% 3.26/1.00      ( ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK4,sK0)
% 3.26/1.00      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
% 3.26/1.00      | v2_struct_0(sK2)
% 3.26/1.00      | v2_struct_0(sK4) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_885]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3110,plain,
% 3.26/1.00      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) != iProver_top
% 3.26/1.00      | v2_struct_0(sK2) = iProver_top
% 3.26/1.00      | v2_struct_0(sK4) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3109]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.26/1.00      | ~ l1_pre_topc(X1)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f40]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_904,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | sK0 != X1 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_905,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(sK0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_904]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_909,plain,
% 3.26/1.00      ( v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_905,c_32]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_910,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_909]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3348,plain,
% 3.26/1.00      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK4,sK0)
% 3.26/1.00      | v2_struct_0(sK2)
% 3.26/1.00      | v2_struct_0(sK4) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_910]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3349,plain,
% 3.26/1.00      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) = iProver_top
% 3.26/1.00      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(sK2) = iProver_top
% 3.26/1.00      | v2_struct_0(sK4) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3348]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_1,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.26/1.00      | ~ l1_pre_topc(X1)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X0) ),
% 3.26/1.00      inference(cnf_transformation,[],[f38]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_954,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,X1)
% 3.26/1.00      | ~ m1_pre_topc(X2,X1)
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | sK0 != X1 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_1,c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_955,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(sK0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_954]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_959,plain,
% 3.26/1.00      ( v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_955,c_32]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_960,plain,
% 3.26/1.00      ( ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_959]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3576,plain,
% 3.26/1.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK1,sK0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK1) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_960]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3577,plain,
% 3.26/1.00      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 3.26/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(sK3) = iProver_top
% 3.26/1.00      | v2_struct_0(sK1) = iProver_top ),
% 3.26/1.00      inference(predicate_to_equality,[status(thm)],[c_3576]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6680,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
% 3.26/1.00      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.26/1.00      | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.26/1.00      | m1_pre_topc(X0,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(X0) = iProver_top ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_4606,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_3098,
% 3.26/1.00                 c_3110,c_3349,c_3577]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7790,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
% 3.26/1.00      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.26/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(sK3) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_7784,c_6680]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_7808,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
% 3.26/1.00      | r1_tsep_1(sK2,sK4)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | v2_struct_0(sK3) ),
% 3.26/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_7790]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6691,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
% 3.26/1.00      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.26/1.00      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.26/1.00      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.26/1.00      | v2_struct_0(sK3) = iProver_top
% 3.26/1.00      | v2_struct_0(sK1) = iProver_top ),
% 3.26/1.00      inference(superposition,[status(thm)],[c_1772,c_6680]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_6692,plain,
% 3.26/1.00      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1)
% 3.26/1.00      | r1_tsep_1(sK2,sK4)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK1,sK0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK1) ),
% 3.26/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6691]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_15,plain,
% 3.26/1.00      ( r1_tsep_1(X0,X1)
% 3.26/1.00      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,X2)
% 3.26/1.00      | ~ m1_pre_topc(X0,X2)
% 3.26/1.00      | ~ m1_pre_topc(X3,X2)
% 3.26/1.00      | ~ m1_pre_topc(X1,X3)
% 3.26/1.00      | ~ v2_pre_topc(X2)
% 3.26/1.00      | ~ l1_pre_topc(X2)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X3) ),
% 3.26/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_612,plain,
% 3.26/1.00      ( r1_tsep_1(X0,X1)
% 3.26/1.00      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,X2)
% 3.26/1.00      | ~ m1_pre_topc(X1,X3)
% 3.26/1.00      | ~ m1_pre_topc(X0,X2)
% 3.26/1.00      | ~ m1_pre_topc(X3,X2)
% 3.26/1.00      | ~ l1_pre_topc(X2)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X3)
% 3.26/1.00      | sK0 != X2 ),
% 3.26/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_613,plain,
% 3.26/1.00      ( r1_tsep_1(X0,X1)
% 3.26/1.00      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,X2)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X2,sK0)
% 3.26/1.00      | ~ l1_pre_topc(sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(sK0) ),
% 3.26/1.00      inference(unflattening,[status(thm)],[c_612]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_615,plain,
% 3.26/1.00      ( v2_struct_0(X2)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | r1_tsep_1(X0,X1)
% 3.26/1.00      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,X2)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X2,sK0) ),
% 3.26/1.00      inference(global_propositional_subsumption,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_613,c_32,c_30]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_616,plain,
% 3.26/1.00      ( r1_tsep_1(X0,X1)
% 3.26/1.00      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.26/1.00      | ~ m1_pre_topc(X1,X2)
% 3.26/1.00      | ~ m1_pre_topc(X2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(X1,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(X1)
% 3.26/1.00      | v2_struct_0(X2) ),
% 3.26/1.00      inference(renaming,[status(thm)],[c_615]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2190,plain,
% 3.26/1.00      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,X0),sK3)
% 3.26/1.00      | r1_tsep_1(sK2,sK3)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK2) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_616]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_4513,plain,
% 3.26/1.00      ( ~ r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3)
% 3.26/1.00      | r1_tsep_1(sK2,sK3)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK4)
% 3.26/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK4,sK0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK2)
% 3.26/1.00      | v2_struct_0(sK4) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2190]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_2175,plain,
% 3.26/1.00      ( ~ r1_tsep_1(sK2,X0)
% 3.26/1.00      | r1_tsep_1(sK2,sK3)
% 3.26/1.00      | ~ m1_pre_topc(X0,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,X0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | v2_struct_0(X0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK2) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_507]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_3913,plain,
% 3.26/1.00      ( r1_tsep_1(sK2,sK3)
% 3.26/1.00      | ~ r1_tsep_1(sK2,sK4)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK3,sK4)
% 3.26/1.00      | ~ m1_pre_topc(sK2,sK0)
% 3.26/1.00      | ~ m1_pre_topc(sK4,sK0)
% 3.26/1.00      | v2_struct_0(sK3)
% 3.26/1.00      | v2_struct_0(sK2)
% 3.26/1.00      | v2_struct_0(sK4) ),
% 3.26/1.00      inference(instantiation,[status(thm)],[c_2175]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_18,negated_conjecture,
% 3.26/1.00      ( ~ r1_tsep_1(sK2,sK3) | ~ r1_tsep_1(sK4,sK1) ),
% 3.26/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_20,negated_conjecture,
% 3.26/1.00      ( m1_pre_topc(sK3,sK4) ),
% 3.26/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(c_21,negated_conjecture,
% 3.26/1.00      ( m1_pre_topc(sK1,sK2) ),
% 3.26/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.26/1.00  
% 3.26/1.00  cnf(contradiction,plain,
% 3.26/1.00      ( $false ),
% 3.26/1.00      inference(minisat,
% 3.26/1.00                [status(thm)],
% 3.26/1.00                [c_12098,c_10586,c_7808,c_6692,c_4513,c_3913,c_18,c_20,
% 3.26/1.00                 c_21,c_22,c_23,c_24,c_25,c_26,c_27,c_28,c_29]) ).
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/1.00  
% 3.26/1.00  ------                               Statistics
% 3.26/1.00  
% 3.26/1.00  ------ General
% 3.26/1.00  
% 3.26/1.00  abstr_ref_over_cycles:                  0
% 3.26/1.00  abstr_ref_under_cycles:                 0
% 3.26/1.00  gc_basic_clause_elim:                   0
% 3.26/1.00  forced_gc_time:                         0
% 3.26/1.00  parsing_time:                           0.012
% 3.26/1.00  unif_index_cands_time:                  0.
% 3.26/1.00  unif_index_add_time:                    0.
% 3.26/1.00  orderings_time:                         0.
% 3.26/1.00  out_proof_time:                         0.013
% 3.26/1.00  total_time:                             0.336
% 3.26/1.00  num_of_symbols:                         42
% 3.26/1.00  num_of_terms:                           4103
% 3.26/1.00  
% 3.26/1.00  ------ Preprocessing
% 3.26/1.00  
% 3.26/1.00  num_of_splits:                          2
% 3.26/1.00  num_of_split_atoms:                     2
% 3.26/1.00  num_of_reused_defs:                     0
% 3.26/1.00  num_eq_ax_congr_red:                    0
% 3.26/1.00  num_of_sem_filtered_clauses:            3
% 3.26/1.00  num_of_subtypes:                        1
% 3.26/1.00  monotx_restored_types:                  0
% 3.26/1.00  sat_num_of_epr_types:                   0
% 3.26/1.00  sat_num_of_non_cyclic_types:            0
% 3.26/1.00  sat_guarded_non_collapsed_types:        0
% 3.26/1.00  num_pure_diseq_elim:                    0
% 3.26/1.00  simp_replaced_by:                       0
% 3.26/1.00  res_preprocessed:                       143
% 3.26/1.00  prep_upred:                             0
% 3.26/1.00  prep_unflattend:                        18
% 3.26/1.00  smt_new_axioms:                         0
% 3.26/1.00  pred_elim_cands:                        3
% 3.26/1.00  pred_elim:                              2
% 3.26/1.00  pred_elim_cl:                           2
% 3.26/1.00  pred_elim_cycles:                       4
% 3.26/1.00  merged_defs:                            0
% 3.26/1.00  merged_defs_ncl:                        0
% 3.26/1.00  bin_hyper_res:                          0
% 3.26/1.00  prep_cycles:                            4
% 3.26/1.00  pred_elim_time:                         0.016
% 3.26/1.00  splitting_time:                         0.
% 3.26/1.00  sem_filter_time:                        0.
% 3.26/1.00  monotx_time:                            0.
% 3.26/1.00  subtype_inf_time:                       0.
% 3.26/1.00  
% 3.26/1.00  ------ Problem properties
% 3.26/1.00  
% 3.26/1.00  clauses:                                33
% 3.26/1.00  conjectures:                            13
% 3.26/1.00  epr:                                    19
% 3.26/1.00  horn:                                   14
% 3.26/1.00  ground:                                 15
% 3.26/1.00  unary:                                  12
% 3.26/1.00  binary:                                 3
% 3.26/1.00  lits:                                   148
% 3.26/1.00  lits_eq:                                4
% 3.26/1.00  fd_pure:                                0
% 3.26/1.00  fd_pseudo:                              0
% 3.26/1.00  fd_cond:                                0
% 3.26/1.00  fd_pseudo_cond:                         0
% 3.26/1.00  ac_symbols:                             0
% 3.26/1.00  
% 3.26/1.00  ------ Propositional Solver
% 3.26/1.00  
% 3.26/1.00  prop_solver_calls:                      32
% 3.26/1.00  prop_fast_solver_calls:                 2286
% 3.26/1.00  smt_solver_calls:                       0
% 3.26/1.00  smt_fast_solver_calls:                  0
% 3.26/1.00  prop_num_of_clauses:                    3194
% 3.26/1.00  prop_preprocess_simplified:             6930
% 3.26/1.00  prop_fo_subsumed:                       164
% 3.26/1.00  prop_solver_time:                       0.
% 3.26/1.00  smt_solver_time:                        0.
% 3.26/1.00  smt_fast_solver_time:                   0.
% 3.26/1.00  prop_fast_solver_time:                  0.
% 3.26/1.00  prop_unsat_core_time:                   0.
% 3.26/1.00  
% 3.26/1.00  ------ QBF
% 3.26/1.00  
% 3.26/1.00  qbf_q_res:                              0
% 3.26/1.00  qbf_num_tautologies:                    0
% 3.26/1.00  qbf_prep_cycles:                        0
% 3.26/1.00  
% 3.26/1.00  ------ BMC1
% 3.26/1.00  
% 3.26/1.00  bmc1_current_bound:                     -1
% 3.26/1.00  bmc1_last_solved_bound:                 -1
% 3.26/1.00  bmc1_unsat_core_size:                   -1
% 3.26/1.00  bmc1_unsat_core_parents_size:           -1
% 3.26/1.00  bmc1_merge_next_fun:                    0
% 3.26/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.26/1.00  
% 3.26/1.00  ------ Instantiation
% 3.26/1.00  
% 3.26/1.00  inst_num_of_clauses:                    738
% 3.26/1.00  inst_num_in_passive:                    302
% 3.26/1.00  inst_num_in_active:                     433
% 3.26/1.00  inst_num_in_unprocessed:                2
% 3.26/1.00  inst_num_of_loops:                      596
% 3.26/1.00  inst_num_of_learning_restarts:          0
% 3.26/1.00  inst_num_moves_active_passive:          156
% 3.26/1.00  inst_lit_activity:                      0
% 3.26/1.00  inst_lit_activity_moves:                0
% 3.26/1.00  inst_num_tautologies:                   0
% 3.26/1.00  inst_num_prop_implied:                  0
% 3.26/1.00  inst_num_existing_simplified:           0
% 3.26/1.00  inst_num_eq_res_simplified:             0
% 3.26/1.00  inst_num_child_elim:                    0
% 3.26/1.00  inst_num_of_dismatching_blockings:      387
% 3.26/1.00  inst_num_of_non_proper_insts:           877
% 3.26/1.00  inst_num_of_duplicates:                 0
% 3.26/1.00  inst_inst_num_from_inst_to_res:         0
% 3.26/1.00  inst_dismatching_checking_time:         0.
% 3.26/1.00  
% 3.26/1.00  ------ Resolution
% 3.26/1.00  
% 3.26/1.00  res_num_of_clauses:                     0
% 3.26/1.00  res_num_in_passive:                     0
% 3.26/1.00  res_num_in_active:                      0
% 3.26/1.00  res_num_of_loops:                       147
% 3.26/1.00  res_forward_subset_subsumed:            12
% 3.26/1.00  res_backward_subset_subsumed:           0
% 3.26/1.00  res_forward_subsumed:                   0
% 3.26/1.00  res_backward_subsumed:                  0
% 3.26/1.00  res_forward_subsumption_resolution:     0
% 3.26/1.00  res_backward_subsumption_resolution:    0
% 3.26/1.00  res_clause_to_clause_subsumption:       2086
% 3.26/1.00  res_orphan_elimination:                 0
% 3.26/1.00  res_tautology_del:                      130
% 3.26/1.00  res_num_eq_res_simplified:              0
% 3.26/1.00  res_num_sel_changes:                    0
% 3.26/1.00  res_moves_from_active_to_pass:          0
% 3.26/1.00  
% 3.26/1.00  ------ Superposition
% 3.26/1.00  
% 3.26/1.00  sup_time_total:                         0.
% 3.26/1.00  sup_time_generating:                    0.
% 3.26/1.00  sup_time_sim_full:                      0.
% 3.26/1.00  sup_time_sim_immed:                     0.
% 3.26/1.00  
% 3.26/1.00  sup_num_of_clauses:                     275
% 3.26/1.00  sup_num_in_active:                      116
% 3.26/1.00  sup_num_in_passive:                     159
% 3.26/1.00  sup_num_of_loops:                       118
% 3.26/1.00  sup_fw_superposition:                   240
% 3.26/1.00  sup_bw_superposition:                   141
% 3.26/1.00  sup_immediate_simplified:               105
% 3.26/1.00  sup_given_eliminated:                   0
% 3.26/1.00  comparisons_done:                       0
% 3.26/1.00  comparisons_avoided:                    0
% 3.26/1.00  
% 3.26/1.00  ------ Simplifications
% 3.26/1.00  
% 3.26/1.00  
% 3.26/1.00  sim_fw_subset_subsumed:                 8
% 3.26/1.00  sim_bw_subset_subsumed:                 13
% 3.26/1.00  sim_fw_subsumed:                        80
% 3.26/1.00  sim_bw_subsumed:                        0
% 3.26/1.00  sim_fw_subsumption_res:                 1
% 3.26/1.00  sim_bw_subsumption_res:                 0
% 3.26/1.00  sim_tautology_del:                      0
% 3.26/1.00  sim_eq_tautology_del:                   14
% 3.26/1.00  sim_eq_res_simp:                        0
% 3.26/1.00  sim_fw_demodulated:                     0
% 3.26/1.00  sim_bw_demodulated:                     0
% 3.26/1.00  sim_light_normalised:                   17
% 3.26/1.00  sim_joinable_taut:                      0
% 3.26/1.00  sim_joinable_simp:                      0
% 3.26/1.00  sim_ac_normalised:                      0
% 3.26/1.00  sim_smt_subsumption:                    0
% 3.26/1.00  
%------------------------------------------------------------------------------
