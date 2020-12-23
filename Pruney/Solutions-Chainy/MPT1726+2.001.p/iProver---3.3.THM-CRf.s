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

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :  181 (3026 expanded)
%              Number of clauses        :  126 ( 611 expanded)
%              Number of leaves         :   16 (1276 expanded)
%              Depth                    :   27
%              Number of atoms          : 1174 (46435 expanded)
%              Number of equality atoms :  181 ( 654 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,conjecture,(
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

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f32,plain,(
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

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f33,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f32,f31,f30,f29,f28])).

fof(f66,plain,
    ( ~ r1_tsep_1(sK4,sK1)
    | ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f62,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f20,plain,(
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
    inference(flattening,[],[f20])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f21])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f55,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f56,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f58,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f59,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f60,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f18,plain,(
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
    inference(flattening,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f21])).

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

fof(f16,plain,(
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
    inference(flattening,[],[f16])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f10,plain,(
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

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f14])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f50,plain,(
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
    inference(cnf_transformation,[],[f25])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f25])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tsep_1(sK2,sK3)
    | ~ r1_tsep_1(sK4,sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_23,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(cnf_transformation,[],[f41])).

cnf(c_31,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_369,plain,
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

cnf(c_370,plain,
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
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_30,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_372,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_370,c_32,c_30])).

cnf(c_373,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_372])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4492,plain,
    ( r1_tsep_1(X0,sK1)
    | ~ r1_tsep_1(sK2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1) ),
    inference(resolution,[status(thm)],[c_373,c_21])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_28,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_4580,plain,
    ( r1_tsep_1(X0,sK1)
    | ~ r1_tsep_1(sK2,X0)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4492,c_29,c_28,c_27,c_26])).

cnf(c_1033,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1032,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2047,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1033,c_1032])).

cnf(c_1037,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k2_tsep_1(X0,X2,X4) = k2_tsep_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_4337,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k2_tsep_1(X1,X3,X5) = k2_tsep_1(X0,X2,X4) ),
    inference(resolution,[status(thm)],[c_2047,c_1037])).

cnf(c_1038,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2126,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_1038,c_1032])).

cnf(c_5583,plain,
    ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
    | r1_tsep_1(k2_tsep_1(X4,X5,X6),X3)
    | X0 != X4
    | X1 != X5
    | X2 != X6 ),
    inference(resolution,[status(thm)],[c_4337,c_2126])).

cnf(c_19,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_6709,plain,
    ( r1_tsep_1(k2_tsep_1(X0,X1,X2),k1_tsep_1(sK0,sK1,sK3))
    | r1_tsep_1(sK2,sK4)
    | sK0 != X0
    | sK2 != X1
    | sK4 != X2 ),
    inference(resolution,[status(thm)],[c_5583,c_19])).

cnf(c_25,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_24,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_20,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1517,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1513,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_804,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_30])).

cnf(c_805,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(unflattening,[status(thm)],[c_804])).

cnf(c_809,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_805,c_32])).

cnf(c_810,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
    inference(renaming,[status(thm)],[c_809])).

cnf(c_1497,plain,
    ( k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_810])).

cnf(c_1681,plain,
    ( k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1513,c_1497])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4097,plain,
    ( v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_36])).

cnf(c_4098,plain,
    ( k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1)
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_4097])).

cnf(c_4104,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1517,c_4098])).

cnf(c_40,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4172,plain,
    ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4104,c_40])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_307,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_31])).

cnf(c_308,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_312,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_32,c_30])).

cnf(c_313,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_312])).

cnf(c_1510,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1)) = iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_313])).

cnf(c_6169,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_1510])).

cnf(c_37,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_41,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_6390,plain,
    ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6169,c_36,c_37,c_40,c_41])).

cnf(c_1522,plain,
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
    inference(cnf_transformation,[],[f43])).

cnf(c_439,plain,
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

cnf(c_440,plain,
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
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_442,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_32,c_30])).

cnf(c_443,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_1506,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_5298,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1506])).

cnf(c_38,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_39,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_42,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_43,plain,
    ( m1_pre_topc(sK4,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_729,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_30])).

cnf(c_730,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_729])).

cnf(c_734,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_730,c_32])).

cnf(c_735,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_734])).

cnf(c_1607,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k2_tsep_1(sK0,X0,sK4),sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_735])).

cnf(c_1831,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_1607])).

cnf(c_1832,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1831])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_779,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_30])).

cnf(c_780,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_779])).

cnf(c_784,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_780,c_32])).

cnf(c_785,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_784])).

cnf(c_1632,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_785])).

cnf(c_1914,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_1915,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_754,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_30])).

cnf(c_755,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_754])).

cnf(c_759,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_755,c_32])).

cnf(c_760,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_759])).

cnf(c_1499,plain,
    ( m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k1_tsep_1(sK0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_760])).

cnf(c_4174,plain,
    ( m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4172,c_1499])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_704,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_30])).

cnf(c_705,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_704])).

cnf(c_709,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X0,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_705,c_32])).

cnf(c_710,plain,
    ( ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
    inference(renaming,[status(thm)],[c_709])).

cnf(c_4985,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_4986,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4985])).

cnf(c_5375,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5298,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_1832,c_1915,c_4174,c_4986])).

cnf(c_6395,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6390,c_5375])).

cnf(c_6448,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6395,c_40,c_41])).

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
    inference(cnf_transformation,[],[f50])).

cnf(c_548,plain,
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

cnf(c_549,plain,
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
    inference(unflattening,[status(thm)],[c_548])).

cnf(c_551,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_549,c_32,c_30])).

cnf(c_552,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_551])).

cnf(c_1503,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_552])).

cnf(c_6458,plain,
    ( r1_tsep_1(sK2,sK3) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6448,c_1503])).

cnf(c_6462,plain,
    ( r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK2,sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6458])).

cnf(c_6181,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_5375])).

cnf(c_6665,plain,
    ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
    | r1_tsep_1(sK2,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6181,c_36,c_37,c_40,c_41])).

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
    inference(cnf_transformation,[],[f51])).

cnf(c_583,plain,
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

cnf(c_584,plain,
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
    inference(unflattening,[status(thm)],[c_583])).

cnf(c_586,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | ~ m1_pre_topc(X2,sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_584,c_32,c_30])).

cnf(c_587,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK0)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(X1,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_1502,plain,
    ( r1_tsep_1(X0,X1) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1) != iProver_top
    | m1_pre_topc(X1,X2) != iProver_top
    | m1_pre_topc(X0,sK0) != iProver_top
    | m1_pre_topc(X1,sK0) != iProver_top
    | m1_pre_topc(X2,sK0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_6676,plain,
    ( r1_tsep_1(sK2,sK4) = iProver_top
    | r1_tsep_1(sK4,sK1) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | m1_pre_topc(sK1,sK2) != iProver_top
    | m1_pre_topc(sK4,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | v2_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_6665,c_1502])).

cnf(c_6680,plain,
    ( r1_tsep_1(sK2,sK4)
    | r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | v2_struct_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6676])).

cnf(c_6776,plain,
    ( r1_tsep_1(sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6709,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,c_20,c_18,c_6462,c_6680])).

cnf(c_6916,plain,
    ( r1_tsep_1(sK4,sK1)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_4580,c_6776])).

cnf(c_7005,negated_conjecture,
    ( ~ r1_tsep_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_23,c_22,c_6916])).

cnf(c_5430,plain,
    ( r1_tsep_1(X0,sK3)
    | ~ r1_tsep_1(X0,sK4)
    | ~ m1_pre_topc(X0,sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(X0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK4) ),
    inference(resolution,[status(thm)],[c_443,c_20])).

cnf(c_5453,plain,
    ( r1_tsep_1(X0,sK3)
    | ~ r1_tsep_1(X0,sK4)
    | ~ m1_pre_topc(X0,sK0)
    | v2_struct_0(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5430,c_25,c_24,c_23,c_22])).

cnf(c_7017,plain,
    ( ~ r1_tsep_1(sK2,sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2) ),
    inference(resolution,[status(thm)],[c_7005,c_5453])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7017,c_6776,c_26,c_27])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.62/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.62/0.99  
% 3.62/0.99  ------  iProver source info
% 3.62/0.99  
% 3.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.62/0.99  git: non_committed_changes: false
% 3.62/0.99  git: last_make_outside_of_git: false
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  ------ Parsing...
% 3.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.62/0.99  
% 3.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.62/0.99  ------ Proving...
% 3.62/0.99  ------ Problem Properties 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  clauses                                 27
% 3.62/0.99  conjectures                             13
% 3.62/0.99  EPR                                     16
% 3.62/0.99  Horn                                    12
% 3.62/0.99  unary                                   11
% 3.62/0.99  binary                                  2
% 3.62/0.99  lits                                    117
% 3.62/0.99  lits eq                                 1
% 3.62/0.99  fd_pure                                 0
% 3.62/0.99  fd_pseudo                               0
% 3.62/0.99  fd_cond                                 0
% 3.62/0.99  fd_pseudo_cond                          0
% 3.62/0.99  AC symbols                              0
% 3.62/0.99  
% 3.62/0.99  ------ Input Options Time Limit: Unbounded
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ 
% 3.62/0.99  Current options:
% 3.62/0.99  ------ 
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  ------ Proving...
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS status Theorem for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  fof(f8,conjecture,(
% 3.62/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f9,negated_conjecture,(
% 3.62/0.99    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => ((r1_tsep_1(X4,X1) & r1_tsep_1(X2,X3)) | (~r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) & ~r1_tsep_1(X2,X4)))))))))),
% 3.62/0.99    inference(negated_conjecture,[],[f8])).
% 3.62/0.99  
% 3.62/0.99  fof(f26,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4))) & (m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f9])).
% 3.62/0.99  
% 3.62/0.99  fof(f27,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f26])).
% 3.62/0.99  
% 3.62/0.99  fof(f32,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((~r1_tsep_1(sK4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,sK4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,sK4)) & m1_pre_topc(X3,sK4) & m1_pre_topc(X1,X2) & m1_pre_topc(sK4,X0) & ~v2_struct_0(sK4))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f31,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,sK3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,sK3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(sK3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,X0) & ~v2_struct_0(sK3))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f30,plain,(
% 3.62/0.99    ( ! [X0,X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(sK2,X3)) & (r1_tsep_1(k2_tsep_1(X0,sK2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(sK2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,sK2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,X0) & ~v2_struct_0(sK2))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f29,plain,(
% 3.62/0.99    ( ! [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,sK1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,sK1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(sK1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,X0) & ~v2_struct_0(sK1))) )),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f28,plain,(
% 3.62/0.99    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((~r1_tsep_1(X4,X1) | ~r1_tsep_1(X2,X3)) & (r1_tsep_1(k2_tsep_1(sK0,X2,X4),k1_tsep_1(sK0,X1,X3)) | r1_tsep_1(X2,X4)) & m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 3.62/0.99    introduced(choice_axiom,[])).
% 3.62/0.99  
% 3.62/0.99  fof(f33,plain,(
% 3.62/0.99    (((((~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)) & (r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK1,sK2) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 3.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f27,f32,f31,f30,f29,f28])).
% 3.62/0.99  
% 3.62/0.99  fof(f66,plain,(
% 3.62/0.99    ~r1_tsep_1(sK4,sK1) | ~r1_tsep_1(sK2,sK3)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f61,plain,(
% 3.62/0.99    ~v2_struct_0(sK4)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f62,plain,(
% 3.62/0.99    m1_pre_topc(sK4,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f5,axiom,(
% 3.62/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))))))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f20,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f5])).
% 3.62/0.99  
% 3.62/0.99  fof(f21,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | (r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f20])).
% 3.62/0.99  
% 3.62/0.99  fof(f41,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X2,X3) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f21])).
% 3.62/0.99  
% 3.62/0.99  fof(f53,plain,(
% 3.62/0.99    v2_pre_topc(sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f52,plain,(
% 3.62/0.99    ~v2_struct_0(sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f54,plain,(
% 3.62/0.99    l1_pre_topc(sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f63,plain,(
% 3.62/0.99    m1_pre_topc(sK1,sK2)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f55,plain,(
% 3.62/0.99    ~v2_struct_0(sK1)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f56,plain,(
% 3.62/0.99    m1_pre_topc(sK1,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f57,plain,(
% 3.62/0.99    ~v2_struct_0(sK2)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f58,plain,(
% 3.62/0.99    m1_pre_topc(sK2,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f65,plain,(
% 3.62/0.99    r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) | r1_tsep_1(sK2,sK4)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f59,plain,(
% 3.62/0.99    ~v2_struct_0(sK3)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f60,plain,(
% 3.62/0.99    m1_pre_topc(sK3,sK0)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f64,plain,(
% 3.62/0.99    m1_pre_topc(sK3,sK4)),
% 3.62/0.99    inference(cnf_transformation,[],[f33])).
% 3.62/0.99  
% 3.62/0.99  fof(f1,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f12,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f1])).
% 3.62/0.99  
% 3.62/0.99  fof(f13,plain,(
% 3.62/0.99    ! [X0,X1,X2] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f12])).
% 3.62/0.99  
% 3.62/0.99  fof(f34,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f13])).
% 3.62/0.99  
% 3.62/0.99  fof(f4,axiom,(
% 3.62/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f18,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f4])).
% 3.62/0.99  
% 3.62/0.99  fof(f19,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f18])).
% 3.62/0.99  
% 3.62/0.99  fof(f39,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f19])).
% 3.62/0.99  
% 3.62/0.99  fof(f43,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,X2) | r1_tsep_1(X3,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f21])).
% 3.62/0.99  
% 3.62/0.99  fof(f3,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f11,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 3.62/0.99    inference(pure_predicate_removal,[],[f3])).
% 3.62/0.99  
% 3.62/0.99  fof(f16,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f11])).
% 3.62/0.99  
% 3.62/0.99  fof(f17,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f16])).
% 3.62/0.99  
% 3.62/0.99  fof(f38,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f2,axiom,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f10,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 3.62/0.99    inference(pure_predicate_removal,[],[f2])).
% 3.62/0.99  
% 3.62/0.99  fof(f14,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f10])).
% 3.62/0.99  
% 3.62/0.99  fof(f15,plain,(
% 3.62/0.99    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f14])).
% 3.62/0.99  
% 3.62/0.99  fof(f36,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f35,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f15])).
% 3.62/0.99  
% 3.62/0.99  fof(f37,plain,(
% 3.62/0.99    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f17])).
% 3.62/0.99  
% 3.62/0.99  fof(f7,axiom,(
% 3.62/0.99    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (~r1_tsep_1(X1,X2) => ((m1_pre_topc(X2,X3) => (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2))) & (m1_pre_topc(X1,X3) => (~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)))))))))),
% 3.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.62/0.99  
% 3.62/0.99  fof(f24,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.62/0.99    inference(ennf_transformation,[],[f7])).
% 3.62/0.99  
% 3.62/0.99  fof(f25,plain,(
% 3.62/0.99    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) & ~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2)) | ~m1_pre_topc(X2,X3)) & ((~r1_tsep_1(k2_tsep_1(X0,X2,X3),X1) & ~r1_tsep_1(k2_tsep_1(X0,X3,X2),X1)) | ~m1_pre_topc(X1,X3))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.62/0.99    inference(flattening,[],[f24])).
% 3.62/0.99  
% 3.62/0.99  fof(f50,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f25])).
% 3.62/0.99  
% 3.62/0.99  fof(f51,plain,(
% 3.62/0.99    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k2_tsep_1(X0,X3,X1),X2) | ~m1_pre_topc(X2,X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 3.62/0.99    inference(cnf_transformation,[],[f25])).
% 3.62/0.99  
% 3.62/0.99  cnf(c_18,negated_conjecture,
% 3.62/0.99      ( ~ r1_tsep_1(sK2,sK3) | ~ r1_tsep_1(sK4,sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_23,negated_conjecture,
% 3.62/0.99      ( ~ v2_struct_0(sK4) ),
% 3.62/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_22,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK4,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_8,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ v2_pre_topc(X3)
% 3.62/0.99      | ~ l1_pre_topc(X3)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_31,negated_conjecture,
% 3.62/0.99      ( v2_pre_topc(sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_369,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X3)
% 3.62/0.99      | ~ m1_pre_topc(X0,X3)
% 3.62/0.99      | ~ l1_pre_topc(X3)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | sK0 != X3 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_370,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ l1_pre_topc(sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_369]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_32,negated_conjecture,
% 3.62/0.99      ( ~ v2_struct_0(sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_30,negated_conjecture,
% 3.62/0.99      ( l1_pre_topc(sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_372,plain,
% 3.62/0.99      ( v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_370,c_32,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_373,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_372]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_21,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK1,sK2) ),
% 3.62/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4492,plain,
% 3.62/0.99      ( r1_tsep_1(X0,sK1)
% 3.62/0.99      | ~ r1_tsep_1(sK2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK2)
% 3.62/0.99      | v2_struct_0(sK1) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_373,c_21]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_29,negated_conjecture,
% 3.62/0.99      ( ~ v2_struct_0(sK1) ),
% 3.62/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_28,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK1,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_27,negated_conjecture,
% 3.62/0.99      ( ~ v2_struct_0(sK2) ),
% 3.62/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_26,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK2,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4580,plain,
% 3.62/0.99      ( r1_tsep_1(X0,sK1)
% 3.62/0.99      | ~ r1_tsep_1(sK2,X0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_4492,c_29,c_28,c_27,c_26]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1033,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1032,plain,( X0 = X0 ),theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2047,plain,
% 3.62/0.99      ( X0 != X1 | X1 = X0 ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_1033,c_1032]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1037,plain,
% 3.62/0.99      ( X0 != X1
% 3.62/0.99      | X2 != X3
% 3.62/0.99      | X4 != X5
% 3.62/0.99      | k2_tsep_1(X0,X2,X4) = k2_tsep_1(X1,X3,X5) ),
% 3.62/0.99      theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4337,plain,
% 3.62/0.99      ( X0 != X1
% 3.62/0.99      | X2 != X3
% 3.62/0.99      | X4 != X5
% 3.62/0.99      | k2_tsep_1(X1,X3,X5) = k2_tsep_1(X0,X2,X4) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_2047,c_1037]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1038,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1) | r1_tsep_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.62/0.99      theory(equality) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2126,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1) | r1_tsep_1(X2,X1) | X2 != X0 ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_1038,c_1032]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5583,plain,
% 3.62/0.99      ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
% 3.62/0.99      | r1_tsep_1(k2_tsep_1(X4,X5,X6),X3)
% 3.62/0.99      | X0 != X4
% 3.62/0.99      | X1 != X5
% 3.62/0.99      | X2 != X6 ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_4337,c_2126]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_19,negated_conjecture,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3))
% 3.62/0.99      | r1_tsep_1(sK2,sK4) ),
% 3.62/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6709,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(X0,X1,X2),k1_tsep_1(sK0,sK1,sK3))
% 3.62/0.99      | r1_tsep_1(sK2,sK4)
% 3.62/0.99      | sK0 != X0
% 3.62/0.99      | sK2 != X1
% 3.62/0.99      | sK4 != X2 ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_5583,c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_25,negated_conjecture,
% 3.62/0.99      ( ~ v2_struct_0(sK3) ),
% 3.62/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_24,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK3,sK0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_20,negated_conjecture,
% 3.62/0.99      ( m1_pre_topc(sK3,sK4) ),
% 3.62/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1517,plain,
% 3.62/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1513,plain,
% 3.62/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_0,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f34]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_804,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2)
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_805,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK0)
% 3.62/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_804]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_809,plain,
% 3.62/0.99      ( v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_805,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_810,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_809]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1497,plain,
% 3.62/0.99      ( k1_tsep_1(sK0,X0,X1) = k1_tsep_1(sK0,X1,X0)
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_810]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1681,plain,
% 3.62/0.99      ( k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1)
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1513,c_1497]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_36,plain,
% 3.62/0.99      ( v2_struct_0(sK1) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4097,plain,
% 3.62/0.99      ( v2_struct_0(X0) = iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_1681,c_36]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4098,plain,
% 3.62/0.99      ( k1_tsep_1(sK0,sK1,X0) = k1_tsep_1(sK0,X0,sK1)
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_4097]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4104,plain,
% 3.62/0.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3)
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1517,c_4098]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_40,plain,
% 3.62/0.99      ( v2_struct_0(sK3) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4172,plain,
% 3.62/0.99      ( k1_tsep_1(sK0,sK3,sK1) = k1_tsep_1(sK0,sK1,sK3) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_4104,c_40]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
% 3.62/0.99      | ~ v2_pre_topc(X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_307,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_308,plain,
% 3.62/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ l1_pre_topc(sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_307]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_312,plain,
% 3.62/0.99      ( v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_308,c_32,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_313,plain,
% 3.62/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1))
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_312]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1510,plain,
% 3.62/0.99      ( m1_pre_topc(X0,k1_tsep_1(sK0,X0,X1)) = iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_313]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6169,plain,
% 3.62/0.99      ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4172,c_1510]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_37,plain,
% 3.62/0.99      ( m1_pre_topc(sK1,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_41,plain,
% 3.62/0.99      ( m1_pre_topc(sK3,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6390,plain,
% 3.62/0.99      ( m1_pre_topc(sK3,k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6169,c_36,c_37,c_40,c_41]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1522,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),k1_tsep_1(sK0,sK1,sK3)) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ m1_pre_topc(X0,X3)
% 3.62/0.99      | ~ v2_pre_topc(X3)
% 3.62/0.99      | ~ l1_pre_topc(X3)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_439,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ m1_pre_topc(X2,X3)
% 3.62/0.99      | ~ m1_pre_topc(X0,X3)
% 3.62/0.99      | ~ l1_pre_topc(X3)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | sK0 != X3 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_440,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ l1_pre_topc(sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_442,plain,
% 3.62/0.99      ( v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_440,c_32,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_443,plain,
% 3.62/0.99      ( ~ r1_tsep_1(X0,X1)
% 3.62/0.99      | r1_tsep_1(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_442]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1506,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1) != iProver_top
% 3.62/0.99      | r1_tsep_1(X0,X2) = iProver_top
% 3.62/0.99      | m1_pre_topc(X2,X1) != iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X2,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X2) = iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5298,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) = iProver_top
% 3.62/0.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1522,c_1506]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_38,plain,
% 3.62/0.99      ( v2_struct_0(sK2) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_39,plain,
% 3.62/0.99      ( m1_pre_topc(sK2,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_42,plain,
% 3.62/0.99      ( v2_struct_0(sK4) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_43,plain,
% 3.62/0.99      ( m1_pre_topc(sK4,sK0) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_3,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_729,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_730,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_729]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_734,plain,
% 3.62/0.99      ( v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_730,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_735,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_734]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1607,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | m1_pre_topc(k2_tsep_1(sK0,X0,sK4),sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_735]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1831,plain,
% 3.62/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | v2_struct_0(sK2)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1607]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1832,plain,
% 3.62/0.99      ( m1_pre_topc(k2_tsep_1(sK0,sK2,sK4),sK0) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK2) = iProver_top
% 3.62/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1831]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(cnf_transformation,[],[f36]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_779,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_1,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_780,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_779]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_784,plain,
% 3.62/0.99      ( v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_780,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_785,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_784]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1632,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | m1_pre_topc(k1_tsep_1(sK0,X0,sK3),sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK3) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_785]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1914,plain,
% 3.62/0.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.62/0.99      | v2_struct_0(sK3)
% 3.62/0.99      | v2_struct_0(sK1) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_1632]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1915,plain,
% 3.62/0.99      ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_2,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f35]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_754,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | ~ v2_struct_0(k1_tsep_1(X1,X2,X0))
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_755,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_754]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_759,plain,
% 3.62/0.99      ( ~ v2_struct_0(k1_tsep_1(sK0,X0,X1))
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_755,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_760,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_759]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1499,plain,
% 3.62/0.99      ( m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top
% 3.62/0.99      | v2_struct_0(k1_tsep_1(sK0,X0,X1)) != iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_760]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4174,plain,
% 3.62/0.99      ( m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_4172,c_1499]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | ~ l1_pre_topc(X1)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
% 3.62/0.99      inference(cnf_transformation,[],[f37]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_704,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,X1)
% 3.62/0.99      | ~ m1_pre_topc(X2,X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | ~ v2_struct_0(k2_tsep_1(X1,X2,X0))
% 3.62/0.99      | sK0 != X1 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_705,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_704]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_709,plain,
% 3.62/0.99      ( ~ v2_struct_0(k2_tsep_1(sK0,X0,X1))
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_705,c_32]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_710,plain,
% 3.62/0.99      ( ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,X0,X1)) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_709]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4985,plain,
% 3.62/0.99      ( ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | ~ v2_struct_0(k2_tsep_1(sK0,sK2,sK4))
% 3.62/0.99      | v2_struct_0(sK2)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(instantiation,[status(thm)],[c_710]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_4986,plain,
% 3.62/0.99      ( m1_pre_topc(sK2,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(k2_tsep_1(sK0,sK2,sK4)) != iProver_top
% 3.62/0.99      | v2_struct_0(sK2) = iProver_top
% 3.62/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_4985]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5375,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),X0) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | m1_pre_topc(X0,k1_tsep_1(sK0,sK1,sK3)) != iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5298,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_1832,
% 3.62/0.99                 c_1915,c_4174,c_4986]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6395,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6390,c_5375]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6448,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK3) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6395,c_40,c_41]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_15,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X3,X2)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ v2_pre_topc(X2)
% 3.62/0.99      | ~ l1_pre_topc(X2)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X3) ),
% 3.62/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_548,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X0,X3),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ m1_pre_topc(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X3,X2)
% 3.62/0.99      | ~ l1_pre_topc(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | sK0 != X2 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_549,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ l1_pre_topc(sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_548]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_551,plain,
% 3.62/0.99      ( v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_549,c_32,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_552,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_551]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1503,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1) = iProver_top
% 3.62/0.99      | r1_tsep_1(k2_tsep_1(sK0,X0,X2),X1) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X2,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X2) = iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_552]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6458,plain,
% 3.62/0.99      ( r1_tsep_1(sK2,sK3) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK4) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top
% 3.62/0.99      | v2_struct_0(sK2) = iProver_top
% 3.62/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6448,c_1503]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6462,plain,
% 3.62/0.99      ( r1_tsep_1(sK2,sK3)
% 3.62/0.99      | r1_tsep_1(sK2,sK4)
% 3.62/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK3,sK4)
% 3.62/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | v2_struct_0(sK3)
% 3.62/0.99      | v2_struct_0(sK2)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6458]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6181,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK3,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK3) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_1510,c_5375]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6665,plain,
% 3.62/0.99      ( r1_tsep_1(k2_tsep_1(sK0,sK2,sK4),sK1) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK2,sK4) = iProver_top ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6181,c_36,c_37,c_40,c_41]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_14,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X3,X2)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ v2_pre_topc(X2)
% 3.62/0.99      | ~ l1_pre_topc(X2)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X3) ),
% 3.62/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_583,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(X2,X3,X0),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X1,X3)
% 3.62/0.99      | ~ m1_pre_topc(X0,X2)
% 3.62/0.99      | ~ m1_pre_topc(X3,X2)
% 3.62/0.99      | ~ l1_pre_topc(X2)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X3)
% 3.62/0.99      | sK0 != X2 ),
% 3.62/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_584,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ l1_pre_topc(sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(sK0) ),
% 3.62/0.99      inference(unflattening,[status(thm)],[c_583]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_586,plain,
% 3.62/0.99      ( v2_struct_0(X2)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_584,c_32,c_30]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_587,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1)
% 3.62/0.99      | ~ r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1)
% 3.62/0.99      | ~ m1_pre_topc(X1,X2)
% 3.62/0.99      | ~ m1_pre_topc(X2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(X1,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(X1)
% 3.62/0.99      | v2_struct_0(X2) ),
% 3.62/0.99      inference(renaming,[status(thm)],[c_586]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_1502,plain,
% 3.62/0.99      ( r1_tsep_1(X0,X1) = iProver_top
% 3.62/0.99      | r1_tsep_1(k2_tsep_1(sK0,X2,X0),X1) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,X2) != iProver_top
% 3.62/0.99      | m1_pre_topc(X0,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X1,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(X2,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(X2) = iProver_top
% 3.62/0.99      | v2_struct_0(X0) = iProver_top
% 3.62/0.99      | v2_struct_0(X1) = iProver_top ),
% 3.62/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6676,plain,
% 3.62/0.99      ( r1_tsep_1(sK2,sK4) = iProver_top
% 3.62/0.99      | r1_tsep_1(sK4,sK1) = iProver_top
% 3.62/0.99      | m1_pre_topc(sK2,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK0) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK1,sK2) != iProver_top
% 3.62/0.99      | m1_pre_topc(sK4,sK0) != iProver_top
% 3.62/0.99      | v2_struct_0(sK2) = iProver_top
% 3.62/0.99      | v2_struct_0(sK1) = iProver_top
% 3.62/0.99      | v2_struct_0(sK4) = iProver_top ),
% 3.62/0.99      inference(superposition,[status(thm)],[c_6665,c_1502]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6680,plain,
% 3.62/0.99      ( r1_tsep_1(sK2,sK4)
% 3.62/0.99      | r1_tsep_1(sK4,sK1)
% 3.62/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK1,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK1,sK2)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | v2_struct_0(sK2)
% 3.62/0.99      | v2_struct_0(sK1)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6676]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6776,plain,
% 3.62/0.99      ( r1_tsep_1(sK2,sK4) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_6709,c_29,c_28,c_27,c_26,c_25,c_24,c_23,c_22,c_21,
% 3.62/0.99                 c_20,c_18,c_6462,c_6680]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_6916,plain,
% 3.62/0.99      ( r1_tsep_1(sK4,sK1) | ~ m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_4580,c_6776]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7005,negated_conjecture,
% 3.62/0.99      ( ~ r1_tsep_1(sK2,sK3) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_18,c_23,c_22,c_6916]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5430,plain,
% 3.62/0.99      ( r1_tsep_1(X0,sK3)
% 3.62/0.99      | ~ r1_tsep_1(X0,sK4)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK3,sK0)
% 3.62/0.99      | ~ m1_pre_topc(sK4,sK0)
% 3.62/0.99      | v2_struct_0(X0)
% 3.62/0.99      | v2_struct_0(sK3)
% 3.62/0.99      | v2_struct_0(sK4) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_443,c_20]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_5453,plain,
% 3.62/0.99      ( r1_tsep_1(X0,sK3)
% 3.62/0.99      | ~ r1_tsep_1(X0,sK4)
% 3.62/0.99      | ~ m1_pre_topc(X0,sK0)
% 3.62/0.99      | v2_struct_0(X0) ),
% 3.62/0.99      inference(global_propositional_subsumption,
% 3.62/0.99                [status(thm)],
% 3.62/0.99                [c_5430,c_25,c_24,c_23,c_22]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(c_7017,plain,
% 3.62/0.99      ( ~ r1_tsep_1(sK2,sK4)
% 3.62/0.99      | ~ m1_pre_topc(sK2,sK0)
% 3.62/0.99      | v2_struct_0(sK2) ),
% 3.62/0.99      inference(resolution,[status(thm)],[c_7005,c_5453]) ).
% 3.62/0.99  
% 3.62/0.99  cnf(contradiction,plain,
% 3.62/0.99      ( $false ),
% 3.62/0.99      inference(minisat,[status(thm)],[c_7017,c_6776,c_26,c_27]) ).
% 3.62/0.99  
% 3.62/0.99  
% 3.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.62/0.99  
% 3.62/0.99  ------                               Statistics
% 3.62/0.99  
% 3.62/0.99  ------ Selected
% 3.62/0.99  
% 3.62/0.99  total_time:                             0.324
% 3.62/0.99  
%------------------------------------------------------------------------------
