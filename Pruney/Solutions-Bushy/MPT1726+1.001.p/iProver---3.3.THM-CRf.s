%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1726+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:17 EST 2020

% Result     : Theorem 3.28s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :  208 (4150 expanded)
%              Number of clauses        :  142 ( 867 expanded)
%              Number of leaves         :   15 (1704 expanded)
%              Depth                    :   25
%              Number of atoms          : 1277 (62204 expanded)
%              Number of equality atoms :  273 (1114 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   34 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f43,plain,(
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
     => ( ( ~ r1_tsep_1(sK6,X1)
          | ~ r1_tsep_1(X2,X3) )
        & ( r1_tsep_1(k2_tsep_1(X0,X2,sK6),k1_tsep_1(X0,X1,X3))
          | r1_tsep_1(X2,sK6) )
        & m1_pre_topc(X3,sK6)
        & m1_pre_topc(X1,X2)
        & m1_pre_topc(sK6,X0)
        & ~ v2_struct_0(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
              | ~ r1_tsep_1(X2,sK5) )
            & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,X1,sK5))
              | r1_tsep_1(X2,X4) )
            & m1_pre_topc(sK5,X4)
            & m1_pre_topc(X1,X2)
            & m1_pre_topc(X4,X0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(sK5,X0)
        & ~ v2_struct_0(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
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
                  | ~ r1_tsep_1(sK4,X3) )
                & ( r1_tsep_1(k2_tsep_1(X0,sK4,X4),k1_tsep_1(X0,X1,X3))
                  | r1_tsep_1(sK4,X4) )
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(X1,sK4)
                & m1_pre_topc(X4,X0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK4,X0)
        & ~ v2_struct_0(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
                    ( ( ~ r1_tsep_1(X4,sK3)
                      | ~ r1_tsep_1(X2,X3) )
                    & ( r1_tsep_1(k2_tsep_1(X0,X2,X4),k1_tsep_1(X0,sK3,X3))
                      | r1_tsep_1(X2,X4) )
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(sK3,X2)
                    & m1_pre_topc(X4,X0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
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
                      & ( r1_tsep_1(k2_tsep_1(sK2,X2,X4),k1_tsep_1(sK2,X1,X3))
                        | r1_tsep_1(X2,X4) )
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK2)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ r1_tsep_1(sK6,sK3)
      | ~ r1_tsep_1(sK4,sK5) )
    & ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),k1_tsep_1(sK2,sK3,sK5))
      | r1_tsep_1(sK4,sK6) )
    & m1_pre_topc(sK5,sK6)
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK6,sK2)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f34,f43,f42,f41,f40,f39])).

fof(f72,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f66,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f67,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
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

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),k1_tsep_1(sK2,sK3,sK5))
    | r1_tsep_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f44])).

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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f73,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
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

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

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

fof(f15,plain,(
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

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,X2)
      | r1_tsep_1(X1,X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_pre_topc(sK5,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,
    ( ~ r1_tsep_1(sK6,sK3)
    | ~ r1_tsep_1(sK4,sK5) ),
    inference(cnf_transformation,[],[f44])).

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
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( m1_pre_topc(X2,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X3,X1),X2)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X1,X3),X2) ) )
                      & ( m1_pre_topc(X1,X3)
                       => ( ~ r1_tsep_1(k2_tsep_1(X0,X2,X3),X1)
                          & ~ r1_tsep_1(k2_tsep_1(X0,X3,X2),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f62,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f63,plain,(
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
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X2,X3)
      | r1_tsep_1(X1,X3)
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
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f51,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1501,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1497,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | k1_tsep_1(X1,X0,X2) = k1_tsep_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1517,plain,
    ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X1,X0) != iProver_top
    | l1_pre_topc(X0) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5173,plain,
    ( k1_tsep_1(sK2,X0,sK5) = k1_tsep_1(sK2,sK5,X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_1517])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_34,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_31,negated_conjecture,
    ( l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_36,plain,
    ( l1_pre_topc(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_41,plain,
    ( v2_struct_0(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6104,plain,
    ( m1_pre_topc(X0,sK2) != iProver_top
    | k1_tsep_1(sK2,X0,sK5) = k1_tsep_1(sK2,sK5,X0)
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5173,c_34,c_36,c_41])).

cnf(c_6105,plain,
    ( k1_tsep_1(sK2,X0,sK5) = k1_tsep_1(sK2,sK5,X0)
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6104])).

cnf(c_6117,plain,
    ( k1_tsep_1(sK2,sK5,sK3) = k1_tsep_1(sK2,sK3,sK5)
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_6105])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_37,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6368,plain,
    ( k1_tsep_1(sK2,sK5,sK3) = k1_tsep_1(sK2,sK3,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6117,c_37])).

cnf(c_10,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_32,negated_conjecture,
    ( v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_338,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X0))
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_32])).

cnf(c_339,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK2,X0,X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_343,plain,
    ( v2_struct_0(X0)
    | v2_struct_0(X1)
    | m1_pre_topc(X0,k1_tsep_1(sK2,X0,X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_339,c_33,c_31])).

cnf(c_344,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK2,X0,X1))
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_343])).

cnf(c_1493,plain,
    ( m1_pre_topc(X0,k1_tsep_1(sK2,X0,X1)) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_344])).

cnf(c_6373,plain,
    ( m1_pre_topc(sK5,k1_tsep_1(sK2,sK3,sK5)) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6368,c_1493])).

cnf(c_38,plain,
    ( m1_pre_topc(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_42,plain,
    ( m1_pre_topc(sK5,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7129,plain,
    ( m1_pre_topc(sK5,k1_tsep_1(sK2,sK3,sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6373,c_37,c_38,c_41,c_42])).

cnf(c_20,negated_conjecture,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),k1_tsep_1(sK2,sK3,sK5))
    | r1_tsep_1(sK4,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1506,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),k1_tsep_1(sK2,sK3,sK5)) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_11,plain,
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
    inference(cnf_transformation,[],[f59])).

cnf(c_470,plain,
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
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_471,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_473,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_471,c_33,c_31])).

cnf(c_474,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X0,X2)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_473])).

cnf(c_1489,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X0,X2) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X2,sK2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_474])).

cnf(c_2712,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),X0) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK4,sK6),sK2) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1489])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_39,plain,
    ( v2_struct_0(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_40,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_43,plain,
    ( v2_struct_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( m1_pre_topc(sK6,sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_44,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3007,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k1_tsep_1(sK2,X0,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4197,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3007])).

cnf(c_4198,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4197])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3731,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k1_tsep_1(sK2,X0,sK5))
    | v2_struct_0(sK2)
    | v2_struct_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4295,plain,
    ( ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ l1_pre_topc(sK2)
    | ~ v2_struct_0(k1_tsep_1(sK2,sK3,sK5))
    | v2_struct_0(sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK3) ),
    inference(instantiation,[status(thm)],[c_3731])).

cnf(c_4296,plain,
    ( m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4295])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k2_tsep_1(X1,X2,X0),X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_3842,plain,
    ( ~ m1_pre_topc(X0,sK2)
    | m1_pre_topc(k2_tsep_1(sK2,X0,sK6),sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4353,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK4,sK6),sK2)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3842])).

cnf(c_4354,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK4,sK6),sK2) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4353])).

cnf(c_4729,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2712,c_34,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_4198,c_4296,c_4354])).

cnf(c_4730,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),X0) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4729])).

cnf(c_7138,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK5) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7129,c_4730])).

cnf(c_12,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
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
    inference(cnf_transformation,[],[f58])).

cnf(c_435,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_32])).

cnf(c_436,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_438,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_436,c_33,c_31])).

cnf(c_439,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X0)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_438])).

cnf(c_1490,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X2,X0) = iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X2,sK2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_439])).

cnf(c_2726,plain,
    ( r1_tsep_1(X0,k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(k2_tsep_1(sK2,sK4,sK6),sK2) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1506,c_1490])).

cnf(c_4824,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | r1_tsep_1(X0,k2_tsep_1(sK2,sK4,sK6)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2726,c_34,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_4198,c_4296,c_4354])).

cnf(c_4825,plain,
    ( r1_tsep_1(X0,k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(X0,k1_tsep_1(sK2,sK3,sK5)) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_4824])).

cnf(c_7137,plain,
    ( r1_tsep_1(sK5,k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_7129,c_4825])).

cnf(c_22,negated_conjecture,
    ( m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_21,negated_conjecture,
    ( m1_pre_topc(sK5,sK6) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_46,plain,
    ( m1_pre_topc(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_19,negated_conjecture,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ r1_tsep_1(sK6,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_48,plain,
    ( r1_tsep_1(sK4,sK5) != iProver_top
    | r1_tsep_1(sK6,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_16,plain,
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
    inference(cnf_transformation,[],[f62])).

cnf(c_579,plain,
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
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_580,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_579])).

cnf(c_582,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_580,c_33,c_31])).

cnf(c_583,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X0,X2),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_582])).

cnf(c_2000,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X0,sK6),X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X1,sK6)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_3242,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),X0)
    | r1_tsep_1(sK4,X0)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_4699,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK5)
    | r1_tsep_1(sK4,sK5)
    | ~ m1_pre_topc(sK5,sK2)
    | ~ m1_pre_topc(sK5,sK6)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK5)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3242])).

cnf(c_4700,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK5) != iProver_top
    | r1_tsep_1(sK4,sK5) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK5,sK6) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4699])).

cnf(c_4744,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK3) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(sK5,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | v2_struct_0(sK5) = iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_4730])).

cnf(c_15,plain,
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
    inference(cnf_transformation,[],[f63])).

cnf(c_614,plain,
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
    | sK2 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_615,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_614])).

cnf(c_617,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_615,c_33,c_31])).

cnf(c_618,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,X2,X0),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_617])).

cnf(c_2018,plain,
    ( r1_tsep_1(X0,X1)
    | ~ r1_tsep_1(k2_tsep_1(sK2,sK4,X0),X1)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ m1_pre_topc(X1,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(sK4) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_3356,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),X0)
    | r1_tsep_1(sK6,X0)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X0,sK4)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(sK4)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2018])).

cnf(c_5496,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK3)
    | r1_tsep_1(sK6,sK3)
    | ~ m1_pre_topc(sK4,sK2)
    | ~ m1_pre_topc(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK4)
    | ~ m1_pre_topc(sK6,sK2)
    | v2_struct_0(sK4)
    | v2_struct_0(sK3)
    | v2_struct_0(sK6) ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_5497,plain,
    ( r1_tsep_1(k2_tsep_1(sK2,sK4,sK6),sK3) != iProver_top
    | r1_tsep_1(sK6,sK3) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK3,sK2) != iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5496])).

cnf(c_7223,plain,
    ( v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top
    | r1_tsep_1(sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7137,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_46,c_48,c_4700,c_4744,c_5497,c_7138])).

cnf(c_7224,plain,
    ( r1_tsep_1(sK4,sK6) = iProver_top
    | v2_struct_0(k2_tsep_1(sK2,sK4,sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7223])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | ~ v2_struct_0(k2_tsep_1(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1513,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | m1_pre_topc(X2,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X1) = iProver_top
    | v2_struct_0(k2_tsep_1(X1,X0,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_7229,plain,
    ( r1_tsep_1(sK4,sK6) = iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | l1_pre_topc(sK2) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7224,c_1513])).

cnf(c_7232,plain,
    ( r1_tsep_1(sK4,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7138,c_34,c_36,c_39,c_40,c_43,c_44,c_7229])).

cnf(c_7240,plain,
    ( r1_tsep_1(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_1490])).

cnf(c_7852,plain,
    ( r1_tsep_1(X0,sK4) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK6) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7240,c_39,c_40,c_43,c_44])).

cnf(c_7864,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top
    | m1_pre_topc(sK5,sK6) != iProver_top
    | v2_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1501,c_7852])).

cnf(c_7942,plain,
    ( r1_tsep_1(sK5,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7864,c_41,c_46])).

cnf(c_9,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X0)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1508,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X1,X0) = iProver_top
    | l1_struct_0(X1) != iProver_top
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_7947,plain,
    ( r1_tsep_1(sK4,sK5) = iProver_top
    | l1_struct_0(sK5) != iProver_top
    | l1_struct_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_7942,c_1508])).

cnf(c_14,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
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
    inference(cnf_transformation,[],[f56])).

cnf(c_365,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ l1_pre_topc(X3)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | sK2 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_366,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_368,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_33,c_31])).

cnf(c_369,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X2,X1)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X2,sK2)
    | ~ m1_pre_topc(X0,sK2)
    | ~ m1_pre_topc(X1,sK2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | v2_struct_0(X2) ),
    inference(renaming,[status(thm)],[c_368])).

cnf(c_1492,plain,
    ( r1_tsep_1(X0,X1) != iProver_top
    | r1_tsep_1(X2,X1) = iProver_top
    | m1_pre_topc(X2,X0) != iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X1,sK2) != iProver_top
    | m1_pre_topc(X2,sK2) != iProver_top
    | v2_struct_0(X2) = iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_7238,plain,
    ( r1_tsep_1(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | m1_pre_topc(sK4,sK2) != iProver_top
    | m1_pre_topc(sK6,sK2) != iProver_top
    | v2_struct_0(X0) = iProver_top
    | v2_struct_0(sK4) = iProver_top
    | v2_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_7232,c_1492])).

cnf(c_7380,plain,
    ( r1_tsep_1(X0,sK6) = iProver_top
    | m1_pre_topc(X0,sK2) != iProver_top
    | m1_pre_topc(X0,sK4) != iProver_top
    | v2_struct_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7238,c_39,c_40,c_43,c_44])).

cnf(c_7394,plain,
    ( r1_tsep_1(sK3,sK6) = iProver_top
    | m1_pre_topc(sK3,sK4) != iProver_top
    | v2_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1497,c_7380])).

cnf(c_7502,plain,
    ( r1_tsep_1(sK3,sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7394,c_37,c_45])).

cnf(c_7507,plain,
    ( r1_tsep_1(sK6,sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | l1_struct_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7502,c_1508])).

cnf(c_1499,plain,
    ( m1_pre_topc(sK4,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1511,plain,
    ( m1_pre_topc(X0,X1) != iProver_top
    | l1_pre_topc(X1) != iProver_top
    | l1_pre_topc(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2908,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1499,c_1511])).

cnf(c_3589,plain,
    ( l1_pre_topc(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2908,c_36])).

cnf(c_5,plain,
    ( l1_struct_0(X0)
    | ~ l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1512,plain,
    ( l1_struct_0(X0) = iProver_top
    | l1_pre_topc(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3594,plain,
    ( l1_struct_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3589,c_1512])).

cnf(c_1503,plain,
    ( m1_pre_topc(sK6,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2906,plain,
    ( l1_pre_topc(sK2) != iProver_top
    | l1_pre_topc(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1503,c_1511])).

cnf(c_3201,plain,
    ( l1_pre_topc(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2906,c_36])).

cnf(c_3206,plain,
    ( l1_struct_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_3201,c_1512])).

cnf(c_1504,plain,
    ( m1_pre_topc(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2905,plain,
    ( l1_pre_topc(sK4) != iProver_top
    | l1_pre_topc(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1504,c_1511])).

cnf(c_3193,plain,
    ( l1_pre_topc(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2905,c_36,c_2908])).

cnf(c_3198,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3193,c_1512])).

cnf(c_1505,plain,
    ( m1_pre_topc(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2904,plain,
    ( l1_pre_topc(sK5) = iProver_top
    | l1_pre_topc(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1505,c_1511])).

cnf(c_3105,plain,
    ( l1_pre_topc(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2904,c_36,c_2906])).

cnf(c_3110,plain,
    ( l1_struct_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3105,c_1512])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7947,c_7507,c_3594,c_3206,c_3198,c_3110,c_48])).


%------------------------------------------------------------------------------
