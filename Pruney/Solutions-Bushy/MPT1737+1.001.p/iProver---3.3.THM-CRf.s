%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1737+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:46:18 EST 2020

% Result     : Theorem 35.12s
% Output     : CNFRefutation 35.12s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 856 expanded)
%              Number of clauses        :  127 ( 216 expanded)
%              Number of leaves         :   19 ( 298 expanded)
%              Depth                    :   17
%              Number of atoms          : 1219 (11277 expanded)
%              Number of equality atoms :  218 ( 256 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal clause size      :   32 (   5 average)
%              Maximal term depth       :    4 (   1 average)

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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
            | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
            | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
            | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
          & r1_tsep_1(X3,X2)
          & m1_pre_topc(X1,X3)
          & m1_pre_topc(X3,X0)
          & v1_tsep_1(X3,X0)
          & ~ v2_struct_0(X3) )
     => ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
          | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
          | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
          | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
        & r1_tsep_1(sK3,X2)
        & m1_pre_topc(X1,sK3)
        & m1_pre_topc(sK3,X0)
        & v1_tsep_1(sK3,X0)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
              & r1_tsep_1(X3,X2)
              & m1_pre_topc(X1,X3)
              & m1_pre_topc(X3,X0)
              & v1_tsep_1(X3,X0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,X0)
          & ~ v2_struct_0(X2) )
     => ( ? [X3] :
            ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,sK2,X1))
              | ~ v1_tsep_1(X1,k1_tsep_1(X0,sK2,X1))
              | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,sK2))
              | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,sK2)) )
            & r1_tsep_1(X3,sK2)
            & m1_pre_topc(X1,X3)
            & m1_pre_topc(X3,X0)
            & v1_tsep_1(X3,X0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(sK2,X0)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_pre_topc(sK1,k1_tsep_1(X0,X2,sK1))
                  | ~ v1_tsep_1(sK1,k1_tsep_1(X0,X2,sK1))
                  | ~ m1_pre_topc(sK1,k1_tsep_1(X0,sK1,X2))
                  | ~ v1_tsep_1(sK1,k1_tsep_1(X0,sK1,X2)) )
                & r1_tsep_1(X3,X2)
                & m1_pre_topc(sK1,X3)
                & m1_pre_topc(X3,X0)
                & v1_tsep_1(X3,X0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,X0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                    & r1_tsep_1(X3,X2)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & v1_tsep_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
    & r1_tsep_1(sK3,sK2)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & v1_tsep_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f43,f42,f41,f40])).

fof(f72,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    r1_tsep_1(sK3,sK2) ),
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
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
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
    inference(cnf_transformation,[],[f33])).

fof(f73,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f75,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f68,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f77,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    m1_pre_topc(sK1,sK3) ),
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
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f3,axiom,(
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

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

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
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f56,plain,(
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
    inference(cnf_transformation,[],[f27])).

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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f80,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) ) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_635,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | r1_tsep_1(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_18651,plain,
    ( r1_tsep_1(X0_43,X1_43)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | X1_43 != k1_tsep_1(sK0,sK1,sK2)
    | X0_43 != sK3 ),
    inference(instantiation,[status(thm)],[c_635])).

cnf(c_44305,plain,
    ( r1_tsep_1(sK3,X0_43)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | X0_43 != k1_tsep_1(sK0,sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_18651])).

cnf(c_120791,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK1))
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_44305])).

cnf(c_31,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_593,negated_conjecture,
    ( m1_pre_topc(sK1,sK0) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1290,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_593])).

cnf(c_24,negated_conjecture,
    ( r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_600,negated_conjecture,
    ( r1_tsep_1(sK3,sK2) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1283,plain,
    ( r1_tsep_1(sK3,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_20,plain,
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
    | k2_tsep_1(X3,X0,k1_tsep_1(X3,X2,X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_604,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X3_43)
    | ~ m1_pre_topc(X0_43,X3_43)
    | ~ m1_pre_topc(X2_43,X0_43)
    | ~ m1_pre_topc(X1_43,X3_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43)
    | ~ l1_pre_topc(X3_43)
    | ~ v2_pre_topc(X3_43)
    | k2_tsep_1(X3_43,X0_43,k1_tsep_1(X3_43,X2_43,X1_43)) = g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43)) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1279,plain,
    ( k2_tsep_1(X0_43,X1_43,k1_tsep_1(X0_43,X2_43,X3_43)) = g1_pre_topc(u1_struct_0(X2_43),u1_pre_topc(X2_43))
    | r1_tsep_1(X1_43,X3_43) != iProver_top
    | m1_pre_topc(X2_43,X1_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X3_43,X0_43) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X3_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_604])).

cnf(c_8398,plain,
    ( k2_tsep_1(X0_43,sK3,k1_tsep_1(X0_43,X1_43,sK2)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_43) != iProver_top
    | m1_pre_topc(sK2,X0_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(superposition,[status(thm)],[c_1283,c_1279])).

cnf(c_30,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_41,plain,
    ( v2_struct_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_43,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16232,plain,
    ( k2_tsep_1(X0_43,sK3,k1_tsep_1(X0_43,X1_43,sK2)) = g1_pre_topc(u1_struct_0(X1_43),u1_pre_topc(X1_43))
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X1_43,sK3) != iProver_top
    | m1_pre_topc(sK3,X0_43) != iProver_top
    | m1_pre_topc(sK2,X0_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8398,c_41,c_43])).

cnf(c_16250,plain,
    ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
    | m1_pre_topc(sK3,sK0) != iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK3) != iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_16232])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_34,negated_conjecture,
    ( v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,negated_conjecture,
    ( l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_32,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_29,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_26,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_25,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2034,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK3)
    | ~ m1_pre_topc(sK3,X1_43)
    | ~ m1_pre_topc(sK2,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | k2_tsep_1(X1_43,sK3,k1_tsep_1(X1_43,X0_43,sK2)) = g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)) ),
    inference(instantiation,[status(thm)],[c_604])).

cnf(c_2465,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,X0_43)
    | ~ m1_pre_topc(sK2,X0_43)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43)
    | k2_tsep_1(X0_43,sK3,k1_tsep_1(X0_43,sK1,sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_2034])).

cnf(c_2467,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(instantiation,[status(thm)],[c_2465])).

cnf(c_16441,plain,
    ( k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16250,c_35,c_34,c_33,c_32,c_31,c_30,c_29,c_28,c_26,c_25,c_24,c_2467])).

cnf(c_22,plain,
    ( r1_tsep_1(X0,X1)
    | ~ v1_tsep_1(X0,X2)
    | v1_tsep_1(k2_tsep_1(X2,X0,X1),X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_602,plain,
    ( r1_tsep_1(X0_43,X1_43)
    | ~ v1_tsep_1(X0_43,X2_43)
    | v1_tsep_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1281,plain,
    ( r1_tsep_1(X0_43,X1_43) = iProver_top
    | v1_tsep_1(X0_43,X2_43) != iProver_top
    | v1_tsep_1(k2_tsep_1(X2_43,X0_43,X1_43),X1_43) = iProver_top
    | m1_pre_topc(X1_43,X2_43) != iProver_top
    | m1_pre_topc(X0_43,X2_43) != iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | l1_pre_topc(X2_43) != iProver_top
    | v2_pre_topc(X2_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_16444,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_tsep_1(sK3,sK0) != iProver_top
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) != iProver_top
    | m1_pre_topc(sK3,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v2_struct_0(sK3) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_16441,c_1281])).

cnf(c_36,plain,
    ( v2_struct_0(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_37,plain,
    ( v2_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_38,plain,
    ( l1_pre_topc(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_39,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_pre_topc(sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_42,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_27,negated_conjecture,
    ( v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_44,plain,
    ( v1_tsep_1(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_45,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(k1_tsep_1(X1,X0,X2),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_620,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(k1_tsep_1(X1_43,X0_43,X2_43),X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1898,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2248,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1898])).

cnf(c_2249,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) = iProver_top
    | m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2248])).

cnf(c_3,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ v2_struct_0(k1_tsep_1(X1,X0,X2))
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_619,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ v2_struct_0(k1_tsep_1(X1_43,X0_43,X2_43))
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_5936,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_5937,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5936])).

cnf(c_70145,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16444,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_43,c_44,c_45,c_2249,c_5937])).

cnf(c_7,plain,
    ( v1_tsep_1(X0,X1)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
    | ~ v2_pre_topc(X1)
    | ~ v2_pre_topc(X0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_615,plain,
    ( v1_tsep_1(X0_43,X1_43)
    | ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ l1_pre_topc(X0_43)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)))
    | ~ v2_pre_topc(X1_43)
    | ~ v2_pre_topc(X0_43)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1268,plain,
    ( v1_tsep_1(X0_43,X1_43) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_0,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | v2_pre_topc(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_622,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43)
    | v2_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1261,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_4,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ l1_pre_topc(X1)
    | l1_pre_topc(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_618,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ l1_pre_topc(X1_43)
    | l1_pre_topc(X0_43) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1265,plain,
    ( m1_pre_topc(X0_43,X1_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | l1_pre_topc(X0_43) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_1522,plain,
    ( v1_tsep_1(X0_43,X1_43) = iProver_top
    | v1_tsep_1(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43) != iProver_top
    | l1_pre_topc(X0_43) != iProver_top
    | l1_pre_topc(X1_43) != iProver_top
    | v2_pre_topc(X0_43) != iProver_top
    | v2_pre_topc(X1_43) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1268,c_1261,c_1265])).

cnf(c_70151,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | l1_pre_topc(sK1) != iProver_top
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v2_pre_topc(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_70145,c_1522])).

cnf(c_70181,plain,
    ( r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_70151])).

cnf(c_10,plain,
    ( ~ r1_tsep_1(X0,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X0,X2)
    | ~ m1_pre_topc(X1,X0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_614,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | ~ m1_pre_topc(X1_43,X2_43)
    | ~ m1_pre_topc(X0_43,X2_43)
    | ~ m1_pre_topc(X1_43,X0_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X2_43)
    | ~ v2_pre_topc(X2_43) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_65403,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),X0_43)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_65415,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK1)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_65403])).

cnf(c_15,plain,
    ( ~ r1_tsep_1(X0,X1)
    | r1_tsep_1(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X0,X3)
    | ~ m1_pre_topc(X2,X0)
    | ~ m1_pre_topc(X1,X3)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X0)
    | v2_struct_0(X1)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X3) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_609,plain,
    ( ~ r1_tsep_1(X0_43,X1_43)
    | r1_tsep_1(X1_43,X2_43)
    | ~ m1_pre_topc(X2_43,X3_43)
    | ~ m1_pre_topc(X0_43,X3_43)
    | ~ m1_pre_topc(X2_43,X0_43)
    | ~ m1_pre_topc(X1_43,X3_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(X3_43)
    | ~ l1_pre_topc(X3_43)
    | ~ v2_pre_topc(X3_43) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_19687,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),X0_43)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X0_43,sK3)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),X1_43)
    | ~ m1_pre_topc(sK3,X1_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(instantiation,[status(thm)],[c_609])).

cnf(c_60459,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK1)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),X0_43)
    | ~ m1_pre_topc(sK3,X0_43)
    | ~ m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,sK3)
    | v2_struct_0(X0_43)
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK3)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43) ),
    inference(instantiation,[status(thm)],[c_19687])).

cnf(c_60461,plain,
    ( r1_tsep_1(k1_tsep_1(sK0,sK2,sK1),sK1)
    | ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_60459])).

cnf(c_629,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(X2_43,X3_43)
    | X2_43 != X0_43
    | X3_43 != X1_43 ),
    theory(equality)).

cnf(c_3356,plain,
    ( m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | X1_43 != k1_tsep_1(sK0,sK1,sK2)
    | X0_43 != sK1 ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_8895,plain,
    ( m1_pre_topc(sK1,X0_43)
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | X0_43 != k1_tsep_1(sK0,sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3356])).

cnf(c_33758,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_8895])).

cnf(c_22555,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0_43)
    | ~ l1_pre_topc(X0_43)
    | ~ v2_pre_topc(X0_43)
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_22557,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_22555])).

cnf(c_1,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | k1_tsep_1(X1,X2,X0) = k1_tsep_1(X1,X0,X2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_621,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | k1_tsep_1(X1_43,X2_43,X0_43) = k1_tsep_1(X1_43,X0_43,X2_43) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_8607,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_7012,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0_43)
    | ~ l1_pre_topc(X0_43)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_7014,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_7012])).

cnf(c_6220,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_struct_0(k1_tsep_1(sK0,sK2,sK1))
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_595,negated_conjecture,
    ( m1_pre_topc(sK2,sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1288,plain,
    ( m1_pre_topc(sK2,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_595])).

cnf(c_1262,plain,
    ( k1_tsep_1(X0_43,X1_43,X2_43) = k1_tsep_1(X0_43,X2_43,X1_43)
    | m1_pre_topc(X1_43,X0_43) != iProver_top
    | m1_pre_topc(X2_43,X0_43) != iProver_top
    | v2_struct_0(X1_43) = iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(X2_43) = iProver_top
    | l1_pre_topc(X0_43) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_3541,plain,
    ( k1_tsep_1(sK0,sK2,X0_43) = k1_tsep_1(sK0,X0_43,sK2)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | l1_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1262])).

cnf(c_4678,plain,
    ( v2_struct_0(X0_43) = iProver_top
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | k1_tsep_1(sK0,sK2,X0_43) = k1_tsep_1(sK0,X0_43,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3541,c_36,c_38,c_41])).

cnf(c_4679,plain,
    ( k1_tsep_1(sK0,sK2,X0_43) = k1_tsep_1(sK0,X0_43,sK2)
    | m1_pre_topc(X0_43,sK0) != iProver_top
    | v2_struct_0(X0_43) = iProver_top ),
    inference(renaming,[status(thm)],[c_4678])).

cnf(c_4689,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1)
    | v2_struct_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_4679])).

cnf(c_4728,plain,
    ( k1_tsep_1(sK0,sK1,sK2) = k1_tsep_1(sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4689,c_39])).

cnf(c_23,negated_conjecture,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_601,negated_conjecture,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1282,plain,
    ( v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_48,plain,
    ( v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_pre_topc(X0,X1)
    | ~ m1_pre_topc(X2,X1)
    | m1_pre_topc(X0,k1_tsep_1(X1,X0,X2))
    | v2_struct_0(X1)
    | v2_struct_0(X0)
    | v2_struct_0(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_612,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | ~ m1_pre_topc(X2_43,X1_43)
    | m1_pre_topc(X0_43,k1_tsep_1(X1_43,X0_43,X2_43))
    | v2_struct_0(X2_43)
    | v2_struct_0(X1_43)
    | v2_struct_0(X0_43)
    | ~ l1_pre_topc(X1_43)
    | ~ v2_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1921,plain,
    ( m1_pre_topc(X0_43,k1_tsep_1(sK0,X0_43,sK2))
    | ~ m1_pre_topc(X0_43,sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_2351,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_2352,plain,
    ( m1_pre_topc(sK2,sK0) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) = iProver_top
    | m1_pre_topc(sK1,sK0) != iProver_top
    | v2_struct_0(sK2) = iProver_top
    | v2_struct_0(sK0) = iProver_top
    | v2_struct_0(sK1) = iProver_top
    | l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2351])).

cnf(c_2384,plain,
    ( m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1282,c_36,c_37,c_38,c_39,c_40,c_41,c_42,c_48,c_2352])).

cnf(c_2385,plain,
    ( v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2384])).

cnf(c_4731,plain,
    ( v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4728,c_2385])).

cnf(c_4732,plain,
    ( ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4731])).

cnf(c_5,plain,
    ( ~ m1_pre_topc(X0,X1)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_617,plain,
    ( ~ m1_pre_topc(X0_43,X1_43)
    | m1_pre_topc(g1_pre_topc(u1_struct_0(X0_43),u1_pre_topc(X0_43)),X1_43)
    | ~ l1_pre_topc(X1_43) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_3357,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1903,plain,
    ( ~ m1_pre_topc(X0_43,sK0)
    | m1_pre_topc(k1_tsep_1(sK0,X0_43,sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(X0_43)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_2263,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK2,sK1),sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(instantiation,[status(thm)],[c_1903])).

cnf(c_624,plain,
    ( X0_43 = X0_43 ),
    theory(equality)).

cnf(c_2203,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_2197,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_598,negated_conjecture,
    ( m1_pre_topc(sK3,sK0) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1285,plain,
    ( m1_pre_topc(sK3,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_2082,plain,
    ( l1_pre_topc(sK0) != iProver_top
    | v2_pre_topc(sK3) = iProver_top
    | v2_pre_topc(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1285,c_1261])).

cnf(c_2103,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2082])).

cnf(c_599,negated_conjecture,
    ( m1_pre_topc(sK1,sK3) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1284,plain,
    ( m1_pre_topc(sK1,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_599])).

cnf(c_2081,plain,
    ( l1_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK3) != iProver_top
    | v2_pre_topc(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1284,c_1261])).

cnf(c_2102,plain,
    ( ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | v2_pre_topc(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2081])).

cnf(c_2019,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[status(thm)],[c_618,c_598])).

cnf(c_2017,plain,
    ( ~ l1_pre_topc(sK3)
    | l1_pre_topc(sK1) ),
    inference(resolution,[status(thm)],[c_618,c_599])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_120791,c_70181,c_65415,c_60461,c_33758,c_22557,c_8607,c_7014,c_6220,c_4732,c_3357,c_2351,c_2263,c_2248,c_2203,c_2197,c_2103,c_2102,c_2019,c_2017,c_25,c_26,c_28,c_29,c_30,c_31,c_32,c_33,c_34,c_35])).


%------------------------------------------------------------------------------
